#!/usr/bin/perl -w
# This code is licensed under GPL 2.0

use strict;
use warnings;
use List::Util qw(sum);
use Fcntl;
use Getopt::Std;
use Proc::Background;
use globals;

my $usage=<<END;

raspawn.pl -0 'command' -1 'directory' -2 'regex' [-3 number]
  [-4 number] [-5 number] [-6 number] [-7 number] [-8 number] [-9 number]

Resource Aware spawn.
Spawns a number of processes while trying to keep resources
utilization just below the maximum. Waits until there are enough system
resources before spawning a new process. Spawns processes over a number 
of files/directories in a given directory untill all are processed.

Usage:
  -0 - command to execute. E.g. 'perl blah.pl -s -i '
  -1 - directory where files (or directories) habituate.
       e.g. ../directory/
  -2 - regular expression used to pick files to process
       e.g. '.*xml' (for all .xml files in the directory)
       (it matches directories also: .* will match . and ..)
  -3 - maximum memory utilization. When memory is utilized over
       this number, spawning is halted until it drops below.
       70% if left out. If 100% of memory gets used, linux starts
       swapping processes out to disk which kills performance.
       70% should be safe enough to avoid this in most cases.
       If system freezes for prolonged periods of time and you
       notice swap value increasing, drop this further or decrease
       linux swappiness.
  -4 - maximum disk i/o utilization in % that should not be exeeded.
       90% if left out. This is the maximum value of all disks -
       if any disk gets over 90%, spawning is halted until it
       drops below.
       (Regular hard disk can do around 150 operations per second, 
       while SSD can do over 10,000)
       (This has nothing to do with disk size utilization)
  -5 - maximum total processor utilization (all cores) in %.
       95% if left out.
  -6 - sleep this many seconds before starting new process.
       5 if left out. 
       If many processes are being spawned without
       any of cpu/memory/disk resources being exhausted, perhaps
       this number needs to be increased (e.g if your processes 
       need >5s to warm up and don't have the time to start running
       full steam).  
       If none of the system resources are being
       exhausted and only a small number of processes are running
       at a time, this number needs to be decreased (e.g. if your
       processes are finishing in <5s, raspawn.pl can not spawn them
       fast enough).
       If your spawned processes end up sleeping
       (status in System Monitor shows sleeping or Waiting Channel
       shows sleep_on_page_killable or waiting on interrupt...)
       instead of working, it is possible that they are being
       spawned too fast. Increase this value to try to fix that.
  -7 - maximum number of processes to spawn at a time.
       128 if left out.
  -8 - limit total number of processes spawned. Stops when
       this many spawned. If left out, processes all files in
       the directory given.
  -9 - print status line every this many sleep periods (-s)
       3 if left out.

(using numerical opions -0 to -9 in order to avoid possible overlap 
with options of the command executed.)

Examples: 

     perl raspawn.pl -0 'ls -la' -1 '../directory/' -2 '.*xml' -8 3

  This executes "ls -la" command on three xml files in ../directory/.
  This results in three commands:
  ls -la ../directory/blah1.xml
  ls -la ../directory/blah2.xml
  ls -la ../directory/blah3.xml

    perl raspawn.pl -0 'perl blah.pl -i ' -1 '../directory/' -2 'A.*txt'

  Executes 'perl blah.pl -s -i' command on all txt files starting
  with A in ../directory/ like so:
  perl blah.pl -s -i ../directory/file1.txt 
  perl blah.pl -s -i ../directory/file2.txt
  ...

    perl raspawn.pl -0 'perl blah.pl -i ' -1 ../directory/ -3 'A.*txt' -3 60

  Executes 'perl blah.pl -s -i ../directory/' command on all txt files
  starting with A in ../directory/ while keeping memory usage below around 60%


END

#for util_cpu()
my ($cpu_prev_idle, $cpu_prev_total, $cpu_prev_usage) = (0,0,0);

my $warmup = 1;

my $MAX_PROC     = 128; #maximum number of active processes that can be spawned

my $MAX_UTIL_DISK = 90; #maximum disk utilization spawn.pl tries not to exceed. In %.

my $MAX_UTIL_MEM  = 80; #maximum memory utilization spawn.pl tries not to exceed. In %.

my $MAX_UTIL_CPU  = 95; #maximum cpu utilization spawn.pl tries not to exceed

my $SLEEP_PERIOD  = 5;          #between spawning new process
my $PRINT_PERIOD  = 3; #print list of active processes every this many sleep periods

my $LIMIT = -1; #Stops when this many spawned. If -1, doesn't stop until all
                #files in the directory processed.

my $nf_start_ok  = 0;        #number of files started fine
my $nf_start_err = 0;        #number of files which did not start fine
my $nf_finished  = 0;        #number of files which processed fine
my $nf_remaining = 0;        #number of files still left to do

my @proca;     #array of spawned processes
my %procf;     #hash of names of files active processes are processing
               #key: pid, value: file name

our ($opt_0, $opt_1, $opt_2, $opt_3, $opt_4, $opt_5, $opt_6, $opt_7, $opt_8, $opt_9);

getopts('0:1:2:3:4:5:6:7:8:9:');

unless ($opt_0 and $opt_1 and $opt_2) {
   print $usage;
}

if ($opt_3) {
   $MAX_UTIL_MEM = $opt_3;
}

if ($opt_4) {
   $MAX_UTIL_DISK = $opt_4;
}

if ($opt_5) {
   $MAX_UTIL_CPU  = $opt_5;
}

if ($opt_6) {
   $SLEEP_PERIOD = $opt_6;
}

if ($opt_7) {
   $MAX_PROC = $opt_7;
}

if ($opt_8) {
   $LIMIT = $opt_8;
}

if ($opt_9) {
   $PRINT_PERIOD = $opt_9;
}

time_init();

spawn ($opt_0, $opt_1, $opt_2);

print "Processed $nf_finished files. Crapped out on $nf_start_err files.\n" .
  "Spent " . time_get_total() ." seconds\n";

if ($nf_remaining) {
   print "Error: there should be no files left to do. It seems that $nf_remaining " .
     "have not been processed\n";
}

exit;

#spawns up to $MAX_PROC processes at a time which execute $cmd command
#over all files in the $dir directory which match the $match mask
###################################################################################
sub spawn {
   my ($cmd,    #in: command. E.g. 'perl ass.pl -s -i '
       $dir,    #in: directory where files (or directories) habituate.
                #e.g. ../directory/
       $match   #in: match string to recognize files to process
                #e.g. '.*xml$' (for file1.xml)
      ) = @_;

   #make sure directory name finishes with "/"
   unless ($dir =~ m/\/$/) {
      $dir = $dir . "/";
   }

   my @ifl;                     #input file list
   @ifl = get_input_list($dir, $match);
   print "\nFOUND " . scalar @ifl . " " . $match . " FILES TO PROCESS IN " . $dir . "\n";
   if ($LIMIT > -1) {
      $#ifl = $LIMIT - 1
   }
   $nf_remaining = scalar @ifl;

   my $i = 0;

   my ($cu, $mu, $du, $su, $un); #cpu util, memory util, disk util, swap usage, unit

   while (scalar @ifl or proc_active_n()) { #run until finished with input list and
                                            #no more active processes
      if (scalar @ifl) {        #not finished with input list?

         $cu = util_cpu();
         $du = util_disk();
         ($mu, $su, $un) = util_mem();

         if ((proc_active_n() < $MAX_PROC) and ($cu < $MAX_UTIL_CPU) and
             ($mu < $MAX_UTIL_MEM) and ($du < $MAX_UTIL_DISK)) {

            my $if = pop(@ifl);                #input file
            my $fc = $cmd . " " .  $dir . $if; #full command
            my $proc = Proc::Background->new($fc);
            if ($proc) {
               push(@proca, $proc);
               $procf{$proc->pid()} = $if;
               print "STARTED:pid " . $proc->pid() . " $fc \n";
               ++$nf_start_ok;
            } else {
               print "Error: could not spawn process: $fc \n";
               ++$nf_start_err;
            }
            if ($warmup) {
               #to ensure the 1st process had enough time to start working.
               #Sometimes, if the process needs to read a huge file, it will
               #not manage to do it before other processes are started which 
               #then clobber each other
               print "\nWarming up. Waiting 10s after 1st process spawned\n";
               sleep(10);
               $warmup = 0;
            }
         }
      }

      proc_active_update();

      $i++;
      my $t = time_get_total();
      if ($i % $PRINT_PERIOD == 0) {
         my $n = $nf_remaining - $nf_start_err;
         printf "ELAPSED " . $t . "s. " .
           "CPU "    . sprintf("%3u", $cu) . "%%, " .
             "MEMORY " . sprintf("%3u", $mu) . "%%, " .
               "DISK "   . sprintf("%3u", $du) . "%%, " .
                 "SWAP "   . sprintf("%u",  $su) . "$un, " .
                   "DONE $nf_finished, TO DO $n. NOW RUNNING " . scalar @proca . ".\n";
         print_hash(" ", \%procf);
         print "\n";
      }
      sleep ($SLEEP_PERIOD);
   }
}

#returns number of spawned processes which are still alive
###################################################################################
sub proc_active_n {
   return scalar @proca;
}

#updates list of active processes by removing processes which have finished
###################################################################################
sub proc_active_update {
   my @ta;                      #temporary array
   foreach my $proc (@proca) {
      if ($proc->alive()) {
         push (@ta, $proc);     #keep only alive processes
      } else {
         print "FINISHED pid: " . $proc->pid() . "\n";
         delete $procf{$proc->pid()};
         ++$nf_finished;
         --$nf_remaining;
      }
   }
   #make the main processor array keep only alive processes
   @proca = @ta;
}


#returns array of names of input files (or directories)
#e.g. list of all xml files in ../bulk/assignments/ directory
###################################################################################
sub get_input_list {
   my ($dir,     #in: directory where files (or directories) habituate
                 #e.g. ../bulk/assignments/
       $match    #in: match string to recognize files
                 #e.g. '.*xml$' (for ad20140204.xml)
      ) = @_;
   my @ta;                      #temporary array
   opendir(DIR, $dir) or die "Error: can not open directory $dir.";
   while ( my $l = readdir(DIR) ) {
      if ($l =~ m/($match)/) {
         push (@ta, $1);
      }
   }

   return @ta;
}

#returns total CPU utilization of all cores in %
###################################################################################
sub util_cpu {

   open (my $F, "/proc/stat") or die ("Cannot open /proc/stat\n");
   my $at = do { local $/; <$F> }; #slurp All Text into a string
   close ($F);

   #grab just the first line with totals for all cores
   my ($tc) = $at =~ m/cpu\s+(.*)\n/; #time columns: "32064297 57346 ..."
   my @ta = split (/\s+/, $tc);       #array of times

   my $tt = sum(@ta);           #total time
   my $ti = $ta[3];             #idle time

   my $dtt = $tt - $cpu_prev_total; #total time since the last time
   my $dti = $ti - $cpu_prev_idle;  #idle time since the last time

   my $u = $cpu_prev_usage;     #cpu usage
   if ($dtt) {                  #avoid division with 0
      $u = (($dtt - $dti) / $dtt) * 100;
   }

   $cpu_prev_usage = $u;
   $cpu_prev_total = $tt;
   $cpu_prev_idle  = $ti;

   #printf "CPU utilization: $u";
   return $u;
}

#returns:
#  total memory utilization in %
#  amount of swap used and unit of measure (kB, mB)..
###################################################################################
sub util_mem {
   my ($mt, $mf, $mc, $st, $sf) = 0; #memory total, memory free, memory cached
                                     #swap total, swap free
   my $un;                 #unit for measuring swap memory (kB, mB...)

   open (my $F, "/proc/meminfo") or die ("Cannot open /proc/meminfo\n");
   my $at = do { local $/; <$F> }; #slurp All Text into a string
   close ($F);

   ($mt, $mf, $mc, $st, $sf, $un) =
     $at =~ m/MemTotal:\s*(\d+)\s.*MemFree:\s*(\d+)\s.*\nCached:\s*(\d+)\s.*\nSwapTotal:\s*(\d+)\s.*\nSwapFree:\s*(\d+)\s([a-zA-Z]*)\n/s;
   #print "mem tot $mt, mem free $mf mem cached $mc, swap total $st $un, " .
   #  "swap free $sf $un\n";

   my $mu = 100;                #memory usage
   if ($mt) {
      $mu = 100*(($mt - $mf - $mc)/$mt);
   }

   my $su = $st - $sf;

   #print "memory utilization $mu, swap used: $su $un\n";

   return ($mu, $su, $un);
}

#returns highest disk utilization in % (of all disks)
###################################################################################
sub util_disk {

   open (my $F, "iostat -dx |") or die ("Cannot open iostat\n");

   my $hdu = 0;                 #highest disk utilization
   my $du  = 0;                 #disk utilization
   while (<$F>) {
      if (/\s([\d\.]+)$/) {
         $hdu = $1 > $hdu ? $1 : $hdu;
      }
   }
   close($F);

   #print "highest disk utilization: $hdu\n";
   return $hdu;
}




