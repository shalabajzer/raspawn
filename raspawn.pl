#!/usr/bin/perl -w
# This code is licensed under GPL 2.0

use strict;
use warnings;
use List::Util qw(sum);
use Fcntl;
use Getopt::Std;
use Proc::Background;

my $usage=<<END;

raspawn.pl -f 'file_w_commands' -0 'command' -1 'directory' -2 'regex' [-3 mem_util]
  [-4 disk_util] [-5 cpu_util] [-6 sleep_between] [-7 max_procs] [-8 total_procs] [-9 print_status_s]

Resource Aware spawn.
Spawns a number of processes while trying to keep resources
utilization just below the maximum. Waits until there are enough system
resources before spawning a new process. Runs a list of commands in an
input file or runs a given command over a number of files/directories
in a given directory.

Usage:
  -f - file containing list of commands to execute. Alternatively, use -0, 
       -1 and -2 options. Each line is treated as a command.
       lines starting with # are treated as comments and skipped
  -0 - command to execute. E.g. 'blah.sh __d__/__f__'.  __d__ is replaced
       with the directory (-1) and __f__ with the file (which matches the 
       regular expression). If you need ' in the command use this '\''
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
       this many spawned. If left out, processes all 
  -9 - print status line every this many sleep periods (-s)
       5 if left out.

  -q - be quiet. Don't print anything out.

(using numerical opions -0 to -9 in order to avoid possible overlap 
with options of the command executed.)

Examples: 

  raspawn.pl -f bach_file -5 70
    This executes all commands in the "batch_file" file while keeping
    toal CPU utilization below 70% approximately.

  raspawn.pl -0 'cat __d__/__f__' -1 './' -2 '.*xml' -8 2
    Assuming the current directory has file1.xml and file2.xml, this executes:
         cat ./file1.xml
         cat ./file2.xml

  raspawn.pl -0 'sleep 10; ls -la __d__/__f__' -1 '.' -2 '.*xml' -8 2
    Assuming the current directory has file1.xml and file2.xml, this executes:
         sleep 10; ls -la ./file1.xml
         sleep 10; ls -la ./file2.xml

  raspawn.pl -0 'perl blah.pl -i __f__ -p' -1 '.' -2 'A.*txt' -3 60
    Executes (assuming file1.txt and file2.txt in the current directory):
      perl blah.pl -i file1.txt -p
      perl blah.pl -i file2.txt -p
    while keeping memory usage below 60%

  raspawn.pl -0 'bbcp -N io '\''tar -c -O -C __d__ __f__'\'' '\''192.168.2.15:tar -x -C /bla/files'\''' -1 '/bla1/files' -2 '[^\.]+' -6 0 -7 16
     Executes (assuming subdirectory 'subdir' and file 'file1' in /bla1/files):
       bbcp -N io 'tar -c -O -C /bla1/files file1' '192.168.2.15:tar -x -C /bla/files'
       bbcp -N io 'tar -c -O -C /bla1/files subdir' '192.168.2.15:tar -x -C /bla/files'
     Spawns maximum 16 processes in parallel and waits 0s between spawning.
     (BTW, this will do very fast copy of all the files and subdirectories in /bla1/files
      from the current machine to the 192.168.2.15 into directory /page/files)
     (BBTW, '[^\.]+' is to match names (of files and subdirs) without . in them (to exclude . and ..))
END

#for util_cpu()
my ($cpu_prev_idle, $cpu_prev_total, $cpu_prev_usage) = (0,0,0);

my $warmup = 1;

my $MAX_PROC     = 128; #maximum number of active processes that can be spawned

my $MAX_UTIL_DISK = 90; #maximum disk utilization we try not to exceed. In %.

my $MAX_UTIL_MEM  = 80; #maximum memory utilization we try not to exceed. In %.

my $MAX_UTIL_CPU  = 95; #maximum cpu utilization we try not to exceed

my $SLEEP_PERIOD  = 5;	#between spawning new process

my $PRINT_PERIOD  = 5;  #print list of active processes every this many sleep periods

my $LIMIT = -1; #Stops when this many spawned. If -1, doesn't stop until all processed.

my $np_start_ok  = 0;	  #number of processes started fine
my $np_start_err = 0;	  #number of processes which did not start fine
my $np_ended_ok  = 0;	  #number of processes which processed fine
my $np_ended_err = 0;	  #number of processes which processed fine
my $np_remaining = 0;	  #number of processes still left to do

my @proca;		#array of active processes
my %procc;		#commands being processed: key: pid, value: command

our ($opt_f, $opt_0, $opt_1, $opt_2, $opt_3, $opt_4, $opt_5, $opt_6, $opt_7, $opt_8, $opt_9, $opt_q);

getopts('f:0:1:2:3:4:5:6:7:8:9:q');

unless ($opt_f or ($opt_0 and $opt_1 and $opt_2)) {
	print $usage;
	exit 1;
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

my $STOP_AT_FIRST_ERROR = 1;
if ($STOP_AT_FIRST_ERROR) {
	 printout("Stops as soon as any command returns an error\n\n");
}

my @cl; #command list - array of commands (with all the arguments supplied...) to execute
@cl = create_command_list();

# foreach my $c (@cl) {
#  	printout ("$c\n");
#  }

spawn (@cl);

print_end_status();

if ($np_start_err or $np_ended_err) {
	 exit 1;
} else {
	 exit 0; #sucess - no commands crapped out
}


#creates list of commands to execute
#returns array with the list
###################################################################################
sub  create_command_list {

	my @cl; #command list

	if ($opt_f) {
		open FILE_I, "< $opt_f" or printout ("\nERROR: Can't open $opt_f.\n\n");
		printout ("input file: $opt_f\n");
		while(<FILE_I>) {
			my $l = $_;
			#skip comment lines (starting with #) and empty lines
			unless (($l =~ m/\s*#/) or ($l =~ m/^\s*$/)) {
				$l =~ s/\n$//;	  #chop off newline
				push (@cl, $l);
			}
		}

		if ($LIMIT > -1) {  #(must chop off before reverse(), eh)
			$#cl = $LIMIT - 1
		}
		@cl = reverse(@cl); #to get it in the same order as in the input file

	} else {
		#create the list of commands from the given command, directory and mask

		my $cmd   = $opt_0; #command. E.g. 'perl ass.pl -s -i '
		my $dir   = $opt_1; #directory where files (or directories) habituate.
		#e.g. ../directory/
		my $match = $opt_2; #match string to recognize files to process
                          #e.g. '.*xml$' (for file1.xml)

		my @ifl;				  #input file list
		@ifl = get_files_list($dir, $match);
		@ifl = reverse(sort(@ifl));

		printout ("\nFOUND " . scalar @ifl . " " . $match . " FILES TO PROCESS IN " . $dir . "\n");

		foreach my $if (@ifl) {  #input file
			my $fc = $cmd;
			$fc =~ s/__d__/$dir/g;
			$fc =~ s/__f__/$if/g;

			push (@cl, $fc);
		}

		if ($LIMIT > -1) {
			$#cl = $LIMIT - 1
		}
	}

	return @cl;
}

#spawns up to $MAX_PROC processes at a time which execute commands in the list
###################################################################################
sub spawn {
	my (@cl     #in: command list
		) = @_;

	$np_remaining = scalar @cl;

	my $sp = 0; #sleep period - new process can be spawned when this is <=0
	my $pp = 0; #print period

	my ($cu, $mu, $du, $su, $un); #cpu util, memory util, disk util, swap usage, unit

	while (scalar @cl or proc_active_n()) { #run until finished with input list and
		                                     #no more active processes
		$cu = util_cpu();
		$du = util_disk();
		($mu, $su, $un) = util_mem();

		proc_active_update();
		my $nr = $np_remaining - $np_start_err - scalar @proca; #number of remaining

		if ( (proc_active_n() < $MAX_PROC) and ($cu < $MAX_UTIL_CPU) and
			  ($mu < $MAX_UTIL_MEM) and ($du < $MAX_UTIL_DISK) and ($nr > 0) and
			  ($sp <= 0) ) {

			my $fc = pop(@cl);					  #full command
			my $proc = Proc::Background->new($fc);

			$sp = $SLEEP_PERIOD;

			if ($proc) {
				push(@proca, $proc);
				$procc{$proc->pid()} = $fc;
				printout ("started:pid " . $proc->pid() . " $fc \n");
				++$np_start_ok;
			} else {
				printout ("Error: could not spawn process: $fc \n");
				++$np_start_err;
			}
			if ($warmup) {
				#to ensure the 1st process had enough time to start working.
				#Sometimes, if the process needs to read a huge file, it will
				#not manage to do it before other processes are started which
				#then clobber each other
				printout ("\nWarming up. Waiting 5s after 1st process spawned\n");
				sleep(5);
				$warmup = 0;
			}
		} else {
			#either hit a max utilization of a resource or spawned max processes
			#or no more remaining or did not sleep $SLEEP_PERIOD since last spawn
			sleep(1);
			$pp--;
			$sp--;
		}

		if ($pp <= 0) {
			my $t = time_get_total();
			my $bla = sprintf "elapsed " . $t . "s. " .
			  "CPU "    . sprintf("%3u", $cu) . "%%, " .
				 "memory " . sprintf("%3u", $mu) . "%%, " .
					"disk "   . sprintf("%3u", $du) . "%%, " .
					  "swap "   . sprintf("%u",  $su) . "$un, " .
						 "Done: " . ($np_ended_ok+$np_ended_err) . " (" . $np_ended_err . " errors). " .
						 "To do $nr. Running " . scalar @proca . ".\n";
			printout ($bla);
			print_hash("  ", \%procc, "\n");
			printout ("\n");
			$pp = $PRINT_PERIOD;
		}

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
	my @ta;							  #temporary array
	foreach my $proc (@proca) {
		if ($proc->alive()) {
			 push (@ta, $proc);	  #keep only alive processes
		} else {
			--$np_remaining;

			 my $es = $proc->wait() / 256; #exit status
			 printout ("finished pid: " . $proc->pid());
			 if ($es) {
				  printout (" with ERRORS. Exited with: $es\n");
				  ++$np_ended_err;
				  if ($STOP_AT_FIRST_ERROR) {
						printout("ERROR. CANCELLING FURTHER PROCESSING...\n");
						print_end_status();
						exit 1;
				  }
			 } else {
				  printout ("\n");
				  ++$np_ended_ok;
			 }

			delete $procc{$proc->pid()};
		}
	}
	#make the main processor array keep only alive processes
	@proca = @ta;
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

	my $tt = sum(@ta);                 #total time
	my $ti = $ta[3];                   #idle time

	my $dtt = $tt - $cpu_prev_total;   #total time since the last time
	my $dti = $ti - $cpu_prev_idle;    #idle time since the last time

	my $u = $cpu_prev_usage;          #cpu usage
	if ($dtt) { #avoid division with 0
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
	my $un;						#unit for measuring swap memory (kB, mB...)

	open (my $F, "/proc/meminfo") or die ("Cannot open /proc/meminfo\n");
	my $at = do { local $/; <$F> }; #slurp All Text into a string
	close ($F);

	($mt, $mf, $mc, $st, $sf, $un) =
	  $at =~ m/MemTotal:\s*(\d+)\s.*MemFree:\s*(\d+)\s.*\nCached:\s*(\d+)\s.*\nSwapTotal:\s*(\d+)\s.*\nSwapFree:\s*(\d+)\s([a-zA-Z]*)\n/s;
	#printout ("mem tot $mt, mem free $mf mem cached $mc, swap total $st $un, " .
	#  "swap free $sf $un\n");

	my $mu = 100;					  #memory usage
	if ($mt) {
		$mu = 100*(($mt - $mf - $mc)/$mt);
	}

	my $su = $st - $sf;

	#printout ("memory utilization $mu, swap used: $su $un\n");

	return ($mu, $su, $un);
}

#returns highest disk utilization in % (of all disks)
###################################################################################
sub util_disk {

	#1 1 is to give 1 reading over 1 second
	open (my $F, "iostat -dxy 1 1 |") or die ("Cannot open iostat\n");

	my $hdu = 0;					  #highest disk utilization
	my $du  = 0;					  #disk utilization
	while (<$F>) {
		if (/\s([\d\.]+)$/) {
			$hdu = $1 > $hdu ? $1 : $hdu;
		}
	}
	close($F);

	#printout ("highest disk utilization: $hdu\n");
	return $hdu;
}

my $st; #start time
my $pt; #previous time (that get_delta_time() was invoked)
###################################################################################
sub time_init {
    $st = time();
}

#returns total time elapsed since init_time() was invoked
###################################################################################
sub time_get_total {
	unless ($st) {
		return -1;
	}
	return time() - $st; #total time
}

sub print_hash {
	my ($tb,       #text before
		 $hr,       #hash reference
		 $ta        #text after
		) = @_;

	while ( my ($key, $value) = each(%$hr) ) {
		printout ($tb . "$key => $value " . $ta);
	}
}

###################################################################################
sub  print_end_status {
	 printout ("\nProcessed " . ($np_start_ok+$np_start_err) . " commands in total, " .
				  "$np_ended_ok of which finished fine and further " .
				  "$np_ended_err finished with errors, whereas " .
				  "$np_start_err didn't initiate properly.\n" .
				  "Spent " . time_get_total() ." seconds\n");
	 
	 if ($np_remaining) {
		  printout ("Error: there should be no commands left to do. It seems that $np_remaining " .
						"have not been processed\n");
	 }
}


###################################################################################
sub  printout {
	my ($t,       #text to print
		) = @_;

	if ($opt_q) {
		return;
	}

	#preceed all non-empty lines with " #" so it is easier to spot/eliminate in
   #the sea of other lines
	my $ot=""; #output text
	foreach (split(/\n/, $t)) {
		 my $l = $_ . "\n";
		 unless ($l =~ m/^\s*$/) {
			  $l= "# " . $l;
		 }
		 $ot .= $l;
	}
	print "$ot";
}

#returns array of names of input files (or directories)
#e.g. list of all xml files in ../bla directory
###################################################################################
sub get_files_list {
	my ($dir,	  #in: directory where files (or directories) habituate
					  #e.g. ../bla/
		 $match	  #in: match string to recognize files
					  #e.g. '.*xml$' (for ad20140204.xml)
		) = @_;

	my @ta;							  #temporary array
	opendir(DIR, $dir) or die "Error: can not open directory $dir.";
	while ( my $l = readdir(DIR) ) {
		if ($l =~ m/($match)/) {
			push (@ta, $1);
		}
	}

	return @ta;
}
