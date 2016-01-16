/*
 * Based on wwsr - Wireless Weather Station Reader
 * Michael Pendec (michael.pendec@gmail.com)
 * Svend Skafte (svend@skafte.net)
 * Adam Pribyl (covex@lowlevel.cz)
 * Bradley Jarvis (bradley.jarvis@dcsi.net.au)
 * Lukas Zvonar (lukic@mag-net.sk)
 * Petr Zitny (petr@zitny.net)
 * Alexey Ozerov (alexey@ozerov.de)
 * 2011-12-20 some code cleaning and restructure, read_period, km/h wind speed
 * 2011-12-21 introduce ws_parse(), struct wrecord
 * 2011-12-22 flexible read period, server url, curl post data
 * 2011-12-25 add inches, mph, utc, introduce ws_format(), urlencode, additional url
 * 2011-12-26 readd rain 60 min calculation
 * 2011-12-28 read config vars from cfg file, multiple add_url, date DD.MM.YYYY and time HH:MM formats
 * 2011-12-29 read read_period from WS, add rain from 0h calculation
 * 2012-01-01 fix error handling in main(), handle ws_submit feedback, get lasttime, submit multiple positions, submit error
 * 2012-01-02 submit last error text to frewe-server
 * 2012-01-03 add support for wetter.com, more accurate time calculation for position shift, accurate cfg read
 * 2012-01-05 don't encode : in HH:MM
 * 2012-01-05 rewrite read_cfg(), add station type, support WH3080, calibration, read data_count
 * 2012-01-08 check data_count when looking for old records, plausi check for age, read illumination & UV
 * 2012-01-14 Better check for invalid values, skip record if too many errors, fix rain calibration
 * 2012-01-15 Double read the data from USB device
 * 2012-01-16 Fix time calculation for submission to frewe-server
 * 2012-01-19 Fix linebreak after OK problem on frewe-server responce
 * 2012-01-24 Integrate weather service URLs, fix bad data prevents position loop problem
 * 2012-01-25 Read weather service access data from cfg
 * 2012-01-26 No formatting in ws_parse, different errorstrings for different services
 * 2012-01-27 Fix address calculation on address overflow
 * 2012-01-28 Handle signals, fix ws_close(), fix address calculation again, multiple tries on USB read problems, recognize sensor loss, station type %K
 * 2012-01-28 Don't handle SIGHUP
 * 2012-02-01 Use http_fetcher instead of curl (saves 200 KB, however is not IPv6 capable)
 * 2012-02-03 Resubmit data also to known weather services
 * 2012-02-04 Handle DOS encoded lines in cfg file, read alarm config, introduce ws_alarm, clean up some code
 * 2012-02-05 Configure emails for errors and alarms in cfg file, enable multiple alarms of each type, fix memory in URLencode
 * 2012-02-09 Fix UV value output
 * 2012-02-11 Add Sauerlandwetter
 * 2012-02-23 Don't drop record if sensors are lost, NB: total rain, indoor values and abs. pressure (?) are usable even if sensors are lost
 		info: frewe.ws_dump - 0xD6C0: 0x05 0x38 0xEE 0x00 0xFF 0xFF 0xFF 0xEE 0x27 0xFF 0xFF 0xFF 0x8C 0x6B 0x03 0x40
 		info: frewe.ws_dump - 0xD6D0: 0x05 0x38 0xEE 0x00 0x35 0x67 0x00 0xEC 0x27 0x11 0x18 0x00 0x08 0x6B 0x03 0x00
 * 2012-02-24 Only resend data to services which support it, don't resend if sensor lost (sensor lost = good data)
 * 2012-03-06 Handle HighIndoorTemp and LowIndoorTemp Alarms
 * 2012-04-04 Continue sending to other weather services on error
 * 2012-05-24 Don't run out of available data on rain calculation
 * 2012-06-11 Flush the stdout (enable data logging into a file), use stderr for debug and info output, wetter.com replaced wetter.de
 * 2012-06-13 Include age of last record last_age in record datetime, pos60 and pos0h calculation, fix rainday calculation for old records
 * 2012-06-15 Ignore get lasttime errors if frewe-server is not available
 * 2012-07-27 make unit conversions in ws_format() instead of ws_parse()
 * 2012-07-27 WH3080: Transmit illumination in W/m² instead of Lux to WUnderground, PWS, Awekas, METOffice
 * 2012-09-01 Remove Wetterpool.de, add Wetternetz Sachsen
 * 2013-03-16 Remove Sauerlandwetter, rename time_interval to read_period, increase http timeout to 15 sec, print version info with -H
 * 2013-03-16 Trying to fix double submissions with -59 logical seconds, later changed back to -1
 * 2013-04-11 Fix SIGSERV by getlasttime from wrong input, fix pause calculation (int overflow)
 * 2013-04-25 Fix pause calculation again
 * 2013-05-23 Fix pause calculation again (use usleep), use getaddrinfo in http_fetcher.c, better validation rainday and rainhour
 * 2013-06-22 Trying to fix stability issue when FreweServer fails, ignore FreweServer submission fault
 * 2013-07-01 Fix stability issue within logger function (use strcpy instead of strcat)
 * 2013-07-12 Try resetting USB port on errno 62 when setting alt device
 * 2013-10-13 New interface URL for Wetternetz Sachsen (2.1)
 * 2014-08-10 Add fhem file
 * 2015-03-25 Send UTC time to frewe-server
 * 2015-04-24 Handle lasttime as UTC
 * 2015-08-20 Don't write fhem.txt for older records
 * 2016-01-16 Separate read interval for fhem.txt, run each 48 seconds for FHEM

 * TODO: Handle rain counter overflow
 */

// #define _XOPEN_SOURCE 1 /* was needed for strptime? */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <signal.h>
#include <usb.h>
#include <time.h>
#include <math.h>
#include <elf.h> 
#include <openssl/md5.h>
#include "http_fetcher.h"

#define PROGRAM_VERSION "1.19"

#define DEFAULT_VENDOR    0x1941
#define DEFAULT_PRODUCT   0x8021
#define DEFAULT_FORMAT    (char *)"\ntime:                  %N\nage:                   %a min\nin humidity:           %h %%\nout humidity:          %H %%\nin temperature:        %I C\nout temperature:       %O C\ndewpoint temperature:  %E C\nwindchill temperature: %C C\nwind speed:            %W km/h\nwind gust:             %G km/h\nwind direction:        %D\npressure:              %P hPa\nrel. pressure:         %L hPa\nrain total:            %R mm\nrain 60 min:           %S mm\nrain since 0h:         %T mm\nillumination:          %M lux\nUV:                    %U\n\n"

// Look http://www.jim-easterbrook.me.uk/weather/mm/ for memory map

#define WS_READ_PERIOD_ADDRESS 16
#define WS_DATA_COUNT_ADDRESS 27
#define WS_CURRENT_POSITION_ADDRESS 30

#define WS_MIN_ENTRY_ADDR 0x0100
#define WS_MAX_ENTRY_ADDR 0x10000
#define WS_TOTAL_ENTRIES ((WS_MAX_ENTRY_ADDR-WS_MIN_ENTRY_ADDR)/ws_entry_size)

#define MAX_ALARMS	20
#define MAX_ADD_URLS	10

// extern double round (double __x) __attribute__ ((__nothrow__)) __attribute__ ((__const__));

int ws_open(usb_dev_handle **dev,uint16_t vendor,uint16_t product,int reset_done);
int ws_close(usb_dev_handle **dev);
int ws_read(usb_dev_handle *dev,uint16_t address,uint8_t *data,uint16_t size);
int ws_reset(usb_dev_handle *dev);
int ws_format(char *format, char *output, unsigned char urlencode, char *user, char *pass, char *error);
int ws_dump(uint16_t address,uint8_t *buffer,uint16_t size,uint8_t width);
uint16_t get_address(uint16_t base, int position);
void strcatenc(char *out,char *text,unsigned char urlencode);
void signal_handler(int signal);
long diff_time(const struct timeval *tact, const struct timeval *tlast);

char* URLencode(char *str);
char* URLdecode(char *str);

struct wrecord
{	time_t datetime;
	char winddir[4];
	float tempout,tempin,windspeed,windspeedms,windgust,tempchill,tempdew,pressabs,pressrel,rain,rainhour,rainday;
	float illu;
	short humin,humout,age;
	short uv,winddeg;
	char ok;
} w,w1;

struct calib
{	float tempin_factor,tempin_offset,tempout_factor,tempout_offset,humin_factor,humin_offset,humout_factor,humout_offset;
	float windspeed_factor,windspeed_offset,windgust_factor,windgust_offset,pressabs_factor,pressabs_offset,rain_factor,rain_offset,winddir_offset;
	float illu_factor,illu_offset,uv_factor,uv_offset;
} c = {1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1,0};

typedef enum log_event
{	LOG_DEBUG=1,
	LOG_WARNING=2,
	LOG_ERROR=4,
	LOG_INFO=8
} log_event;

FILE *_log_debug=NULL,*_log_warning=NULL,*_log_error=NULL,*_log_info=NULL;
void logger(log_event event,char *function,char *msg,...);

char *errorstring="N/A"; 			// What to write if value is not available or out of range
char *format=DEFAULT_FORMAT, *add_url[MAX_ADD_URLS];
char *FHEM_errorstring="";
char *FHEM_format=DEFAULT_FORMAT;
char *FHEM_file=NULL;
char *frewe_server_url=NULL, *frewe_server_key=NULL, *frewe_server_url_submit=NULL, *frewe_server_url_lasttime=NULL, *frewe_server_url_error=NULL, *frewe_server_url_alarm=NULL;
char *frewe_server_senddata=NULL, *frewe_server_resend=NULL, *error_email=NULL;
char *ws_type="WH1080";				// default to WH1080

char ws_entry_size;
int run_interval=0;			// in seconds, 0 means run once and exit, change it by -r option or RunInterval cfg
int fhem_interval=48;
int read_period;			// Minutes between each stored reading (set in the WS configuration)
int altitude=0;				// default altitude is sea level in meter - change it by -A option or Altitude cfg
uint16_t vendor=DEFAULT_VENDOR,product=DEFAULT_PRODUCT;
char add_url_counter=0, alm_counter=0;

usb_dev_handle *dev=NULL;

//char filebuf[256];
char *filebuf=NULL; 			// Will be allocated by html_fetcher

char *frewe_server_url_submit_template   = "%s?serverkey=%s&action=addrecord&datetime=%%n&tempin=%%I&tempout=%%O&tempdew=%%E&tempchill=%%C&humin=%%h&humout=%%H&windgust=%%G&windspeed=%%W&winddir=%%D&pressabs=%%P&pressrel=%%L&rain=%%R&illu=%%M&uv=%%U&rainrate=%%S";
char *frewe_server_url_lasttime_template = "%s?serverkey=%s&action=getlasttime";
char *frewe_server_url_error_template    = "%s?serverkey=%s&action=submiterror&email=%s";
char *frewe_server_url_alarm_template    = "%s?serverkey=%s&action=alarm";

struct wservice
{	char *name;
	char *userkey;
	char *passkey;
	char *url;
	char *user;
	char *pass;
	char md5;
	char *error;
	char resend;
} ws[] =
{	{ "Weather Underground", "WUnderground_StationID", "WUnderground_Password", "http://weatherstation.wunderground.com/weatherstation/updateweatherstation.php?action=updateraw&ID=%x&PASSWORD=%X&dateutc=%n&winddir=%d&windspeedmph=%w&windgustmph=%g&humidity=%H&tempf=%o&dewptf=%e&baromin=%l&indoortempf=%i&indoorhumidity=%h&rainin=%s&dailyrainin=%t&solarradiation=%m&UV=%U&softwaretype=Freetz%%20Weather", NULL, NULL, 0, "", 1},
	{ "PWS Weather", "PWSWeather_StationID", "PWSWeather_Password", "http://www.pwsweather.com/pwsupdate/pwsupdate.php?action=updateraw&ID=%x&PASSWORD=%X&dateutc=%n&winddir=%d&windspeedmph=%w&windgustmph=%g&humidity=%H&tempf=%o&dewptf=%e&baromin=%l&indoortempf=%i&indoorhumidity=%h&rainin=%s&dailyrainin=%t&solarradiation=%m&UV=%U&softwaretype=Freetz%%20Weather%%20on%%20%K", NULL, NULL, 0, "", 0},
	{ "Awekas", "Awekas_Username", "Awekas_Password", "http://www.awekas.at/extern/eingabe_pruefung.php?val=%x;%X;%Y;%Z;%O;%H;%L;%T;%W;%d;;;;de;;%G;%m;%U;;;;%S;", NULL, NULL, 1, "", 0},
	{ "MET Office", "METOffice_SiteID", "METOffice_SiteAuthKey", "http://wow.metoffice.gov.uk/automaticreading?siteid=%x&siteAuthenticationKey=%X&dateutc=%n&winddir=%d&windspeedmph=%w&windgustmph=%g&humidity=%H&tempf=%o&dewptf=%e&baromin=%l&indoortempf=%i&indoorhumidity=%h&rainin=%s&dailyrainin=%t&solarradiation=%m&UV=%U&softwaretype=Freetz%%20Weather%%20on%%20%K", NULL, NULL, 0, "", 1},
//	{ "Wetternetz Sachsen", "WetternetzSachsen_UserID", "WetternetzSachsen_Password", "http://www.wetternetz-sachsen.de/get_daten_20.php?var=%x;%X;V2.0;%K;%Z;%Y;%O;--;--;--;--;--;%H;%E;--;--;--;--;--;--;--;%S;--;--;--;--;%T;--;%W;%d;%G;--;--;--;--;--;--;--;--;--;%C;--;--;%L;%P;--;--;--;--;--;--;--;--;--;--;--;--;--;--;%m;--;--;%U;--;%M;--;--;--;--;--;--;--;--;--;--;--;--;--;--;--;--;%R;--;--;--;--;--;--;--;--;--;--;--;--;--", NULL, NULL, 0, "", 0},
	{ "Wetternetz Sachsen", "WetternetzSachsen_UserID", "WetternetzSachsen_Password", "http://www.wetternetz-sachsen.de/get_daten_21.php?var=%x;%X;V2.1;FreetzW;%Z;%Y;-2;%O;--;--;--;--;--;%H;--;--;%S;--;--;--;%W;%d;%G;--;--;--;--;--;%C;--;--;%L;%P;--;--;--;--;--;--;--;%m;--;--;%U;--;--;--;--;--;--;--;--;--;--;--;--;--;--;--;--;--;--;--;--;--;", NULL, NULL, 0, "", 0},
	{ "Wetter.com", "Wetter.com_Username", "Wetter.com_Password", "http://www.wetterarchiv.de/interface/http/input.php?benutzername=%x&passwort=%X&datum=%y&feuchtigkeit=%H&temperatur=%O&windrichtung=%d&windstaerke=%v&luftdruck=%L&niederschlagsmenge=%S&niederschlagsmenge_zeit=60", NULL, NULL, 0, "", 1},
	{ "Wetter.de OBSOLETED", "Wetter.de_Username", "Wetter.de_Password", "http://www.wetterarchiv.de/interface/http/input.php?benutzername=%x&passwort=%X&datum=%y&feuchtigkeit=%H&temperatur=%O&windrichtung=%d&windstaerke=%v&luftdruck=%L&niederschlagsmenge=%S&niederschlagsmenge_zeit=60", NULL, NULL, 0, "", 1},	 // This is only for compatibility to pre 1.11 version config files
	{ "Wedaal", "Wedaal_Username", "Wedaal_StationPass", "http://www.wedaal.de/get_wetter.php?val=%x;%X;%O;%H;%L;%T;%W;%d;%Z;%Y;;;;;;;;;;;;;;;", NULL, NULL, 1, "", 0}
};

char *walarm_type[] =
{	"HighOutdoorTemp", "LowOutdoorTemp", "HighWindchillTemp", "LowWindchillTemp", "HighDewTemp", "LowDewTemp", 
	"HighIndoorTemp", "LowIndoorTemp", "HighOutdoorHumidity", "LowOutdoorHumidity", "HighIndoorHumidity", "LowIndoorHumidity", 
	"HighRelPressure", "LowRelPressure", "HighWind", "LowWind", "HighGust", "LowGust", 
	"HighRainHour", "LowRainHour", "HighRainDay", "LowRainDay", "HighIllumination", "LowIllumination", "HighUV", "LowUV"
};

struct walarm
{	char *type;
	float threshold;
	char set;
	char *url;
	char *run;
	char *email;
} alm[MAX_ALARMS];


//***************************************************************
// MAIN
//***************************************************************

int main(int argc, char **argv)
{
	int rv=0,c,i,l;
	uint8_t help=0,dump=0, md5[16];
	char *cp, md5str[33];
	int position=0,startpos,endpos,curpos;		// default position is 0 (=now) - altering this by -p option can lead to read some of stored values
	int pos60, pos0h;
	int data_count;
	int last_age;
	int read_weather,read_fhem;

	uint16_t address,address0,address60,address0h;
	long pause;
	time_t starttime,curtime,lasttime;
	struct timeval tact, tlast, tlastfhem;
	struct tm *tmptr, tm;
	char *output;
	
	FILE *fd;

	_log_error=stderr;
	_log_info=stderr;

// Handle signals, don't break on SIGHUP!

	signal(SIGTERM, signal_handler);
	signal(SIGQUIT, signal_handler);
	signal(SIGINT, signal_handler);
	signal(SIGFPE, signal_handler);
	signal(SIGILL, signal_handler);
	signal(SIGSEGV, signal_handler);
	signal(SIGBUS, signal_handler);

// Init add_url array, need it?

	for (i=0;i<MAX_ADD_URLS;i++) add_url[i]=NULL;

// Parse options

	while (rv==0 && (c=getopt(argc,argv,"hH?vxf:d:a:A:p:e:t:s:c:u:r:t:k:"))!=-1)
	{
		switch (c)
		{
			case 'a': // set device id
				sscanf(optarg,"%hX:%hX",&vendor,&product);
				logger(LOG_DEBUG,"main","USB device set to vendor=%04X product=%04X",vendor,product);
				break;

			case 'A': // set altitude
				sscanf(optarg,"%d",&altitude);
				logger(LOG_DEBUG,"main","altitude set to %d",altitude);
				break;

			case 'p': // set position
				sscanf(optarg,"%d",&position);
				logger(LOG_DEBUG,"main","weather station log position set to %d",position);
				break;

			case 'c': // read configuration from file
				i=read_cfg(optarg);
				logger(LOG_DEBUG,"main","reading cfg from file %s returned %d",optarg,i);
				break;

			case 'r': // set continuous run with time interval
				sscanf(optarg,"%d",&run_interval);
				logger(LOG_DEBUG,"main","continuos run interval set to %d seconds",run_interval);
				break;

			case 'v': // verbose messages
				_log_debug=_log_warning=stderr;
				logger(LOG_DEBUG,"main","Verbose messaging turned on");
				break;

			case 'x': // XML export
				optarg = "<data>\
\n\t<timestamp>\n\t\t<data>%N</data>\n\t</timestamp>\
\n\t<temp>\n\t\t<indoor>\n\t\t\t<data>%I</data>\n\t\t\t<unit>C</unit>\n\t\t</indoor>\n\t\t<outdoor>\n\t\t\t<data>%O</data>\n\t\t\t<unit>C</unit>\n\t\t</outdoor>\n\t\t<windchill>\n\t\t\t<data>%C</data>\n\t\t\t<unit>C</unit>\n\t\t</windchill>\n\t\t<dewpoint>\n\t\t\t<data>%E</data>\n\t\t\t<unit>C</unit>\n\t\t</dewpoint>\n\t</temp>\
\n\t<wind>\n\t\t<speed>\n\t\t\t<data>%W</data>\n\t\t\t<unit>km/h</unit>\n\t\t</speed>\n\t\t<gust>\n\t\t\t<data>%G</data>\n\t\t\t<unit>km/h</unit>\n\t\t</gust>\n\t\t<direct>\n\t\t\t<data>%d</data>\n\t\t\t<unit>degrees</unit>\n\t\t</direct>\n\t\t<direct_str>\n\t\t\t<data>%D</data>\n\t\t\t<unit>Str</unit>\n\t\t</direct_str>\n\t</wind>\
\n\t<pressure>\n\t\t<abs>\n\t\t\t<data>%P</data>\n\t\t\t<unit>hPa</unit>\n\t\t</abs>\n\t\t<rel>\n\t\t\t<data>%L</data>\n\t\t\t<unit>hPa</unit>\n\t\t</rel>\n\t</pressure>\
\n\t<rain>\n\t\t<hour>\n\t\t\t<data>%?</data>\n\t\t\t<unit>mm</unit>\n\t\t</hour>\n\t\t<day>\n\t\t\t<data>%?</data>\n\t\t\t<unit>mm</unit>\n\t\t</day>\n\t\t<total>\n\t\t\t<data>%R</data>\n\t\t\t<unit>mm</unit>\n\t\t</total>\n\t</rain>\
\n\t<humidity>\n\t\t<indoor>\n\t\t\t<data>%h</data>\n\t\t\t<unit>%%</unit>\n\t\t</indoor>\n\t\t<outdoor>\n\t\t\t<data>%H</data>\n\t\t\t<unit>%%</unit>\n\t\t</outdoor>\n\t</humidity>\
\n</data>\n";
			case 'f': // Format output
				logger(LOG_DEBUG,"main","Format output using '%s'",optarg);
				format=optarg;
				break;

			case 's': // Server URL
				logger(LOG_DEBUG,"main","Server URL set to '%s'",optarg);
				frewe_server_url=optarg;
				break;

			case 'k': // Server Key
				logger(LOG_DEBUG,"main","Server Key set to '%s'",optarg);
				frewe_server_key=optarg;
				break;

			case 't': // Device Type
				logger(LOG_DEBUG,"main","Device type set to '%s'",optarg);
				ws_type=optarg;
				break;

			case 'u': // Additional URL
				logger(LOG_DEBUG,"main","Additional URL set to '%s'",optarg);
				if (add_url_counter<MAX_ADD_URLS) add_url[add_url_counter++]=optarg;
				break;

			case 'e': // Error string
				logger(LOG_DEBUG,"main","Error string set to: '%s'",optarg);
				errorstring=optarg;
				break;

			case 'd': // Dump raw data from weather station
			{
				uint16_t a,s,w;
				dump=1;
				a=0;
				s=0x100;
				w=16;
//				sscanf(optarg,"0x%hX:0x%hX",&a,&s);
				if (sscanf(optarg,"0x%hX:0x%hX",&a,&s)<2)
				if (sscanf(optarg,"0x%hX:%hu",&a,&s)<2)
				if (sscanf(optarg,"%hu:0x%hX",&a,&s)<2)
				if (sscanf(optarg,"%hu:%hu",&a,&s)<2)
				if (sscanf(optarg,":0x%hX",&s)<1)
					sscanf(optarg,":%hu",&s);

				logger(LOG_DEBUG,"main","Dump options address=%u size=%u",a,s);

				if (dev==NULL) rv=ws_open(&dev,vendor,product,0);

				if (dev)
				{
					uint8_t *b;

					logger(LOG_DEBUG,"main","Allocating %u bytes for read buffer",s);
					b=malloc(s);
					if (!b) 
						logger(LOG_ERROR,"main","Could not allocate %u bytes for read buffer",s);
					else
					{
						logger(LOG_DEBUG,"main","Allocated %u bytes for read buffer",s);
						ws_read(dev,a,b,s);
						ws_dump(a,b,s,w);
						free(b);
					}
				}

				if (dev) ws_close(&dev);
				break;
			}

			case 'H':
			{
				help=1;
				printf("Freetz Weather Client (frewe-client) for FRITZ!Box\n");
				printf("Alexey Ozerov (c) 2014 - ver. %s\n\n", PROGRAM_VERSION);
				break;
			}

			case '?':
			case 'h':
				help=1;
				printf("Freetz Weather Client (frewe-client) for FRITZ!Box\n");
				printf("Alexey Ozerov (c) 2014 - ver. %s\n\n", PROGRAM_VERSION);
				printf("Options\n");
				printf(" -? -h            Display this help\n");
				printf(" -a <v>:<p>       Change the vendor:product address of the usb device from the default\n");
				printf(" -A <alt in m>    Change altitude\n");
				printf(" -c <filename>    Read configuration from cfg file\n");
				printf(" -p <pos>         Alter position in weather station log from current position (can be +- value)\n");
				printf(" -v               Verbose output, enable debug and warning messages\n");
				printf(" -d [addr]:[len]  Dump length bytes from address\n");
				printf(" -x               XML output\n");
				printf(" -r <sec>         Run continuosly with given interval in seconds\n");
				printf(" -s <url>         Freetz weather server URL\n");
				printf(" -k <key>         Freetz weather server key\n");
				printf(" -t <type>        Weather Station Type: WH1080 (default) or WH3080\n");
				printf(" -u <url>         Additional URL to submit the data (format like -f)\n");
				printf(" -e <errstr>      Write this errstr if measured value is out of range (e.g. outdoor unit is disconnected)\n");
				printf(" -f <string>      Format output to user defined string\n");
				printf("    %%a - record age\n");
				printf("    %%C - outside wind chill temperature C\n");
				printf("    %%c - outside wind chill temperature F\n");
				printf("    %%D - wind direction - named\n");
				printf("    %%d - wind direction - degrees\n");
				printf("    %%E - outside dew temperature C\n");
				printf("    %%e - outside dew temperature F\n");
				printf("    %%G - wind gust in km/h\n");
				printf("    %%g - wind gust in mph\n");
				printf("    %%h - inside humidity\n");
				printf("    %%H - outside humidity\n");
				printf("    %%I - inside temperature C\n");
				printf("    %%i - inside temperature F\n");
				printf("    %%K - weather station type\n");
				printf("    %%L - relative pressure in hPa\n");
				printf("    %%l - relative pressure in inch\n");
				printf("    %%m - illumination in W/m² (WH3080 only)\n");
				printf("    %%M - illumination in lux (WH3080 only)\n");
				printf("    %%N - date/time string YYYY-MM-DD HH:MM:SS local time\n");
				printf("    %%n - date/time string YYYY-MM-DD HH:MM:SS UTC time\n");
				printf("    %%O - outside temperature C\n");
				printf("    %%o - outside temperature F\n");
				printf("    %%P - absolute pressure in hPa\n");
				printf("    %%p - absolute pressure in inch\n");
				printf("    %%R - rain total from meteostation start in mm\n");
				printf("    %%r - rain total from meteostation start in inch\n");
				printf("    %%S - rain last 60 min in mm\n");
				printf("    %%s - rain last 60 min in inch\n");
				printf("    %%T - rain from 0h local time in mm\n");
				printf("    %%t - rain from 0h local time in inch\n");
				printf("    %%U - UV radiation (WH3080 only)\n");
				printf("    %%v - wind speed in m/s\n");
				printf("    %%W - wind speed in km/h\n");
				printf("    %%w - wind speed in mph\n");
				printf("    %%Y - date string DD.MM.YYYY local time\n");
				printf("    %%y - date/time string YYYYMMDDhhmm local time\n");
				printf("    %%Z - time string HH:MM local time\n");
		}
	}

	if (rv==0 && help==0 && dump==0)
	{

// Set entry size according to device type and create buffers

		if(strcasecmp(ws_type,"WH3080")==0 || strcasecmp(ws_type,"WH3081")==0)
			ws_entry_size=0x14;
		else
			ws_entry_size=0x10;

		uint8_t buffer[ws_entry_size],buffer60[ws_entry_size],buffer0h[ws_entry_size];

// Prepare frewe-server URLs

		if (frewe_server_url!=NULL && frewe_server_key!=NULL)
		{	
			l=strlen(frewe_server_url)+strlen(frewe_server_key);
			
			if (strcasecmp(frewe_server_senddata,"On")==0)
			{	frewe_server_url_submit = malloc(l+strlen(frewe_server_url_submit_template));
				if (!frewe_server_url_submit)
					logger(LOG_ERROR,"main","Could not allocate %u bytes for frewe-server URL",l+strlen(frewe_server_url_submit_template));
				else
					sprintf(frewe_server_url_submit,frewe_server_url_submit_template,frewe_server_url,frewe_server_key);
			}
			if (strcasecmp(frewe_server_resend,"On")==0)
			{	frewe_server_url_lasttime = malloc(l+strlen(frewe_server_url_lasttime_template));
				if (!frewe_server_url_lasttime)
					logger(LOG_ERROR,"main","Could not allocate %u bytes for frewe-server URL",l+strlen(frewe_server_url_lasttime_template));
				else
					sprintf(frewe_server_url_lasttime,frewe_server_url_lasttime_template,frewe_server_url,frewe_server_key);
			}
			if (error_email!=NULL)
			{	frewe_server_url_error = malloc(l+strlen(frewe_server_url_error_template)+strlen(error_email));
				if (!frewe_server_url_error)
					logger(LOG_ERROR,"main","Could not allocate %u bytes for frewe-server URL",l+strlen(frewe_server_url_error_template)+strlen(error_email));
				else
					sprintf(frewe_server_url_error,frewe_server_url_error_template,frewe_server_url,frewe_server_key,error_email);
			}
			if (1)
			{	frewe_server_url_alarm = malloc(l+strlen(frewe_server_url_alarm_template));
				if (!frewe_server_url_alarm)
					logger(LOG_ERROR,"main","Could not allocate %u bytes for frewe-server URL",l+strlen(frewe_server_url_alarm_template));
				else
					sprintf(frewe_server_url_alarm,frewe_server_url_alarm_template,frewe_server_url,frewe_server_key);
			}
		}

// Make a pause for the Fritzbox to set time and connect to internet

		time(&starttime);

		while (starttime<10000)
		{
			logger(LOG_WARNING,"main","Time is still unset: %d, wait 10 secs...", starttime);
			sleep(10);
			time(&starttime);
		}

// Get read period from WS

		rv=ws_open(&dev,vendor,product,0);
		if (rv==0) rv=ws_read(dev,WS_READ_PERIOD_ADDRESS,buffer,1);
		if (rv==0)
		{	read_period=buffer[0];
			logger(LOG_DEBUG,"main","Weather station read period is %d minutes",read_period);
		}
		ws_close(&dev);

		if (rv!=0)
		{	logger(LOG_ERROR,"main","Can't get read period from weather station. Stopped!");
			return rv;
		}

// Start main loop for run_interval repetitions

		w.ok=w1.ok=0;
		read_weather=read_fhem=1;

		do
		{

// Start reading

			rv=0;				// reset errors
			startpos=endpos=position; 	// default

// Read current time, this will be the time for record in position 0

			time(&curtime);
			tmptr=localtime(&curtime);
			if (read_weather)
				gettimeofday(&tlast, NULL);
			if (read_fhem)
				gettimeofday(&tlastfhem, NULL);
			

// Get the current data count (records actually saved on ws)

			if (rv==0)
			{	rv=ws_open(&dev,vendor,product,0);
				if (rv==0) rv=ws_read(dev,WS_DATA_COUNT_ADDRESS,buffer,2);
				if (rv==0)
				{	data_count=buffer[0]+buffer[1]*256;
					if (data_count<0 || data_count>WS_TOTAL_ENTRIES) data_count=WS_TOTAL_ENTRIES;
					logger(LOG_DEBUG,"main","Data count is %d",data_count);
				}
				ws_close(&dev);
			}


// Get last time saved on frewe-server and calculate positions

			if (rv==0 && read_weather && frewe_server_url_lasttime!=NULL)
			{
				logger(LOG_DEBUG,"main","Getting lasttime from server URL: %s", frewe_server_url_lasttime);
				rv=ws_submit(frewe_server_url_lasttime,&filebuf);
				if (rv==0 && strlen(filebuf)>25) rv=1;				// Got some buggy output which can cause SIGSERV in strptime

				if (rv==0 && strncasecmp(filebuf,"Not found",9)==0)	// If lasttime not found try to read all records from WS
				{ 
					startpos=1-data_count;
					endpos=0;
					logger(LOG_INFO,"main","Will now read ALL entries from %d to %d, this will take time...",startpos,endpos);
				}

				else if (rv==0)						// If lasttime found read only newer records
				{ 	
					logger(LOG_DEBUG,"main","Last record datetime is %s",filebuf);
					if (!strptime(filebuf, "%Y-%m-%d %H:%M:%S", &tm)) rv=1;
					if (rv!=0) logger(LOG_ERROR,"main","Failed to convert lasttime from %s", filebuf);
					if (rv==0) 
					{	tm.tm_isdst = -1; // tells mktime() to determine whether daylight saving time is in effect
						lasttime = timegm(&tm);  // mktime assumes the time in tm struct is localtime, but this time it's UTC
						if (lasttime == -1) rv=1;
						if (rv!=0) logger(LOG_ERROR,"main","Failed to get lasttime seconds from %s", filebuf);
					}
					if (rv==0) 
					{	logger(LOG_DEBUG,"main","Lasttime on frewe-server is %d, time gap is %d",lasttime,curtime-lasttime);
						startpos=floor((float)(curtime-lasttime-1)/read_period/60)*-1;  // -1 logical seconds to avoid double submittions
						if (startpos<1-data_count) startpos=1-data_count;
						endpos=0;
						logger(LOG_WARNING,"main","Will now read entries from %d to %d",startpos,endpos);
					}
					else
						rv=0;	// Ignore this error and read the current position
				}
				else
				{	logger(LOG_ERROR,"main","Failed to get lasttime from %s", frewe_server_url_lasttime);
					rv=0; // Ignore this error and get the data only for the current position
				}
			}

// Warn if position doesn't meet a real record

			if (rv==0 && (startpos>0 || startpos<1-data_count || endpos >0 || endpos<1-data_count))
				logger(LOG_INFO,"main","Position is out of available data, %d records are saved on device",data_count);

// Read last record address & age

			if (rv==0)
			{
				rv=ws_open(&dev,vendor,product,0);
				if (rv==0) rv=ws_read(dev,WS_CURRENT_POSITION_ADDRESS,buffer,2);			
				if (rv==0) address=buffer[0]+buffer[1]*256;
				if (rv==0) rv=ws_read(dev,address,buffer,sizeof(buffer));
				if (rv==0) last_age = (int) buffer[0x00];
				if (rv!=0) logger(LOG_ERROR,"main","Can't read last position address or age from WS");
				ws_close(&dev);
			}

// Positions loop

			if (rv==0)
			{
    			for (curpos=startpos;curpos<=endpos;curpos++)	// NB: data errors don't break this loop
    			{
    
    				rv=ws_open(&dev,vendor,product,0);	// rv is reset here
    
// Read record for the current position
    
    				address0=get_address(address,curpos);
    				if (rv==0) rv=ws_read(dev,address0,buffer,sizeof(buffer));
    
// Read record ~60 mins ago (if not existent take first available record)
    
    				if (rv==0)
    				{	
    					pos60 = curpos-round((float)(60-last_age)/read_period)-1;
    					if (0-pos60>=data_count) pos60=1-data_count;
   						address60=get_address(address,pos60);
    				}
    				if (rv==0) rv=ws_read(dev,address60,buffer60,sizeof(buffer60));
    
// Read record from ~0h of the curpos' day (if not existent take first available record)
// The calculation is not accurate when changing daylight saving time
    
    				if (rv==0)
    				{	
    					pos0h = 0-round((float)(tmptr->tm_hour*60+tmptr->tm_min-last_age)/read_period)-1;
    					while (curpos<pos0h) pos0h -= round((float)60*24/read_period);
    					if (0-pos0h>=data_count) pos0h=1-data_count;
   						address0h=get_address(address,pos0h);
    				}
    				if (rv==0) rv=ws_read(dev,address0h,buffer0h,sizeof(buffer0h));
    
// Close USB device anyway
    
    				ws_close(&dev);
    
// Parse the buffers for the weather values into w
    
    				if (rv==0) 
    				{	rv=ws_parse(buffer,buffer60,buffer0h,curtime,curpos,last_age);
    					if (rv==2)
    					{	logger(LOG_ERROR,"main","ws_parse reported negative rain, position=%d, address0=0x%x, address60=0x%x, address0h=0x%x,",curpos,address0,address60,address0h);
    						continue;
    					}
    					
    					if (rv!=0)
    					{	logger(LOG_WARNING,"main","ws_parse reported an error, the record will be ignored");
    						continue;
    					}
    				}
    
// Format and print data
    
    				if (rv==0 && format!=NULL)
    				{	output=malloc(strlen(format)+100);
    					if (!output)
    					{	logger(LOG_ERROR,"main","Could not allocate %u bytes for output",strlen(format)+100);
    						rv=1;
    					}
    					else
    					{	rv=ws_format(format,output,0,"","",errorstring);
    						if (rv!=0)
    							logger(LOG_ERROR,"main","Error formatting data return code %d", rv);
    						else
    						{	printf("%s",output);
    							fflush(stdout);
    						}
    						free(output);
    					}
    				}

 
// Format and submit data to frewe-server
    
    				if (rv==0 && read_weather && frewe_server_url_submit!=NULL) 
    				{	output=malloc(strlen(frewe_server_url_submit)+100);
    					if (!output)
    					{	logger(LOG_ERROR,"main","Could not allocate %u bytes for output",strlen(frewe_server_url_submit)+100);
    						rv=1;
    					}
    					else
    					{	rv=ws_format(frewe_server_url_submit,output,1,"","","");
    						if (rv!=0) 
    							logger(LOG_ERROR,"main","Error formatting data return code %d", rv);
    						else
    						{	logger(LOG_DEBUG,"main","Submitting to server URL: %s", output);
    							rv=ws_submit(output,&filebuf);

        					if (rv!=0 || strncasecmp(filebuf,"OK",2)!=0) 
        					{	logger(LOG_ERROR,"main","Error submitting to frewe-server, check FreweServerURL");
        						rv=0; // Ignore this error, don's stop

/*
        						if (curpos<endpos)
        						{ 	curpos=endpos-1; // Stop processing other stuff and goto last position if frewe-server fails, TODO: good so?
        							free(output);
        							continue;
        						}
*/		        						
        					}
        				}

    						free(output);
    					}
   					
    				}

// Check alarm thresholds and make alarm actions (Get/Run)
// NB: Alarms will be done even when resending data

						if (w.ok && w1.ok && rv==0)
						{
							for(i=0;i<alm_counter;i++)
							{	if (alm[i].url==NULL && alm[i].run==NULL && alm[i].email==NULL) continue;
								
								if(strcasecmp(alm[i].type, "HighOutdoorTemp")==0 && w.tempout>=alm[i].threshold && w1.tempout<alm[i].threshold) ws_alarm (&w,&alm[i]);
								if(strcasecmp(alm[i].type, "LowOutdoorTemp")==0 && w.tempout<=alm[i].threshold && w1.tempout>alm[i].threshold) ws_alarm (&w,&alm[i]);
								if(strcasecmp(alm[i].type, "HighWindchillTemp")==0 && w.tempchill>=alm[i].threshold && w1.tempchill<alm[i].threshold) ws_alarm (&w,&alm[i]);
								if(strcasecmp(alm[i].type, "LowWindchillTemp")==0 && w.tempchill<=alm[i].threshold && w1.tempchill>alm[i].threshold) ws_alarm (&w,&alm[i]);							
								if(strcasecmp(alm[i].type, "HighDewTemp")==0 && w.tempdew>=alm[i].threshold && w1.tempdew<alm[i].threshold) ws_alarm (&w,&alm[i]);
								if(strcasecmp(alm[i].type, "LowDewTemp")==0 && w.tempdew<=alm[i].threshold && w1.tempdew>alm[i].threshold) ws_alarm (&w,&alm[i]);
								if(strcasecmp(alm[i].type, "HighIndoorTemp")==0 && w.tempin>=alm[i].threshold && w1.tempin<alm[i].threshold) ws_alarm (&w,&alm[i]);
								if(strcasecmp(alm[i].type, "LowIndoorTemp")==0 && w.tempin<=alm[i].threshold && w1.tempin>alm[i].threshold) ws_alarm (&w,&alm[i]);
								if(strcasecmp(alm[i].type, "HighOutdoorHumidity")==0 && w.humout>=alm[i].threshold && w1.humout<alm[i].threshold) ws_alarm (&w,&alm[i]);
								if(strcasecmp(alm[i].type, "LowOutdoorHumidity")==0 && w.humout<=alm[i].threshold && w1.humout>alm[i].threshold) ws_alarm (&w,&alm[i]);
								if(strcasecmp(alm[i].type, "HighIndoorHumidity")==0 && w.humin>=alm[i].threshold && w1.humin<alm[i].threshold) ws_alarm (&w,&alm[i]);
								if(strcasecmp(alm[i].type, "LowIndoorHumidity")==0 && w.humin<=alm[i].threshold && w1.humin>alm[i].threshold) ws_alarm (&w,&alm[i]);
								if(strcasecmp(alm[i].type, "HighRelPressure")==0 && w.pressrel>=alm[i].threshold && w1.pressrel<alm[i].threshold) ws_alarm (&w,&alm[i]);
								if(strcasecmp(alm[i].type, "LowRelPressure")==0 && w.pressrel<=alm[i].threshold && w1.pressrel>alm[i].threshold) ws_alarm (&w,&alm[i]);
								if(strcasecmp(alm[i].type, "HighWind")==0 && w.windspeed>=alm[i].threshold && w1.windspeed<alm[i].threshold) ws_alarm (&w,&alm[i]);
								if(strcasecmp(alm[i].type, "LowWind")==0 && w.windspeed<=alm[i].threshold && w1.windspeed>alm[i].threshold) ws_alarm (&w,&alm[i]);
								if(strcasecmp(alm[i].type, "HighGust")==0 && w.windgust>=alm[i].threshold && w1.windgust<alm[i].threshold) ws_alarm (&w,&alm[i]);
								if(strcasecmp(alm[i].type, "LowGust")==0 && w.windgust<=alm[i].threshold && w1.windgust>alm[i].threshold) ws_alarm (&w,&alm[i]);
								if(strcasecmp(alm[i].type, "HighRainHour")==0 && w.rainhour>=alm[i].threshold && w1.rainhour<alm[i].threshold) ws_alarm (&w,&alm[i]);
								if(strcasecmp(alm[i].type, "LowRainHour")==0 && w.rainhour<=alm[i].threshold && w1.rainhour>alm[i].threshold) ws_alarm (&w,&alm[i]);						
								if(strcasecmp(alm[i].type, "HighRainDay")==0 && w.rainday>=alm[i].threshold && w1.rainday<alm[i].threshold) ws_alarm (&w,&alm[i]);
								if(strcasecmp(alm[i].type, "LowRainDay")==0 && w.rainday<=alm[i].threshold && w1.rainday>alm[i].threshold) ws_alarm (&w,&alm[i]);
								if(strcasecmp(alm[i].type, "HighIllumination")==0 && w.illu>=alm[i].threshold && w1.illu<alm[i].threshold) ws_alarm (&w,&alm[i]);
								if(strcasecmp(alm[i].type, "LowIllumination")==0 && w.illu<=alm[i].threshold && w1.illu>alm[i].threshold) ws_alarm (&w,&alm[i]);						
								if(strcasecmp(alm[i].type, "HighUV")==0 && w.uv>=alm[i].threshold && w1.uv<alm[i].threshold) ws_alarm (&w,&alm[i]);
								if(strcasecmp(alm[i].type, "LowUV")==0 && w.uv<=alm[i].threshold && w1.uv>alm[i].threshold) ws_alarm (&w,&alm[i]);
							}
						}

// Format and submit data to known weather services
    
      			for (i=0;i<sizeof(ws)/sizeof(ws[0]) && read_weather && rv==0;i++)
      			{	
      				if (ws[i].user==NULL || ws[i].pass==NULL) continue;	// Skip if service is not in use
      					
      				if (!ws[i].resend && curpos!=endpos) continue;		// Skip if service doesn't support data resend
      				
    				 	l = strlen(ws[i].url)+100+strlen(ws[i].user);
    					if (ws[i].md5==1) l+=MD5_DIGEST_LENGTH; else l+=strlen(ws[i].pass);
    					
    					output=malloc(l);
    					if (!output)
    					{	logger(LOG_ERROR,"main","Could not allocate %d bytes for output",l);
    						rv=1;
    					}
    					else
    					{
    						if (ws[i].md5==1)
    						{	MD5(ws[i].pass, strlen(ws[i].pass), md5);
    							sprintf(md5str, "%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x", md5[0],md5[1],md5[2],md5[3],md5[4],md5[5],md5[6],md5[7], md5[8],md5[9],md5[10],md5[11],md5[12],md5[13],md5[14],md5[15]);
    						}
    
    						rv=ws_format(ws[i].url,output,1,ws[i].user,ws[i].md5==1? md5str : ws[i].pass, ws[i].error);
    						if (rv!=0) 
    							logger(LOG_ERROR,"main","Error formatting data return code %d", rv);
    						else
    						{	logger(LOG_DEBUG,"main","Submitting to server URL: %s", output);
    							rv=ws_submit(output,&filebuf); 
    							// NB: Error in ws_submit will be ignored, just put warning, don't stop
    							if (rv!=0) 
    							{	logger(LOG_WARNING,"main","Submitting to server %s failed", output);
    								rv=0;
    							}
    						}
    						free(output);
    					}
      			}

// Save the previous record to w1
      			
      			w1=w;

    			}

// Position loop ends here


// NB: only last position (endpos) record will be put to fhem.txt and submitted to additional URLs        
    
// Format and print data for FHEM into FHEM_file
    
  				if (rv==0 && read_fhem && FHEM_format!=NULL && FHEM_file!=NULL)
  				{	output=malloc(strlen(FHEM_format)+100);
  					if (!output)
  					{	logger(LOG_ERROR,"main","Could not allocate %u bytes for FHEM output",strlen(FHEM_format)+100);
  						rv=1;
  					}
  					else
  					{	rv=ws_format(FHEM_format,output,0,"","",FHEM_errorstring);
  						if (rv!=0)
  							logger(LOG_ERROR,"main","Error FHEM formatting data return code %d", rv);
  						else
  						{	fd = fopen (FHEM_file, "w");
  							if (fd == NULL)
  								logger(LOG_ERROR,"main","Error opening FHEM_File %s for writing", FHEM_file);
  							else
  							{ logger(LOG_DEBUG,"main","Writing to FHEM file %s", FHEM_file);
  								fprintf(fd,"%s",output);
  								fclose(fd);
  							}
  						}
  						free(output);
  					}
  				}

    
// Format and submit data to additional URLs according to -u or WeatherURL cfg
    
    			for (i=0;i<add_url_counter && read_weather && rv==0;i++)
    			{
    				if (add_url[i]!=NULL)
    				{	output=malloc(strlen(add_url[i])+100);
    					if (!output)
    					{	logger(LOG_ERROR,"main","Could not allocate %u bytes for output",strlen(add_url[i])+100);
    						rv=1;
    					}
    					else
    					{	rv=ws_format(add_url[i],output,1,"","","");
    						if (rv!=0)
    							logger(LOG_ERROR,"main","Error formatting data return code %d", rv);
    						else
    						{	logger(LOG_DEBUG,"main","Submitting to additional URL: %s", output);
    							rv=ws_submit(output,&filebuf); 
    							// NB: Error in ws_submit will be ignored, just warning
    							if (rv!=0) 
    							{	logger(LOG_WARNING,"main","Submitting to server %s failed", output);
    								rv=0;
    							}
    						}
					free(output);
    					}
    				}
    			}
			}

// Make a pause

			if (run_interval>0)
			{	
				gettimeofday(&tact, NULL);
				
				while (run_interval*1000000 > diff_time(&tact, &tlast) && fhem_interval*1000000 > diff_time(&tact, &tlastfhem))
				{	logger(LOG_DEBUG,"main","Sleeping a second prior to the next timers check");
					sleep(1);
					gettimeofday(&tact, NULL);
				}
					
			  read_weather=read_fhem=0;
			  
				if (run_interval*1000000 <= diff_time(&tact, &tlast))
					read_weather=1;
			  if (fhem_interval*1000000 <= diff_time(&tact, &tlastfhem))
			  	read_fhem=1;
				
			}
			
		} while (run_interval>0);

	}

	return rv;
}

//***************************************************************
// Read configuration from the cfg file
//***************************************************************

struct cfgvar
{	char *key;
	char *type;
	void *value;
} cfgvar[] =
{	{"StationType","%s",&ws_type},
	{"Altitude","%d",&altitude},
	{"RunInterval","%d",&run_interval},
	{"TempInFactor","%f",&c.tempin_factor},
	{"TempInOffset","%f",&c.tempin_offset},
	{"TempOutFactor","%f",&c.tempout_factor},
	{"TempOutOffset","%f",&c.tempout_offset},
	{"HumidityInFactor","%f",&c.humin_factor},
	{"HumidityInOffset","%f",&c.humin_offset},
	{"HumidityOutFactor","%f",&c.humout_factor},
	{"HumidityOutOffset","%f",&c.humout_offset},
	{"PressAbsFactor","%f",&c.pressabs_factor},
	{"PressAbsOffset","%f",&c.pressabs_offset},
	{"WindspeedFactor","%f",&c.windspeed_factor},
	{"WindspeedOffset","%f",&c.windspeed_offset},
	{"WindgustFactor","%f",&c.windspeed_factor},
	{"WindgustOffset","%f",&c.windspeed_offset},
	{"RainFactor","%f",&c.rain_factor},
	{"RainOffset","%f",&c.rain_offset},
	{"WinddirOffset","%f",&c.winddir_offset},
	{"IlluminationFactor","%f",&c.illu_factor},
	{"IlluminationOffset","%f",&c.illu_offset},
	{"UVFactor","%f",&c.uv_factor},
	{"UVOffset","%f",&c.uv_offset},
	{"OutputFormat","%s",&format},
	{"ErrorString","%s",&errorstring},
	{"FHEM_OutputFormat","%s",&FHEM_format},
	{"FHEM_ErrorString","%s",&FHEM_errorstring},
	{"FHEM_File","%s",&FHEM_file},
	{"FreweServer_URL","%s",&frewe_server_url},
	{"FreweServer_Key","%s",&frewe_server_key},
	{"FreweServer_SendData","%s",&frewe_server_senddata},
	{"FreweServer_Resend","%s",&frewe_server_resend},
	{"Error_Email","%s",&error_email}
};

int read_cfg(char *fname)
{
	FILE	*fp;
	char	temp[1024], *key, *value, keyfound, advkey[100];
	int 	i;


	if( ( fp = fopen( fname, "r" ) ) == NULL )
	{	logger(LOG_ERROR,"read_cfg","Could not open cfg file %s",fname);
		return 1;
	}

	while( fgets( temp, 1024, fp ) != 0 )
	{

// Skip empty and comment lines

		if( (temp[0] == '\n') || (temp[0] == '#') || (temp[0] == '\r' && temp[1] == '\n')) continue;

// Separate key and value from the input line

		int p = strcspn(temp, " \t\n\r");				// Find the first occurance of spaces and replace them with \0
		if (p>0) temp[p]='\0'; 
		else continue;

		key = temp;
		value = temp + p + 1;

		while (*value=='\t' || *value=='\n' || *value=='\r' || *value==' ') value++;	// Skip further spaces and remove the trailing \n or \r
		if (strlen(value)>0 && value[strlen(value)-1]=='\n') value[strlen(value)-1]='\0';
		if (strlen(value)>0 && value[strlen(value)-1]=='\r') value[strlen(value)-1]='\0';


// Look for different cfgvar keys and save the values

		keyfound=0;

		for(i=0;i<sizeof(cfgvar)/sizeof(cfgvar[0]);i++)
		{	if(strcasecmp(cfgvar[i].key, key) == 0)
			{	if (strcasecmp(cfgvar[i].type,"%s")==0)
				{	*(char **)(cfgvar[i].value)=malloc(strlen(value)+1);
					if (!*(char **)(cfgvar[i].value))
						logger(LOG_WARNING,"read_cfg","Could not allocate memory for cfg string %s",value);
					else
					{	strcpy(*(char **)(cfgvar[i].value), value);
						logger(LOG_DEBUG,"read_cfg","Key '%s' is set to '%s'",key,value);
					}

				}
				else
				{ 	sscanf(value,cfgvar[i].type,cfgvar[i].value);
					logger(LOG_DEBUG,"read_cfg","Key '%s' is set to '%s'",key,value);
				}
				keyfound++;
				break;
			}
		}

// Look for weather service key

		for(i=0;i<sizeof(ws)/sizeof(ws[0]);i++)
		{	if(strcasecmp(ws[i].userkey, key) == 0)
			{	ws[i].user = malloc(strlen(value)+1);
				if (!ws[i].user)
					logger(LOG_WARNING,"read_cfg","Could not allocate memory for cfg string %s",value);
				else
				{	strcpy(ws[i].user,value);
					logger(LOG_DEBUG,"read_cfg","WS key '%s' is set to '%s'",key,value);
				}
				keyfound++;
				break;
			}
			if(strcasecmp(ws[i].passkey, key) == 0)
			{	ws[i].pass = malloc(strlen(value)+1);
				if (!ws[i].pass)
					logger(LOG_WARNING,"read_cfg","Could not allocate memory for cfg string %s",value);
				else
				{	strcpy(ws[i].pass,value);
					logger(LOG_DEBUG,"read_cfg","WS key '%s' is set to '%s'",key,value);
				}
				keyfound++;
				break;
			}
		}

// Look for alarm keys

		for(i=0;i<sizeof(walarm_type)/sizeof(walarm_type[0]);i++)
		{	
			if(strcasecmp(walarm_type[i], key) == 0)
			{	if (alm_counter<MAX_ALARMS)
        			{ 	sscanf(value,"%f",&alm[alm_counter].threshold);
        				alm[alm_counter].type=walarm_type[i];
        				alm[alm_counter].url=NULL;
        				alm[alm_counter].run=NULL;
        				alm[alm_counter].email=NULL;
        				logger(LOG_DEBUG,"read_cfg","Alarm key '%s' is set to '%s'",key,value);
        				alm_counter++;
        				keyfound++;
        				break;
        			}
        			else
        				logger(LOG_WARNING,"read_cfg","Too many alarms defined, ignored %s=%s",key,value);
        		}
		}


// Look for Alarm_Get, Alarm_Run, Alarm_Email
			

		if(strcasecmp("Alarm_Get", key) == 0)
		{	
			if (alm_counter>0)
			{	if (alm[alm_counter-1].url==NULL)
				{
					alm[alm_counter-1].url = malloc(strlen(value)+1);
					if (!alm[alm_counter-1].url)
						logger(LOG_WARNING,"read_cfg","Could not allocate memory for cfg string %s",value);
					else
					{	strcpy(alm[alm_counter-1].url,value);
						logger(LOG_DEBUG,"read_cfg","Alarm URL '%s' is set for Alarm type '%s'",value,alm[alm_counter-1].type);
					}
				}
				else
					logger(LOG_WARNING,"read_cfg","Alarm URL already defined, ignore %s=%s",key,value);
			}
			else
				logger(LOG_WARNING,"read_cfg","Alarm URL without alarm ignored %s=%s",key,value);
			keyfound=1;
		}

		if(strcasecmp("Alarm_Run", key) == 0)
		{	
			if (alm_counter>0)
			{	if (alm[alm_counter-1].run==NULL)
				{
					alm[alm_counter-1].run = malloc(strlen(value)+1);
					if (!alm[alm_counter-1].run)
						logger(LOG_WARNING,"read_cfg","Could not allocate memory for cfg string %s",value);
					else
					{	strcpy(alm[alm_counter-1].run,value);
						logger(LOG_DEBUG,"read_cfg","Alarm Command '%s' is set for Alarm type '%s'",value,alm[alm_counter-1].type);
					}
				}
				else
					logger(LOG_WARNING,"read_cfg","Alarm Command already defined, ignored %s=%s",key,value);
			}
			else
				logger(LOG_WARNING,"read_cfg","Alarm Command without alarm ignored %s=%s",key,value);
			keyfound=1;
		}

		if(strcasecmp("Alarm_Email", key) == 0)
		{	
			if (alm_counter>0)
			{	if (alm[alm_counter-1].email==NULL)
				{
					alm[alm_counter-1].email = malloc(strlen(value)+1);
					if (!alm[alm_counter-1].email)
						logger(LOG_WARNING,"read_cfg","Could not allocate memory for cfg string %s",value);
					else
					{	strcpy(alm[alm_counter-1].email,value);
						logger(LOG_DEBUG,"read_cfg","Alarm eMail '%s' is set for Alarm type '%s'",value,alm[alm_counter-1].type);
					}
				}
				else
					logger(LOG_WARNING,"read_cfg","Alarm eMail already defined, ignored %s=%s",key,value);
			}
			else
				logger(LOG_WARNING,"read_cfg","Alarm eMail without alarm ignored %s=%s",key,value);
			keyfound=1;
		}


// Look for WeatherURL keys

		if(strcasecmp("WeatherURL", key) == 0)
		{	if (add_url_counter<MAX_ADD_URLS)
			{ 	add_url[add_url_counter] = malloc(strlen(value)+1);
				if (!add_url[add_url_counter]) 
					logger(LOG_WARNING,"read_cfg","Could not allocate memory for cfg value %s",value);
				else
				{	strcpy(add_url[add_url_counter], value);
					logger(LOG_DEBUG,"read_cfg","Weather URL '%s' added",add_url[add_url_counter]);
					add_url_counter++;
				}
			}
			else
				logger(LOG_WARNING,"read_cfg","Too many Weather URLs defined, ignore %s",value);
			keyfound=1;
		}

// If key is unknown just put a warning, nothing else

		if (!keyfound)
		{	logger(LOG_WARNING,"read_cfg","Unknown cfg key '%s' skipped",key);
		}

	}
 
	fclose(fp); 
	return 0;
} 

//***************************************************************
// Handle USB device
//***************************************************************

int ws_open(usb_dev_handle **dev,uint16_t vendor,uint16_t product,int reset_done)
{
	int rv;
	struct usb_bus *bus;

	rv=0;
	*dev=NULL;

	logger(LOG_DEBUG,"ws_open","Initialise usb");
	usb_init();
	usb_set_debug(0);
	usb_find_busses();
	usb_find_devices();

	logger(LOG_DEBUG,"ws_open","Scan for device %04X:%04X",vendor,product);
	for (bus=usb_get_busses(); bus && *dev==NULL; bus=bus->next)
	{
		struct usb_device *device;

		for (device=bus->devices; device && *dev==NULL; device=device->next)
		{
			if (device->descriptor.idVendor == vendor
				&& device->descriptor.idProduct == product)
			{
				logger(LOG_DEBUG,"ws_open","Found device %04X:%04X",vendor,product);
				*dev=usb_open(device);
			}
		}
	}

	if (rv==0 && *dev)
	{
		char buf[100];

		if (usb_get_driver_np(*dev,0,buf,sizeof(buf))==0)
		{	logger(LOG_WARNING,"ws_open","Interface 0 already claimed by driver \"%s\", attempting to detach it", buf);
			rv=usb_detach_kernel_driver_np(*dev,0);
			if (rv!=0) logger(LOG_ERROR,"ws_open","Error detaching kernel driver return code %d", rv);
		}

		if (rv==0)
		{	rv=usb_claim_interface(*dev,0);
			if (rv!=0) logger(LOG_ERROR,"ws_open","Error claiming device return code %d", rv);
		}

		if (rv==0)
		{	rv=usb_set_altinterface(*dev,0);		// Sometimes error -62 occures here, although the device is attached
			if (rv==-62 && !reset_done)
			{	logger(LOG_ERROR,"ws_open","Error setting alt interface return code %d, trying to reset the USB device", rv);
				rv=usb_reset(*dev);
				if (rv!=0)
					logger(LOG_ERROR,"ws_open","Error resetting USB device return code %d", rv);
				else
				{	
					rv=usb_close(*dev);		// Close, re-enumerate and reopen the USB device after reset
					rv=ws_open(dev,vendor,product,1);
					return rv;
					
				}
			}
			else if (rv!=0) logger(LOG_ERROR,"ws_open","Error setting alt interface return code %d", rv);
		}
	}
	else
	{
		logger(LOG_ERROR,"ws_open","Device %04X:%04X not found",vendor,product);
		rv=1;
	}

	if (rv==0) logger(LOG_DEBUG,"ws_open","Device %04X:%04X opened",vendor,product);

	return rv;
}

int ws_close(usb_dev_handle **dev)
{
	int rv;

	if (*dev)
	{
		rv=usb_release_interface(*dev, 0);
		if (rv!=0) logger(LOG_ERROR,"ws_close","Could not release interface, return code %d", rv);

		rv=usb_close(*dev);
		if (rv!=0) logger(LOG_ERROR,"ws_close","Error closing interface, return code %d", rv);

		*dev=NULL;
	}

	if (rv==0) logger(LOG_DEBUG,"ws_close","USB device released and closed");

	return rv;
}

int ws_read(usb_dev_handle *dev,uint16_t address,uint8_t *data,uint16_t size)
{
	uint16_t i,c;
	int rv;
	uint8_t s,tmp[0x20],tmp2[0x20];

	memset(data,0,size);

	logger(LOG_DEBUG,"ws_read","Reading %d bytes from 0x%04X",size,address);

	i=0;
	c=sizeof(tmp);
	s=size-i<c?size-i:c;

	for (;i<size;i+=s, s=size-i<c?size-i:c)
	{
		uint16_t a;
		char cmd[9],try;

		a=address+i;
		sprintf(cmd,"\xA1%c%c%c\xA1%c%c%c",a>>8,a,c,a>>8,a,c);

		try=0;

		do
		{
        		logger(LOG_DEBUG,"ws_read","Send read command: Addr=0x%04X Size=%u",a,s);
        		rv=usb_control_msg(dev,USB_TYPE_CLASS+USB_RECIP_INTERFACE,9,0x200,0,cmd,sizeof(cmd)-1,1000);
        		logger(LOG_DEBUG,"ws_read","Sent %d of %d bytes",rv,sizeof(cmd)-1); 
        		rv=usb_interrupt_read(dev,0x81,tmp,c,1000);
        		logger(LOG_DEBUG,"ws_read","Read %d of %d bytes",rv,c); 
        		if (rv!=c)
        		{	if (try>3)
        			{	if (rv<0)
        					logger(LOG_ERROR,"ws_read","Error %d while reading from USB device",rv); 
        				else
        					logger(LOG_ERROR,"ws_read","Read only %d of %d bytes",rv,c); 
        				return 1;
        			}
        			else
        			{	try++;
        				continue;
        			}
        		}
        		
        		if (try>0 && memcmp(tmp, tmp2, sizeof(tmp))==0) break;
        		else
        		{	memcpy(tmp2,tmp,sizeof(tmp));
        			try++;
        			if (try>3)
        			{	logger(LOG_ERROR,"ws_read","Couldn't read the same %d bytes after 3 attempts",c);
        				return 1;
        			}
        		}
        		
        	}
        	while (1);

		memcpy(data+i,tmp,s);
	}

	return 0;
}

/*
int ws_reset(usb_dev_handle *dev)
{
	printf("Resetting WetterStation history\n");

	usb_control_msg(dev,USB_TYPE_CLASS+USB_RECIP_INTERFACE,9,0x200,0,"\xA0\x00\x00\x20\xA0\x00\x00\x20",8,1000);
	usb_control_msg(dev,USB_TYPE_CLASS+USB_RECIP_INTERFACE,9,0x200,0,"\x55\x55\xAA\xFF\xFF\xFF\xFF\xFF",8,1000);
	//_send_usb_msg("\xa0","\x00","\x00","\x20","\xa0","\x00","\x00","\x20");
	//_send_usb_msg("\x55","\x55","\xaa","\xff","\xff","\xff","\xff","\xff");
	usleep(28*1000);

	usb_control_msg(dev,USB_TYPE_CLASS+USB_RECIP_INTERFACE,9,0x200,0,"\xFF\xFF\xFF\xFF\xFF\xFF\xFF\xFF",8,1000);
	//_send_usb_msg("\xff","\xff","\xff","\xff","\xff","\xff","\xff","\xff");
	usleep(28*1000);

	//_send_usb_msg("\x05","\x20","\x01","\x38","\x11","\x00","\x00","\x00");
	usb_control_msg(dev,USB_TYPE_CLASS+USB_RECIP_INTERFACE,9,0x200,0,"\x05\x20\x01\x38\x11\x00\x00\x00",8,1000);
	usleep(28*1000);

	//_send_usb_msg("\x00","\x00","\xaa","\x00","\x00","\x00","\x20","\x3e");
	usb_control_msg(dev,USB_TYPE_CLASS+USB_RECIP_INTERFACE,9,0x200,0,"\x00\x00\xAA\x00\x00\x00\x20\x3E",8,1000);
	usleep(28*1000);

	return 0;
}
*/

//***************************************************************
// Parse, format and submit weather values
//***************************************************************

// Unit conversion functions

float c2f(float deg)
{ return 1.8*deg+32;
}

float kmh2mph(float speed)
{ return speed*0.621371192;
}

float kmh2ms(float speed)
{ return speed / 3.6;
}

float hpa2in(float press)
{ return press*0.0295300586467;
}

float mm2in(float size)
{ return size*0.0393700787;
}

// There is no single conversion factor between lx and W/m2; there is a different conversion factor for every wavelength
// and it is not possible to make a conversion unless one knows the spectral composition of the light.

float lux2wattm2(float lux)
{ return lux*1.4641/1000;
}

// Parse memory buffer and fill the wrecord static structure w with all weather values

int ws_parse(uint8_t *buffer, uint8_t *buffer60, uint8_t *buffer0h, time_t curtime, int position, int last_age)
{
	char *dir[]=
	{
		"N","NNE","NE","ENE","E","ESE","SE","SSE",
		"S","SSW","SW","WSW","W","WNW","NW","NNW"
	};
	short dirdeg[]=
	{
		0,23,45,68,90,113,135,158,
		180,203,225,248,270,293,315,338
	};
	char errcount=0, sensorlost=0;
	float lastrain;
	short tempi,tempo;

// Age of the record (in minutes)

	w.age=buffer[0x00];

	if (w.age>read_period+1)
	{	logger(LOG_ERROR,"ws_parse","Age of record %d is not reasonable bigger than read_period %d",w.age,read_period);
		errcount++;
	}

// Datetime

	if (position==0)
		w.datetime=curtime;
	else
		w.datetime=curtime-last_age*60+(position+1)*read_period*60;		// This is not very accurate as age can vary +-1 min for each record

// Check loss of sensors

	if (buffer[0x0F] & 64)
	{	logger(LOG_ERROR,"ws_parse","Sensor contact lost");
		sensorlost=1;
	}

// Inside Temperature (°C)

	if (buffer[0x03] >= 0x80) tempi=buffer[0x02]+(buffer[0x03]<<8) ^ 0x7FFF;	//weather station uses top bit for sign and not normal
                           else   tempi=buffer[0x02]+(buffer[0x03]<<8) ^ 0x0000;	//signed short, so we need to correct this with xor
	w.tempin =(float)(tempi)/10*c.tempin_factor+c.tempin_offset;

	if ((w.tempin > 100) || (w.tempin < -100)) 
	{	logger(LOG_ERROR,"ws_parse","Temperature inside out of range: %f C",w.tempin);
		errcount++;
	}

// Outside Temperature (°C)

	if (!sensorlost)
	{
		if (buffer[0x06] >= 0x80) tempo=buffer[0x05]+(buffer[0x06]<<8) ^ 0x7FFF;	//weather station uses top bit for sign and not normal
	                           else   tempo=buffer[0x05]+(buffer[0x06]<<8) ^ 0x0000;	//signed short, so we need to correct this with xor
		w.tempout=(float)(tempo)/10*c.tempout_factor+c.tempout_offset;
	
		if ((w.tempout > 100) || (w.tempout < -100))
		{	logger(LOG_ERROR,"ws_parse","Temperature outside out of range: %f C",w.tempout);
			errcount++;
		}
	}
	else
	{	w.tempout = 255; 								// 255 means bad value
	}


// Inside Humidity (%)

	w.humin = floor((float)buffer[0x01]*c.humin_factor+c.humin_offset);
	if ((w.humin > 100) || (w.humin == 0)) 
	{	logger(LOG_ERROR,"ws_parse","Humidity inside out of range: %d %%",w.humin);
		errcount++;
	}

// Outside Humidity (%)

	if (!sensorlost)
	{	w.humout = floor((float)buffer[0x04]*c.humout_factor+c.humout_offset);
		if ((w.humout > 100) || (w.humout == 0)) 
		{	logger(LOG_ERROR,"ws_parse","Humidity outside out of range: %d %%",w.humout);
			errcount++;
		}
	}
	else
		w.humout=255;

// Dew point (°C)

	if (w.tempout<100 && w.tempout>-100 && w.humout <= 100 && w.humout>0)
	{	float gama = (17.271*w.tempout)/(237.7+w.tempout) + log ((w.humout==0)?0.001:(float)w.humout/100);		//gama=aT/(b+T) + ln (RH/100)
		w.tempdew = (237.7 * gama) / (17.271 - gama);									//Tdew= (b * gama) / (a - gama)
	}
	else
	{	w.tempdew = 255;
	}

// Wind speed (km/h)

	if (sensorlost || buffer[0x09]==255)
	{	w.windspeed=-1.0;

		if (!sensorlost)
		{	logger(LOG_ERROR,"ws_parse","Invalid windspeed: %f km/h",w.windspeed);
			errcount++;
		}
	}
	else
	{	w.windspeed=(float)(buffer[0x09])/10*3.6*c.windspeed_factor+c.windspeed_offset;
	}
	

// Wind gust (km/h)

       if (sensorlost || buffer[0x0A]==255)
	{	w.windgust=-1.0;
		
		if (!sensorlost)
		{	logger(LOG_ERROR,"ws_parse","Invalid windgust: %f km/h",w.windgust);
			errcount++;
		}
	}
	else
	{      w.windgust=(float)(buffer[0x0A])/10*3.6*c.windgust_factor+c.windgust_offset;
	}

// Windchill temperature (°C)

	if (w.tempout<100 && w.tempout>-100 && w.windspeed!=-1)
	{	if (w.tempout<10.0)
			w.tempchill=13.12 + 0.6215 * w.tempout - 11.37*pow(w.windspeed,0.16) + 0.3965*w.tempout*pow(w.windspeed,0.16);
		else
			w.tempchill=w.tempout;
		if(w.tempout<w.tempchill) w.tempchill=w.tempout; 				// windchill can't be more than tempout
	}
	else
	{	w.tempchill=255;
	}

// Wind direction - named

	if (!sensorlost)
		strcpy (w.winddir,dir[buffer[0x0C]<sizeof(dir)/sizeof(dir[0])?buffer[0x0C]:0]);
	else
		strcpy (w.winddir,"ERR");

// Wind direction - degrees

	if (!sensorlost)
	{	w.winddeg=dirdeg[buffer[0x0C]<sizeof(dir)/sizeof(dir[0])?buffer[0x0C]:0]+c.winddir_offset;
		if (w.winddeg<0) w.winddeg+=360;
		if (w.winddeg>=360) w.winddeg-=360;
	}
	else
		w.winddeg=-1;

// Absolute pressure (hPa)

	w.pressabs = (float)(buffer[0x07]+(buffer[0x08]<<8))/10*c.pressabs_factor+c.pressabs_offset;

	if (w.pressabs < 900 || w.pressabs>1100)
	{	logger(LOG_ERROR,"ws_parse","Pressure out of range: %f hPa",w.pressabs);
		errcount++;
	}

// Relative pressure (hPa)

	if (w.pressabs > 900 && w.pressabs<1100 && w.tempout<100 && w.tempout>-100)
	{	float m=altitude / (18429.1 + 67.53 * w.tempout + 0.003 * altitude); 			// Power exponent to correction function
		w.pressrel=w.pressabs * pow(10,m);
	}
	else
	{	w.pressrel=-1;
	}

// Rain total (mm)

	w.rain = (float)(buffer[0x0D]+(buffer[0x0E]<<8))*0.3*c.rain_factor+c.rain_offset;

// Rain last 60 mins (mm) - NB: last rain is set even if sensors were lost

	lastrain = (float)(buffer60[0x0D]+(buffer60[0x0E]<<8))*0.3*c.rain_factor+c.rain_offset;
	w.rainhour = w.rain - lastrain;
	if (w.rainhour<0 || w.rainhour>50)
	{	logger(LOG_ERROR,"ws_parse","Rainhour is out of range, rain=%f, lastrain=%f",w.rain,lastrain);
		w.rainhour=-1;
		errcount++;

// TEST: Drop the record with negative rain (something strange happens here)

		w.ok=0;
		return 2;
	}


// Rain from 0h (mm) - NB: last rain is set even if sensors were lost

	lastrain = (float)(buffer0h[0x0D]+(buffer0h[0x0E]<<8))*0.3*c.rain_factor+c.rain_offset;
	w.rainday = w.rain - lastrain;
	if (w.rainday<0 || w.rainday>100)
	{	logger(LOG_ERROR,"ws_parse","Rainday is out of range rain=%f, lastrain=%f",w.rain,lastrain);
		w.rainday=-1;
		errcount++;

// TEST: Drop the record with negative rain (something strange happens here)

		w.ok=0;
		return 2;
	}

// All rain stuff is probably invalid if sensors are lost (even if values were read)

	if (sensorlost)
	{	w.rain = -1;
		w.rainhour = -1;
		w.rainday = -1;
	}

// UV & Illumination (WH3080 only)

	if(strcasecmp(ws_type,"WH3080")==0 || strcasecmp(ws_type,"WH3081")==0)
	{	
		if (!sensorlost)
		{	w.uv = floor((float)buffer[19]*c.uv_factor+c.uv_offset);
 			w.illu = (float)(buffer[16]+(buffer[17]<<8)+(buffer[18]<<16))*0.1*c.illu_factor+c.illu_offset;
 		}
 		else
 		{	w.uv=-1.0;
			w.illu=-1.0;
 		}
	}
	else
	{	w.uv=-1.0;
		w.illu=-1.0;
	}
	

// Check if values are reasonable...

	if (errcount>=3)					// Ignore record if too many errors, though connection to outdoor unit is not lost
	{	w.ok=0;
		return 1;
	}
	else if (sensorlost)
	{	w.ok=0;	
		return 0;
	}
	else
	{	w.ok=1;
		return 0;
	}
		
}

/*
static size_t write_callback(char *buffer, size_t size,size_t nitems,void *output)
{
//	logger(LOG_DEBUG,"write_callback","Received data size %d nitems %d content: %s", size, nitems,buffer);
	strncpy(output,buffer,255);
	return size*nitems;
}
*/

int ws_submit(char *server_url, char** filebuf)
{
	if (*filebuf) 
	{	free(*filebuf);
		*filebuf=NULL;
	}

	http_setTimeout(15);
	int l=http_fetch(server_url, filebuf);
	
	if (l>=0)
	{	logger(LOG_DEBUG,"ws_submit","http_fetcher performed OK content: %s", *filebuf);
		return 0;
	}
	else
	{	logger(LOG_WARNING,"ws_submit","http_fetcher failed with message \"%s\"", http_strerror());
		return 1;
	}
}

// Make alarm specified by alm for weather record w

int ws_alarm (struct wrecord *w, struct walarm *alm)
{	
	char rv=0;

	if (alm->url != NULL)
	{
		char *output=malloc(strlen(alm->url)+100);
		if (!output)
		{	logger(LOG_ERROR,"main","Could not allocate %u bytes for output",strlen(alm->url)+100);
			rv=1;
		}
		else
		{	rv=ws_format(alm->url,output,1,"","","");
			if (rv!=0) 
				logger(LOG_ERROR,"main","Error formatting data return code %d", rv);
			else
			{	logger(LOG_DEBUG,"main","Submitting to alarm URL: %s", output);
				rv=ws_submit(output,&filebuf); // NB: Error in ws_submit will be ignored, just warning
				if (rv!=0) logger(LOG_WARNING,"main","Submitting to alarm URL %s failed", output);
			}
			free(output);
		}
	}

	rv=0;

	if (alm->run != NULL)
	{
		char *output=malloc(strlen(alm->run)+100);
		if (!output)
		{	logger(LOG_ERROR,"main","Could not allocate %u bytes for output",strlen(alm->run)+100);
			rv=1;
		}
		else
		{	rv=ws_format(alm->run,output,1,"","","");
			if (rv!=0) 
				logger(LOG_ERROR,"main","Error formatting data return code %d", rv);
			else
			{	logger(LOG_WARNING,"main","Launching command: %s", output);
				system(output); // NB: Errors are not recognizable here
			}
			free(output);
		}
	}

	rv=0;
	
	if (alm->email != NULL && frewe_server_url_alarm!=NULL)
	{
		char *output=malloc(strlen(frewe_server_url_alarm)+strlen(alm->email)+100);
		if (!output)
		{	logger(LOG_ERROR,"main","Could not allocate %u bytes for output",strlen(frewe_server_url_alarm)+strlen(alm->email)+100);
			rv=1;
		}
		else
		{	sprintf(output,"%s&email=%s&type=%s%%20%0.1f",frewe_server_url_alarm,alm->email,alm->type,alm->threshold);
			logger(LOG_DEBUG,"main","Submitting to alarm email URL: %s", output);
			rv=ws_submit(output,&filebuf); // NB: Error in ws_submit will be ignored, just warning
			if (rv!=0) logger(LOG_WARNING,"main","Submitting to alarm email URL %s failed", output);
			free(output);
		}
	}
	
	return 0;		// Errors will be ignored
}



// Format wrecord w according to format string into out

void strcatenc(char *out,char *text,unsigned char urlencode)
{
	char *encoded=NULL;
	if (urlencode)
	{	encoded=URLencode(text);
		if (!encoded)
		{	logger(LOG_ERROR,"main","URLencode could not allocate memory for '%s'",text);
		}
		else
		{	strcat(out,encoded);
			free(encoded);
		}
	}
	else
	{	strcat(out,text);
	}
	return;
}


int ws_format(char *format, char *out, unsigned char urlencode, char *user, char *pass, char *error)
{
	char buf[100];

	strcpy(out,"");

	for (;*format;format++)
	{
		if (*format=='%')
		{
			switch (*++format)
			{
				case 'h': // inside humidity %
					if (w.humin>100 || w.humin==0)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%d",out,w.humin);
					break;

				case 'H': // outside humidity %
					if (w.humout>100 || w.humout==0)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%d",out,w.humout);
					break;

				case 'I': // inside temperature C
					if (w.tempin>100 || w.tempin<-100)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.1f",out,w.tempin);
					break;

				case 'i': // inside temperature F
					if (w.tempin>100 || w.tempin<-100)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.1f",out,c2f(w.tempin));
					break;

				case 'O': // outside temperature C
					if (w.tempout>100 || w.tempout<-100)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.1f",out,w.tempout);
					break;

				case 'o': // outside temperature F
					if (w.tempout>100 || w.tempout<-100)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.1f",out,c2f(w.tempout));
					break;

				case 'E': // dew point C
					if (w.tempdew>100 || w.tempdew<-100)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.1f",out,w.tempdew);
					break;

				case 'e': // dew point F
					if (w.tempdew>100 || w.tempdew<-100)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.1f",out,c2f(w.tempdew));
					break;

				case 'C': // windchill temperature C
					if (w.tempchill>100 || w.tempchill<-100)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.1f",out,w.tempchill);
					break;

				case 'c': // windchill temperature F
					if (w.tempchill>100 || w.tempchill<-100)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.1f",out,c2f(w.tempchill));
					break;

				case 'W': // wind speed kmh
					if (w.windspeed==-1)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.1f",out,w.windspeed);
					break;

				case 'w': // wind speed mph
					if (w.windspeed==-1)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.1f",out,kmh2mph(w.windspeed));
					break;

				case 'v': // wind speed ms
					if (w.windspeed==-1)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.1f",out,kmh2ms(w.windspeed));
					break;

				case 'G': // wind gust kmh
					if (w.windgust==-1)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.1f",out,w.windgust);
					break;

				case 'g': // wind gust mph
					if (w.windgust==-1)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.1f",out,kmh2mph(w.windgust));
					break;

				case 'D': // wind direction - named
					strcatenc(out,w.winddir,urlencode);
					break;

				case 'd': // wind direction - degrees
					if (w.winddeg==-1)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%d",out,w.winddeg);
					break;

				case 'P': // abs. pressure hPa
					if (w.pressabs<900 || w.pressabs>1100)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.1f",out,w.pressabs);
					break;

				case 'p': // abs. pressure in
					if (w.pressabs<900 || w.pressabs>1100)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.2f",out,hpa2in(w.pressabs));
					break;

				case 'L': // rel. pressure hPa
					if (w.pressrel<900 || w.pressrel>1100)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.1f",out,w.pressrel);
					break;

				case 'l': // rel. pressure in
					if (w.pressrel<900 || w.pressrel>1100)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.2f",out,hpa2in(w.pressrel));
					break;

				case 'm': // illumination in W/m²
					if (w.illu==-1)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.2f",out,lux2wattm2(w.illu));
					break;

				case 'M': // illumination in lux
					if (w.illu==-1)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.1f",out,w.illu);
					break;

				case 'R': // rain total counter mm
					if (w.rain==-1)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.1f",out,w.rain);
					break;

				case 'r': // rain total counter in
					if (w.rain==-1)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.2f",out,mm2in(w.rain));
					break;

				case 'S': // rain 60 min mm
					if (w.rainhour==-1)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.1f",out,w.rainhour);
					break;

				case 's': // rain 60 min in
					if (w.rainhour==-1)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.2f",out,mm2in(w.rainhour));
					break;

				case 'T': // rain from 0h mm
					if (w.rainday==-1)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.1f",out,w.rainday);
					break;

				case 't': // rain from 0h in
					if (w.rainday==-1)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%0.2f",out,mm2in(w.rainday));
					break;

				case 'N': // datetime local
					strftime(buf,sizeof(buf),"%Y-%m-%d %H:%M:%S",localtime(&w.datetime));
					strcatenc(out,buf,urlencode);
					break;

				case 'n': // datetime UTC
					strftime(buf,sizeof(buf),"%Y-%m-%d %H:%M:%S",gmtime(&w.datetime));
					strcatenc(out,buf,urlencode);
					break;

				case 'U': // UV
					if (w.uv==-1)
						strcatenc(out,error,urlencode);
					else
						sprintf(out,"%s%d",out,w.uv);
					break;

				case 'Y': // date DD.MM.YYYY local
					strftime(buf,sizeof(buf),"%d.%m.%Y",localtime(&w.datetime));
					strcatenc(out,buf,urlencode);
					break;

				case 'y': // datetime YYYYMMDDhhmm local
					strftime(buf,sizeof(buf),"%Y%m%d%H%M",localtime(&w.datetime));
					strcatenc(out,buf,urlencode);
					break;

				case 'Z': // time HH:MM local
					strftime(buf,sizeof(buf),"%H:%M",localtime(&w.datetime));
					strcatenc(out,buf,0); // Force no encoding for :
					break;

				case 'a': // age
					sprintf(out,"%s%d",out,w.age);
					break;

				case 'K': // ws type
					strcatenc(out,ws_type,urlencode);
					break;

				case 'x': // username
					strcatenc(out,user,urlencode);
					break;

				case 'X': // password
					strcatenc(out,pass,urlencode);
					break;

				case '%': // percents
					strcatenc(out,"%",0);
					break;
			}
		}
		else if (*format=='\\')
		{
			switch (*++format)
			{
				case 'n':
					strcatenc(out,"\n",urlencode);
					break;

				case 'r':
					strcatenc(out,"\r",urlencode);
					break;

				case 't':
					strcatenc(out,"\t",urlencode);
					break;

			}
		}
		else
		{
			char minibuf[2];
			sprintf(minibuf,"%c",*format);
			strcatenc(out,minibuf,0);
		}
	}

	return 0;
}


int ws_dump(uint16_t address,uint8_t *data,uint16_t size,uint8_t w)
{
	uint16_t i,j,s;
	char *buf;

	s=8+(w*5)+1;
	logger(LOG_DEBUG,"ws_dump","Allocate %u bytes for temporary buffer",s);
	buf=malloc(s);
	if (!buf) logger(LOG_WARNING,"ws_dump","Could not allocate %u bytes for temporary buffer, verbose dump enabled",s);

	logger(LOG_INFO,"ws_dump","Dump %u bytes from address 0x%04X",size,address);
	for (i=0;i<size && buf && data;)
	{
		if (buf) sprintf(buf,"0x%04X:",address+i);
		for (j=0;j<w && i<size;i++,j++)
		{
			if (buf)
			{
				sprintf(buf,"%s 0x%02X",buf,data[i]);
			} else
			{
				logger(LOG_INFO,"ws_dump","0x%04X: 0x%02X",address+i,data[i]);
			}
		}
		if (buf) logger(LOG_INFO,"ws_dump",buf);
	}

	return 0;
}

// Get address for given base and position, correct circular buffer calculation

uint16_t get_address(uint16_t base, int position)
{
	signed long a = base + position * ws_entry_size;
	
	if (a >= WS_MAX_ENTRY_ADDR)
	{	while (a+WS_MIN_ENTRY_ADDR >= WS_MAX_ENTRY_ADDR) a -= WS_MAX_ENTRY_ADDR;
		a += WS_MIN_ENTRY_ADDR;
	}
	
	if (a < WS_MIN_ENTRY_ADDR)
	{	while (a-WS_MIN_ENTRY_ADDR < WS_MIN_ENTRY_ADDR) a += WS_MAX_ENTRY_ADDR;
		a -= WS_MIN_ENTRY_ADDR;
	}
	
	logger(LOG_DEBUG,"get_address","Base 0x%04X position %d = 0x%04X",base,position,(uint16_t) a);
	
	return (uint16_t) a;
}


//***************************************************************
// Signal handling
//***************************************************************

void signal_handler(int signal)
{
	if (signal == SIGTERM)
		logger(LOG_DEBUG,"signal_handler","SIGTERM received, exiting...");
	else if (signal == SIGQUIT)
		logger(LOG_ERROR,"signal_handler","SIGQUIT received, exiting...");
	else if (signal == SIGINT)
		logger(LOG_ERROR,"signal_handler","SIGINT received, exiting...");
	else if (signal == SIGFPE)
		logger(LOG_ERROR,"signal_handler","SIGFPE received, exiting...");
	else if (signal == SIGILL)
		logger(LOG_ERROR,"signal_handler","SIGILL received, exiting...");
	else if (signal == SIGSEGV)
		logger(LOG_ERROR,"signal_handler","SIGSEGV received, exiting...");
	else if (signal == SIGBUS)
		logger(LOG_ERROR,"signal_handler","SIGBUS received, exiting...");
	else		
		logger(LOG_ERROR,"signal_handler","Unknown signal received, exiting...");

	if (dev) ws_close(&dev);
	exit(1);
}

//***************************************************************
// Common functions
//***************************************************************

void logger(log_event event,char *function,char *msg,...)
{
	va_list args;

	va_start(args,msg);
	switch (event)
	{
		case LOG_DEBUG:
			if (_log_debug)
			{
				fprintf(_log_debug,"message: frewe.%s - ",function);
				vfprintf(_log_debug,msg,args);
				fprintf(_log_debug,"\n");
			}
			break;

		case LOG_WARNING:
			if (_log_warning)
			{
				fprintf(_log_warning,"warning: frewe.%s - ",function);
				vfprintf(_log_warning,msg,args);
				fprintf(_log_warning,"\n");
			}
			break;

		case LOG_ERROR:
			if (_log_error)
			{
				fprintf(_log_error,"error: frewe.%s - ",function);
				vfprintf(_log_error,msg,args);
				fprintf(_log_error,"\n");

// Send error message to frewe-server

				if (frewe_server_url_error!=NULL)
				{
					char *last_error_text = malloc(strlen(msg)+500);
					if (last_error_text) 
					{	vsprintf(last_error_text,msg,args); 
						char *server_url_error_full = malloc(strlen(frewe_server_url_error)+strlen(last_error_text)+100);
						if (server_url_error_full)
						{	strcpy(server_url_error_full,frewe_server_url_error);
							strcat(server_url_error_full,"&errortext=");
							strcatenc(server_url_error_full,last_error_text,1);
							logger(LOG_DEBUG,"main","Submit error message to server URL: %s", server_url_error_full);
							ws_submit(server_url_error_full,&filebuf);
							free(server_url_error_full);
						}
						free(last_error_text);
					}
				}
			}
			break;

		case LOG_INFO:
			if (_log_info)
			{
				fprintf(_log_info,"info: frewe.%s - ",function);
				vfprintf(_log_info,msg,args);
				fprintf(_log_info,"\n");
			}
			break;
	}
	va_end(args);
}

// Converts a hex character to its integer value

char from_hex(char ch) {
  return isdigit(ch) ? ch - '0' : tolower(ch) - 'a' + 10;
}

// Converts an integer value to its hex character

char to_hex(char code) 
{
	static char hex[] = "0123456789abcdef";
	return hex[code & 15];
}

// Returns a url-encoded version of str
// IMPORTANT: be sure to free() the returned string after use

char* URLencode(char *str) 
{
	char *pstr = str, *buf = malloc(strlen(str) * 3 + 1), *pbuf = buf;
	if (buf!=NULL)
	{
        	while (*pstr)
          	{
            		if (isalnum(*pstr) || *pstr == '-' || *pstr == '_' || *pstr == '.' || *pstr == '~') 
              			*pbuf++ = *pstr;
            		else if (*pstr == ' ') 
              			*pbuf++ = '+';
            		else 
              			*pbuf++ = '%', *pbuf++ = to_hex(*pstr >> 4), *pbuf++ = to_hex(*pstr & 15);
            		pstr++;
          	}
          	*pbuf = '\0';
	}
  	return buf;
}

// Returns a url-decoded version of str 
// IMPORTANT: be sure to free() the returned string after use

char* URLdecode(char *str)
{
	char *pstr = str, *buf = malloc(strlen(str) + 1), *pbuf = buf;
	if (buf!=NULL)
	{
		while (*pstr) 
		{
			if (*pstr == '%') 
			{
      				if (pstr[1] && pstr[2]) 
      				{
        				*pbuf++ = from_hex(pstr[1]) << 4 | from_hex(pstr[2]);
        				pstr += 2;
      				}
    			} 
    			else if (*pstr == '+') 
    			{ 
      				*pbuf++ = ' ';
    			} 
    			else 
    			{
      				*pbuf++ = *pstr;
    			}
    			pstr++;
  		}
  		*pbuf = '\0';
  	}
	return buf;
}

long diff_time(const struct timeval *tact, const struct timeval *tlast)
{
    long diff;

    diff = (tact->tv_usec + 1000000 * tact->tv_sec) -
	   (tlast->tv_usec + 1000000 * tlast->tv_sec);
	   
    return diff;
}
