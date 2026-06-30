#! /usr/bin/perl
#
# Converts a simple, creator-friendly format for Map::Tube maps into standard Map::Tube XML format.
#
# The purpose of this format is not generality, well-structuredness, suitability for data exchange etc.,
# but to allow fast entry of tube line information for Map::Tube. It will derive or generate all
# data that are internally needed for Map::Tube. The format is crufty and idiosyncratic.
# It does support the extension to the original Map::Tube format to specify names in more than one script or language.
#
# The format centres around tube lines. In the simplest case, there is one text line giving the name (and colour)
# of the tube line, followed by all the station names in proper order (one station per line).
# The software will create all the automatically creatable additional information, like unique ids
# and station-position indices.
# Special characters allow for the specification of branches and one-way connections.
# Names are checked for similarity to alert for possible typos.
#
# Each text line contains either:
# * nothing => ignored
# * Lines starting with # => ignored
# * a semicolon, followed by the map name; optionally, followed by alternate names, each separated by a semicolon;
# optionally followed by a colon, followed by a prefix to use for the ids. (Default: first three letters of map name)
# * a colon followed by a tube line name
#   * plus possibly a semicolon and then an alternate name
#   * plus possibly a colon and then a colour code
# (This tube line will be applied to the subsequently defined stations.)
# * a station name
# * possibly preceded by a "=", "<", or ">"
#   * "=" means that this station is bidirectionally linked to the previous station (if any).
#   This is the default, so the "=" can be omitted.
#   * "<" means that this station links to the previous one, but not the other way round (unidirectional)
#   * ">" means that this station is linked to by the previous one, but not the other way round (unidirectional)
#   * "!" means that this station is not connected to the previous one.
# * plus possibly a semicolon and then an alternate name
# * plus possibly a "=", "<", or ">" and then the name of a station linked to or from this one on the same tube line (used for branches in tube lines)
#   * "=" again means bidirectional linking
#   * ">" means unidirectional linking from the initially named station to the one named in the tail specification
#   * "<" means unidirectional linking to the initially named station from the one named in the tail specification
# * plus possibly a colon, followed by an other_link name, followed by a semicolon, followed by a station name.
# * Tail specifications with "="/"<"/">" and other_link specifications can be repeated. They always refer to the station named first on the text line
#   Tail specifications of connected stations should be stated only if they are not the immediately preceding or following station in the sequence.
# * Text lines may carry a comment at the line end. Comments start at a hash sign followed by at least one blank.
# Comments are carried over into the XML file close to the subsequent line or station.
#
# Gisbert W. Selke, 2026-06-30
#
use Modern::Perl;
use utf8;
use open ':std', ':encoding(UTF-8)'; # needed for properly encoding/decoding Unicode strings on I/O
use Data::Dump qw(dump);
use Getopt::Long::Descriptive;
use List::Util qw(pairs);
use Text::Levenshtein::XS qw(distance);
use Tie::IxHash;
use version 0.77 ( );
use XML::Twig;

our $VERSION = version->declare('v0.1.1');

my ( $basename, $id_prefix, $errct, $xml, $root, $map_name, %map_names_alt, $dist_limit,
   $opts, $usage_info, %doc, %idstore,
   %line_names, %line_names_alt, %line_ids, %line_ids_idx,
   %station_names, %station_names_alt, %station_ids, %station_lines, %station_links, %station_other_links,
   %station_temp_link, %station_temp_other_link,
   );

( $opts, $usage_info ) = describe_options(
               '%c %o [base file name]',
               ( [ 'map=s',        'base file name for the input ("-map.lst" and "-map.xml" will be added)', ],
               [ 'mapname=s',    'descriptive name of the map', ],
               [ 'prefix=s',     'prefix to use for internal ids of lines and stations', ],
               [ 'similarity=i', 'threshold for flagging names as potential typos', { default => 2 } ],
               [ 'help|h|?',     'show usage message and exit', { shortcircuit => 1 } ],
               ),
               { show_defaults => 1 }
      );
if ( $opts->help( ) ) {
  print STDERR $usage_info->text( );
  exit(1);
}
($basename)  =  $opts->map( ) // $ARGV[0];
$map_name  =  $opts->mapname( ) // $basename;
$id_prefix   =  idmaker( $opts->prefix( ) // lc( substr( $basename, 0, 3 ) ) );
$id_prefix  .=  '_' unless ( $id_prefix =~ /_$/ );
$dist_limit  =  $opts->similarity( );

my $lstname = $basename . '-map.lst';
die "Input file '$lstname' not found: $@" unless -s $lstname;

my @comment;

my( $line_id, $line_name, $idx, $prev_id, $prev_name );
open( my $inf, '<', $lstname ) or die "Cannot read list file $lstname: $@";
binmode( $inf, ':utf8' );
binmode( STDOUT, ':utf8' );
while (<$inf>) {
  chomp;
  s/^\s+//;
  s/\s+$//;
  next unless $_;
  if ( /(?:#\s+(.*))|(?:#$)/ ) {
  push( @comment, $1 ) if length($1);
  s/\s*(#\s+.*$)|(#$)//;
  }
  next if $_ eq '';
  s/\s*:\s*/:/;
  s/\s*;\s*/;/;
  my @parts = /(                        # catch all parts
        (?:                       # just for grouping, not capturing
          (?<!\\)                   # negative lookbehind: the following only if not preceded by a backslash
          [=<>:;]                   # a single operator
        )                       # and we have a single operator
        |                       # ... or ...
        (?:                       # just for grouping, not capturing
          (?<=\\)                   # positive lookbehind: the following only if preceded by a backslash
          [=<>:;]                   # an escaped operator character, to be treated like an ordinary character
          |                       # ... or ...
          [^=<>:;]                    # anything not looking like an operator
        )+                        # and possibly many of these
         )/gx;
  # final works:
  if (@parts) {
  if ( $parts[0] =~ /^!/ ) {
    # Operator '!' only allowed at the start of the line; not handled by the regex above
    $parts[0] = substr( $parts[0], 1 );
    unshift( @parts, '!' );
  } elsif ( $parts[0] !~ /^[=<>:;]$/ ) {
    # If no operator given at start of line, default is '=':
    unshift( @parts, '=' );
  }
  }
  @parts = map { s/ & / &amp; /g; $_ } map { s/\\(.)/$1/g; $_ } @parts;    # replace escaped operator characters by the plain characters

# say STDERR dump(\@parts);
  # Now run through all the @parts, which contains alternating operators and texts.
  @parts = pairs(@parts);

  my( $op, $text ) = @{ shift(@parts) };
  if ( $op eq ';' ) {
  # This defines the map name. It should occur only once at the start of the input.
  $map_name = $text // $map_name;
  my $name_alt_ct = '';
  while (@parts) {
    ( $op, $text ) = @{ shift(@parts) };
    if ( $op eq ';' ) {
    $name_alt_ct++ while exists( $map_names_alt{'name_alt' . $name_alt_ct} );
    $map_names_alt{'name_alt' . $name_alt_ct} = $text;
    } elsif ( $op eq ':' ) {
    $id_prefix  = $text;
    $id_prefix .=  '_' unless ( $id_prefix =~ /_$/ );
    } else {
    die "Internal error: unhandled operator '$op' in line $.";
    }
  }
  next;
  }

  if ( $op eq ':' ) {
  # This defines a (possibly new) line:
  $line_name = $text;
  if ( exists $line_names{$line_name} ) {
    # We know this line already. We ignore additional information possibly given here.
    $line_id   = $line_names{$line_name}{'id'};
    $idx     = ( sort { $b <=> $a } keys( %{ $line_ids_idx{$line_id} } ) )[0];
    $prev_name = ( grep { exists( $station_lines{$_}{$line_id} ) && exists( $station_lines{$_}{$line_id}{$idx} ) } keys(%station_names) )[0];
    $prev_id   = $station_names{$prev_name}{'id'};
  } else {
    # This line is new to us:
    $line_id = uc( idmaker( ( split( /\s+/, $line_name ) )[0], 6, $id_prefix ) );
    my %tmp;
    tie( %tmp, 'Tie::IxHash', 'id' => $line_id, 'name' => $line_name, color => '#404040', );
    my $name_alt_ct = '';
    while (@parts) {
    ( $op, $text ) = @{ shift(@parts) };
    if ( $op eq ';' ) {
      $name_alt_ct++ while exists( $tmp{'name_alt' . $name_alt_ct} );
      if ( exists( $line_names_alt{$text}{$name_alt_ct} ) ) {
      warn "Alternative name $text multiply defined\n";
      $errct++;
      }
      $line_names_alt{$text}{$name_alt_ct} = $line_name;
      $tmp{'name_alt' . $name_alt_ct} = $text;
    } elsif ( $op eq ':' ) {
      $tmp{'color'} = $text;
    } else {
      die "Internal error: unhandled operator '$op' in line $.";
    }
    }
    $line_names{$line_name} = \%tmp;
    $line_ids{$line_id} = $line_name;
    $idx = 0;
    undef($prev_id);
    undef($prev_name);
  }
  if ( @comment ) {
    $line_names{$line_name}{'comment'} //= [ ];
    push( @{ $line_names{$line_name}{'comment'} }, @comment );
    undef(@comment);
  }
  next;
  }

  # This must be a station definition:
  my $name = $text;
  my( @mylinks, $id );
  $idx++; # Index of station on this line
  my $is_new_station;
  if ( exists $station_names{$name} ) {
  # We have already heard about this station before:
  $id = $station_names{$name}{'id'};
  #if ($name_alt) {
  #  if ( exists( $station_names{$name}{'name_alt'} ) ) {
  #  if ( $station_names{$name}{'name_alt'} ne $name_alt ) {
  #    warn "Station name $name has inconsistent alternative names";
  #    $errct++;
  #  }
  #  }
  #  if ( exists( $station_names_alt{$name_alt} ) ) {
  #  if ( $station_names_alt{$name_alt} ne $name ) {
  #    warn "Station alternative name $name_alt is tied to different station names";
  #    $errct++;
  #  }
  #  }
  #}
  } else {
  # This station is new to us.
  $id = sprintf( "%s%02d", lc($line_id // 'dummy'), $idx );
  my %tmp;
  tie( %tmp, 'Tie::IxHash', 'id' => $id, 'name' => $name, );
  $station_names{$name} = \%tmp;
  $is_new_station++;
  }

  if ( !defined($line_id) ) {
  warn "Station name $name without a previously defined line -- station ignored\n";
  $errct++;
  next;
  }

  if ( $op ne '!' ) {
  # Handle connection to and/or from previous station (if any).
  $station_links{$name}{$prev_id}++ if $prev_id && ( $op ne '>' );
  $station_links{$prev_name}{$id}++ if $prev_name && ( $op ne '<' );
  }
  # Prepare for this station to be linked on the next occasion
  $prev_id   = $id;
  $prev_name = $name;

  my $name_alt_ct = '';
  while (@parts) {
  ( $op, $text ) = @{ shift(@parts) };
  if ( $op eq ';' ) {
    # An alternative station name (of possibly many):
    $name_alt_ct++ while ( exists( $station_names{$name}{'name_alt' . $name_alt_ct} ) && ( $station_names{$name}{'name_alt' . $name_alt_ct} ne $text ) );
    if ( exists( $station_names{$name}{'name_alt' . $name_alt_ct} ) && ( $station_names{$name}{'name_alt' . $name_alt_ct} ne $text ) && !$is_new_station ) {
    $station_names{$name}{'name_alt' . $name_alt_ct} = $text;
    warn "Station name $name has differing numbers of multiple alternative names\n" if $name_alt_ct;
    } else {
    $station_names{$name}{'name_alt' . $name_alt_ct} = $text;
    }
    if ( exists( $station_names_alt{$text}{$name_alt_ct} ) && ( $station_names_alt{$text}{$name_alt_ct} ne $name ) ) {
    warn "Station alternative name $text is tied to different station names\n";
    $errct++;
    }
    $station_names_alt{$text}{$name_alt_ct} = $name;
  } elsif ( $op =~ /[=<>]/ ) {
    # Handle explicit bi- or unidirectional link in tail specification. Operator "!" not allowed in tail spec, because it wouldn't make sense.
    my $mylink_id;
    if ( exists( $station_names{$text} ) ) {
    # This link concerns a station that we already know:
    $mylink_id = $station_names{$text}{'id'};
    } else {
    # This concerns a station that we haven't encountered before, so we have no ID yet. Pick an "impossible" temporary one.
    $mylink_id = $station_temp_link{$text} //= ' ' . $line_id . ' ' . $idx;
    }
    $station_links{$name}{$mylink_id}++ if ( $op ne '<' );
    $station_links{$text}{$id}++      if ( $op ne '>' );
  } elsif ( $op eq ':' ) {
    die "Incomplete other_link specification at line $." unless @parts;
    # Handle other_links
    my $other_link_name = $text;
    ( $op, $text ) = @{ shift(@parts) };
    die "Invalid other_link specification at line $.: op='$op'" unless $op eq ';';
    my $mylink_id;
    if ( exists( $station_names{$text} ) ) {
    # This other_link concerns a station that we already know:
    $mylink_id = $station_names{$text}{'id'};
    } else {
    # This concerns a station that we haven't encountered before, so we have no ID yet. Pick an "impossible" temporary one.
    $mylink_id = $station_temp_other_link{$text} //= ' ' . scalar( keys %station_temp_other_link );
    }
    $station_other_links{$name}{$mylink_id} = $other_link_name;
  } else {
    die "Internal error: unhandled operator '$op' in line $.";
  }
  }

  $station_ids{$id} = $name;
  $station_names{$name}{'line'} = undef;
  $station_names{$name}{'link'} = undef;
  if ( exists( $station_lines{$name}{$line_id} ) ) {
  warn "Station name $name occurs multiply on line name $line_name\n";
  $errct++;
  }
  $station_lines{$name}{$line_id}{$idx}++;

  if ( @comment ) {
  $station_names{$name}{'comment'} //= [ ];
  push( @{ $station_names{$name}{'comment'} }, @comment );
  undef(@comment);
  }
}
close($inf);

# Finalize any dangling temp_ids on ordinary links:
for my $mylink_name( keys %station_temp_link ) {
  my $mylink_id = $station_temp_link{$mylink_name};
  my( undef, $myline_id, $idx ) = split( /\s+/, $mylink_id );
  if ( exists( $station_lines{$mylink_name} ) ) {
  if ( exists( $station_lines{$mylink_name}{$myline_id} ) ) {
    # Found this station on this line. Happy!
    my $id = $station_names{$mylink_name}{'id'};
    for ( grep { exists( $station_links{$_}{$mylink_id} ) } keys %station_links ) {
    $station_links{$_}{$id}++;
    delete( $station_links{$_}{$mylink_id} );
    }
  } else {
    warn "There is a '>' link to station name '$mylink_name' which exists but not on this line\n";
    $errct++;
  }
  } else {
  warn "There is a '>' link to undefined station name '$mylink_name'\n";
  $errct++;
  }
}

# Finalize any dangling temp_ids on other_links:
for my $mylink_name( keys %station_temp_other_link ) {
  my $mylink_id = $station_temp_other_link{$mylink_name};
  if ( exists( $station_names{$mylink_name} ) ) {
  for my $station_name( keys %station_other_links ) {
    if ( exists $station_other_links{$station_name}{$mylink_id} ) {
    $station_other_links{$station_name}{ $station_names{$mylink_name}{'id'} } = $station_other_links{$station_name}{$mylink_id};
    delete( $station_other_links{$station_name}{$mylink_id} );
    }
  }
  } else {
  warn "There is an other_link to undefined station name '$mylink_name'\n";
  $errct++;
  }
}

# Just in case: make all other_links symmetric:
for my $station_name( keys %station_other_links ) {
  my $station_id = $station_names{$station_name}{'id'};
  for my $linked_id( keys %{ $station_other_links{$station_name} } ) {
  my $linked_name = $station_ids{$linked_id};
  $station_other_links{$linked_name}{$station_id} = $station_other_links{$station_name}{$linked_id};
  }
}

$doc{'comment'} = \@comment if @comment;
# say STDERR 'Map name:';
# say STDERR dump($map_name);
# say STDERR 'Map names alt:';
# say STDERR dump(\%map_names_alt);
# say STDERR 'Line ids:';
# say STDERR dump(\%line_ids);
# say STDERR 'Line names_alt:';
# say STDERR dump(\%line_names_alt);
# say STDERR 'Line names';
# say STDERR dump(\%line_names);
# say STDERR 'Station ids:';
# say STDERR dump(\%station_ids);
# say STDERR 'Station names_alt:';
# say STDERR dump(\%station_names_alt);
# say STDERR 'Station names:';
# say STDERR dump(\%station_names);
# say STDERR 'Station lines:';
# say STDERR dump(\%station_lines);
# say STDERR 'Station links:';
# say STDERR dump(\%station_links);
# say STDERR 'Station other_links:';
# say STDERR dump(\%station_other_links);
# say STDERR '----------------------------------------------------------------';


my @station_names = sort keys %station_names;
my $n_station_names = scalar(@station_names);
my $simil_ct = 0;
for my $i ( 0..($n_station_names-2) ) {
  for my $j ( ($i+1)..($n_station_names-1) ) {
  if ( distance( $station_names[$i], $station_names[$j] ) <= $dist_limit ) {
    warn "Should these station names be identical? :$station_names[$i]:$station_names[$j]:\n";
    $simil_ct++;
  } else {
    my $name1 = $station_names[$i];
    my $name2 = $station_names[$j];
    $name1 =~ s/[^\w\d]+//g;
    $name2 =~ s/[^\w\d]+//g;
    if ( $name1 eq $name2 ) {
    warn "These station names are almost identical: :$station_names[$i]:$station_names[$j]:\n";
    $simil_ct++;
    }
  }
  }
}
say STDERR "$simil_ct pair(s) of similar station names" if $simil_ct;

say STDERR scalar( keys %line_names ), ' tube lines, ', scalar( keys %station_names ), ' stations';

die "$errct problem(s) must still be resolved" if $errct;

my $conv = XML::Twig::encode_convert( 'utf-8');
$xml = XML::Twig->new( keep_atts_order => 1,
             pretty_print    => 'record',
             comments      => 'process',
             keep_encoding => 1,
           #  output_encoding => 'utf-8',
           #  output_filter => $conv,
           );
# $xml->parse( '<?xml version="1.0" encoding="utf-8"?><tube name="' . $map_name . '"><lines></lines><stations></stations></tube>' );
$xml->parse( '<?xml version="1.0" encoding="utf-8"?><tube><lines></lines><stations></stations></tube>' );
$root = $xml->root( );
$root->set_att( name => $map_name, %map_names_alt );

my $lines_elt  = $root->first_child('lines');
my $stations_elt = $root->first_child('stations');

for my $line_name( sort keys(%line_names) ) {
  emit_comment( $root, $lines_elt, $line_names{$line_name} );
  # For each line, create a <line> tag under <lines>:
  my $line_elt = $root->new( 'line' => $line_names{$line_name} );
  $line_elt->paste( 'last_child', $lines_elt );

  $root->new( '#COMMENT' => ' ' . $line_name . ' ' )->paste( 'last_child', $stations_elt );

  # For each station, create a <station> tag under <stations>.
  # The order is given by the first line on which a station occurs, and therein in index order:
  my $line_id = $line_names{$line_name}{'id'};
  my @mystation_names = grep { exists( $station_lines{$_}{$line_id} ) } keys(%station_names);
  my %mystation_names = map { $_ => ( sort( keys( %{ $station_lines{$_}{$line_id} } ) ) )[0] } @mystation_names;
  for my $station_name( sort { $mystation_names{$a} <=> $mystation_names{$b} } keys(%mystation_names) ) {
  $station_names{$station_name}{'link'} = join( ',', sort( keys( %{ $station_links{$station_name} } ) ) );

  my @mylines;
  for my $myline_id( sort( keys( %{ $station_lines{$station_name} } ) ) ) {
    push( @mylines, join( ',', map { join( ':', $myline_id, $_ ) } sort { $a <=> $b } ( keys( %{ $station_lines{$station_name}{$myline_id} } ) ) ) );
  }
  $station_names{$station_name}{'line'} = join( ',', @mylines );

  if ( $station_other_links{$station_name} ) {
    my @myother_links;
    for my $myother_link_id( sort( keys( %{ $station_other_links{$station_name} } ) ) ) {
    push( @myother_links, join( ':', $station_other_links{$station_name}{$myother_link_id}, $myother_link_id ) );
    }
    $station_names{$station_name}{'other_link'} = join( ',', @myother_links );
  }

  emit_comment( $root, $stations_elt, $station_names{$station_name} );

  my $station_elt = $root->new( 'station' => $station_names{$station_name} );
  $station_elt->paste( 'last_child', $stations_elt );
  delete( $station_names{$station_name} );
  }
}

emit_comment( $root, $root, \%doc );

$xml->print( );


sub emit_comment {
  my( $root, $container, $href ) = @_;
  return unless $href;
  return unless exists $href->{'comment'};
  my @comment;
  for my $lin ( @{ $href->{'comment'} } ) {
  push( @comment, $lin ) unless grep { $lin eq $_ } @comment;
  }
  $root->new( '#COMMENT' => " $_ " )->paste( 'last_child', $container ) for @comment;
  delete  $href->{'comment'};

  return;
}

sub idmaker {
  my( $str, $maxlen, $prefix ) = @_;
  $str =~ tr/²³ÄäÁáÀàÂâÃãÅåÆæªČčÇç¢©ĎďÐðÉéÈèÊêĚěËë€ƒÍíÌìÎîÏï£µŇňÑñÖöÓóÒòÔôÕõŒœØøŘř®ŠšßŤťÞþÜüÚúÙùÛûŮůÝýŸÿ¥Žž/23AaAaAaAaAaAaAaaCcCcccDdDdEeEeEeEeEeEFIiIiIiIiLmNnNnOoOoOoOoOoOoOoRrrSssTtTtUuUuUuUuUuYyYyYZz/;
  $str =~ s/(\P{ASCII})/sprintf('%x', ord($1))/ge;
  $str =~ tr/A-Za-z0-9/_/c;
  $str = substr( $str, 0, $maxlen ) if $maxlen;
  $str = $prefix . $str if $prefix;
  my $tmp = '';
  $tmp++ while exists $idstore{ $str . $tmp };
  $str .= $tmp;
  $idstore{$str}++;

  return $str;
}
