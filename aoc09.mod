# ADVENT OF CODE 2015, DAY 9
# GNU MathProg solution by ojdo
# License: CC0

# Given undirected, weighted graph (V,E) of cities; input data at bottom
set V;
set E within V cross V;
param distance{(i,j) in E};
param N := card(V);

# for route and flow variables, derive the set of directed arcs between cities
set A within V cross V := E union setof{(i,j) in E} (j,i);
param weight{(i,j) in A} := (if (i,j) in E then distance[i,j] 
                                           else distance[j,i]);


# Variables
var route{(i,j) in A} binary;    # 1 if route contains (i -> j), 0 else
var flow_in{(i,j) in A} >= 0;    # flow quantity N@origin --> 0@destination
var flow_ot{(i,j) in A} >= 0;    # flow quantity N@origin --> 0@destination
var origin{v in V} binary;       # 1 if v is origin 0 else
var destination{v in V} binary;  # 1 if v is destination, 0 else
var passed{v in V} binary;       # 1 if v is travelled through, 0 else
var total_distance;  # total travel distance

# part I
minimize obj: total_distance;

# part II
# maximize obj: total_distance;

# Objective
# ---------
# sum of the distances of all travelled routes (i,j). The conditional if-else
# is required because only half of the arcs (i,j) in A have an identical
# element in E. 
s.t. distance_rule:
    total_distance = sum{(i,j) in A} route[i,j] * weight[i,j];

# Flow conservation
# -----------------
# This is the main logic leap. If the route is imagined as a single pen stroke,
# the sum of incoming strokes (first line, value 0 or 1) minus the sum of
# outgoing strokes (second line) be equal to zero. The only exception to this
# rule are the origin and destination cities. In the origin (positive), only a
# leaving (negative) route sum is necessary, while at the destination
# (negative) only an incoming (positive) route sum is required.
s.t. route_conservation{v in V}: 
    sum{(other,v) in A} route[other,v] - 
    sum{(v,other) in A} route[v,other] +
    origin[v] - destination[v] = 0;

s.t. flow_conservation{v in V}: 
    sum{(other,v) in A} flow_ot[other,v] - 
    sum{(v,other) in A} flow_in[v,other] +
    N * origin[v] - 1 * destination[v] = 0;

s.t. flow_loss_in_arcs{(i,j) in A}:
    flow_in[i,j] - flow_ot[i,j] = 1 * route[i,j];

s.t. flow_only_on_route{(i,j) in A}:
    flow_in[i,j] <= N * route[i,j];
    
# Ok, but how does this problem lead to a route that visits all cities?
# Nothing, so far. Right now, the minimising solution would simply be to set 
# all variable values to 0. So let's change that!
    
# First, we require that there is exactly one origin city.
s.t. one_origin: sum{v in V} origin[v] = 1;

# Same for the destination: there shall be exactly one.
s.t. one_destination: sum{v in V} destination[v] = 1;

# Is that already enough? 
# 
# Unfortunately, not. The solver could just pick any city and declare it *both*
# origin and destination. As we do not have to solve a classical travelling
# salesman problem here, the optimal solution can never be a roundtrip, anyway.
# Just imagine the minimal roundtrip. Just leave any single edge out, and you
# have created an even shorter origin-desintation trip.
#
# In short: forbid that a single city may be both origin and destination:
s.t. either_or{v in V}: origin[v] + destination[v] <= 1;

# Enough now?
# No again. Solver simply picks the two closest cities. We must somehow enforce
# that *all* cities must lie in the path of the flow variable `route`. How can
# we do that?

# First, we introduce the indicator variable `passed` and require that each
# city is either origin, destination or passed through during the final
# route:
s.t. at_least_one{v in V}: passed[v] + destination[v] + origin[v] >= 1;

# and now we must constrain the value of passed such that it may only become 
# 1 if the sum of incoming route (from the conservation constraint above) is
# non-zero. So let's do that:
s.t. route_pass{v in V}: passed[v] <= sum{(other,v) in A} route[other,v];



# Enough now?
# 
#
# Yes! 
solve;
# Wait for a bit (ok, 0.2 secs are pretty good)

# and print the solution
printf "\nShortest route: %d\n", total_distance;
for{v in V: origin[v] > 0 or destination[v] > 0} {
    printf "%s: %s\n", if destination[v] > 0 
        then  "destination" else "origin", v;
}
printf "\n";
for{(i,j) in A: route[i,j] > 0} {
    printf "%-13s -> %-13s: %3d, %3d\n", i, j,
    flow_ot[i,j],
    if (i,j) in E then distance[i,j] 
                  else distance[j,i];
}

data;

set V := 
  AlphaCentauri Arbre Faerun Norrath 
  Snowdin Straylight Tambi Tristram;

param : E : distance :=
  Tristram      AlphaCentauri  34
  Tristram      Snowdin       100
  Tristram      Tambi          63
  Tristram      Faerun        108
  Tristram      Norrath       111
  Tristram      Straylight     89
  Tristram      Arbre         132
  AlphaCentauri Snowdin         4
  AlphaCentauri Tambi          79
  AlphaCentauri Faerun         44
  AlphaCentauri Norrath       147
  AlphaCentauri Straylight    133
  AlphaCentauri Arbre          74
  Snowdin       Tambi         105
  Snowdin       Faerun         95
  Snowdin       Norrath        48
  Snowdin       Straylight     88
  Snowdin       Arbre           7
  Tambi         Faerun         68
  Tambi         Norrath       134
  Tambi         Straylight    107
  Tambi         Arbre          40
  Faerun        Norrath        11
  Faerun        Straylight     66
  Faerun        Arbre         144
  Norrath       Straylight    115
  Norrath       Arbre         135
  Straylight    Arbre         127;
end;
