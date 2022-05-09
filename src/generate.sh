#!/bin/bash

rm -rf ../files
mkdir ../files

for N in {28,32,36}
do
  K=$((N/4))
  T=$((K))
  T1=$((T-1))
  for S in {10..14}
  do
    python3 ./mdp-gen.py -n $N -t $T -s $S
    mv mdp-n$N-k$K-t$T-s$S.cnf ../files/mdp-$N-$S-sat.cnf
    python3 ./mdp-gen.py -n $N -t $T1 -s $S
    mv mdp-n$N-k$K-t$T1-s$S.cnf ../files/mdp-$N-$S-unsat.cnf
  done
done
