-- Prove2me | solution 1 for Kyprianou.Ch06.fourOverlapIndexedAtomFamilyPairwiseDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:41:52.054159+00:00
-- url     : https://prove2.me/submissions/43c6f39d-95f3-4e2e-ba90-85b5f5e9e290

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (N : Omega → NNReal → Set E → Nat)
    (B C : Set E) (s t : NNReal) (k l : Nat) :
    let F : Fin (k+1) × Fin (l+1) → Set Omega := fun i =>
      {omega | (i.1 : Nat)+(i.2 : Nat) ≤ l ∧
        N omega s (B \ C) = k-(i.1 : Nat) ∧
        N omega s (B ∩ C) = (i.1 : Nat) ∧
        N omega s (C \ B) = (i.2 : Nat) ∧
        N omega t C - N omega s C = l-(i.1 : Nat)-(i.2 : Nat)}
    Pairwise (fun i j => Disjoint (F i) (F j)) := by
  dsimp only
  intro i j hij
  apply Set.disjoint_left.mpr
  intro omega hi hj
  apply hij
  change (i.1 : Nat)+(i.2 : Nat) ≤ l ∧
    N omega s (B \ C) = k-(i.1 : Nat) ∧
    N omega s (B ∩ C) = (i.1 : Nat) ∧
    N omega s (C \ B) = (i.2 : Nat) ∧
    N omega t C-N omega s C = l-(i.1 : Nat)-(i.2 : Nat) at hi
  change (j.1 : Nat)+(j.2 : Nat) ≤ l ∧
    N omega s (B \ C) = k-(j.1 : Nat) ∧
    N omega s (B ∩ C) = (j.1 : Nat) ∧
    N omega s (C \ B) = (j.2 : Nat) ∧
    N omega t C-N omega s C = l-(j.1 : Nat)-(j.2 : Nat) at hj
  apply Prod.ext
  · exact Fin.ext (hi.2.2.1.symm.trans hj.2.2.1)
  · exact Fin.ext (hi.2.2.2.1.symm.trans hj.2.2.2.1)
