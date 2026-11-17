-- Prove2me | solution 1 for Kyprianou.Ch06.overlappingMarkedCountSpatialPartitionAe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:05:53.799728+00:00
-- url     : https://prove2.me/submissions/986e8217-919b-4956-931e-e9dcf6cc43c6

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B C : Set E) :
    ∀ᵐ omega ∂P, ∀ t : NNReal,
      N omega t B = N omega t (B \ C) + N omega t (B ∩ C) ∧
      N omega t C = N omega t (C \ B) + N omega t (B ∩ C) := by
  filter_upwards [hPPP.2.1] with omega hPath
  intro t
  have hDisjB : Disjoint (B \ C) (B ∩ C) := by
    apply Set.disjoint_left.mpr
    intro x hxBC hxInt
    exact hxBC.2 hxInt.2
  have hDisjC : Disjoint (C \ B) (B ∩ C) := by
    apply Set.disjoint_left.mpr
    intro x hxCB hxInt
    exact hxCB.2 hxInt.1
  have hUnionB : (B \ C) ∪ (B ∩ C) = B := by
    ext x
    simp only [Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
    tauto
  have hUnionC : (C \ B) ∪ (B ∩ C) = C := by
    ext x
    simp only [Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
    tauto
  constructor
  · calc
      N omega t B = N omega t ((B \ C) ∪ (B ∩ C)) := by
        rw [hUnionB]
      _ = N omega t (B \ C) + N omega t (B ∩ C) :=
        hPath.2.1 t (B \ C) (B ∩ C) hDisjB
  · calc
      N omega t C = N omega t ((C \ B) ∪ (B ∩ C)) := by
        rw [hUnionC]
      _ = N omega t (C \ B) + N omega t (B ∩ C) :=
        hPath.2.1 t (C \ B) (B ∩ C) hDisjC
