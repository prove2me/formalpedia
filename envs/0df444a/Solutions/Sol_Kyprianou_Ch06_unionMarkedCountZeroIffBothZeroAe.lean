-- Prove2me | solution 1 for Kyprianou.Ch06.unionMarkedCountZeroIffBothZeroAe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:11:10.502206+00:00
-- url     : https://prove2.me/submissions/7ad015cb-e5ad-4c85-9a22-eb4beefef078

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
      (N omega t B = 0 ∧ N omega t C = 0) ↔
      N omega t (B ∪ C) = 0 := by
  filter_upwards [hPPP.2.1] with omega hw
  intro t
  have hDisjU : Disjoint B (C \ B) := by
    apply Set.disjoint_left.mpr
    intro x hxB hxC
    exact hxC.2 hxB
  have hUnion : B ∪ (C \ B) = B ∪ C := by
    ext x
    simp only [Set.mem_union, Set.mem_diff]
    tauto
  have hU :
      N omega t (B ∪ C) =
        N omega t B + N omega t (C \ B) := by
    calc
      N omega t (B ∪ C) =
        N omega t (B ∪ (C \ B)) := by rw [hUnion]
      _ = N omega t B + N omega t (C \ B) :=
        hw.2.1 t B (C \ B) hDisjU
  have hDisjC : Disjoint (C \ B) (B ∩ C) := by
    apply Set.disjoint_left.mpr
    intro x hxC hxInt
    exact hxC.2 hxInt.1
  have hSetC : (C \ B) ∪ (B ∩ C) = C := by
    ext x
    simp only [Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
    tauto
  have hC :
      N omega t C =
        N omega t (C \ B) + N omega t (B ∩ C) := by
    calc
      N omega t C =
        N omega t ((C \ B) ∪ (B ∩ C)) := by rw [hSetC]
      _ = N omega t (C \ B) + N omega t (B ∩ C) :=
        hw.2.1 t (C \ B) (B ∩ C) hDisjC
  have hDisjB : Disjoint (B \ C) (B ∩ C) := by
    apply Set.disjoint_left.mpr
    intro x hxBC hxInt
    exact hxBC.2 hxInt.2
  have hSetB : (B \ C) ∪ (B ∩ C) = B := by
    ext x
    simp only [Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
    tauto
  have hB :
      N omega t B =
        N omega t (B \ C) + N omega t (B ∩ C) := by
    calc
      N omega t B =
        N omega t ((B \ C) ∪ (B ∩ C)) := by rw [hSetB]
      _ = N omega t (B \ C) + N omega t (B ∩ C) :=
        hw.2.1 t (B \ C) (B ∩ C) hDisjB
  omega
