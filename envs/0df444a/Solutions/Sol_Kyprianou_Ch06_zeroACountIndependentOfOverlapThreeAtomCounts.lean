-- Prove2me | solution 1 for Kyprianou.Ch06.zeroACountIndependentOfOverlapThreeAtomCounts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T12:21:00.11746+00:00
-- url     : https://prove2.me/submissions/e7ab1815-5dcc-4657-bdfb-5d2a08cac927

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfThreeDisjointOutsideCounts
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B C : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hFA : n A < ⊤) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (s t : NNReal) (k l q : Nat) :
    P {omega | N omega s A = 0 ∧ N omega t (B \ C) = k ∧
      N omega t (C \ B) = l ∧ N omega t (B ∩ C) = q} =
    P {omega | N omega s A = 0} *
    P {omega | N omega t (B \ C) = k ∧
      N omega t (C \ B) = l ∧ N omega t (B ∩ C) = q} := by
  have hABDiff : Disjoint A (B \ C) := by
    apply Set.disjoint_left.mpr
    intro x hxA hxD
    exact (Set.disjoint_left.mp hAB) hxA hxD.1
  have hACDiff : Disjoint A (C \ B) := by
    apply Set.disjoint_left.mpr
    intro x hxA hxD
    exact (Set.disjoint_left.mp hAC) hxA hxD.1
  have hAInter : Disjoint A (B ∩ C) := by
    apply Set.disjoint_left.mpr
    intro x hxA hxI
    exact (Set.disjoint_left.mp hAB) hxA hxI.1
  have hBCDiff : Disjoint (B \ C) (C \ B) := by
    apply Set.disjoint_left.mpr
    intro x hxB hxC
    exact hxB.2 hxC.1
  have hBDInter : Disjoint (B \ C) (B ∩ C) := by
    apply Set.disjoint_left.mpr
    intro x hxB hxI
    exact hxB.2 hxI.2
  have hCDInter : Disjoint (C \ B) (B ∩ C) := by
    apply Set.disjoint_left.mpr
    intro x hxC hxI
    exact hxC.2 hxI.1
  have hFiniteBD : n (B \ C) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.diff_subset) hFB
  have hFiniteCD : n (C \ B) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.diff_subset) hFC
  have hFiniteI : n (B ∩ C) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.inter_subset_left) hFB
  exact
    Kyprianou.Ch06.zeroACountIndependentOfThreeDisjointOutsideCounts
      P n N hPPP A (B \ C) (C \ B) (B ∩ C)
      hA (hB.diff hC) (hC.diff hB) (hB.inter hC)
      hABDiff hACDiff hAInter hBCDiff hBDInter hCDInter
      hFA hFiniteBD hFiniteCD hFiniteI s t k l q
