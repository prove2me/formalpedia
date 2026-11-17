-- Prove2me | solution 1 for Kyprianou.Ch06.zeroACountIndependentOfDistinctOverlappingOutsideMarkCountsAllTimes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:28:27.791967+00:00
-- url     : https://prove2.me/submissions/c0e294f0-5305-4f6d-8b8e-ae1291c33231

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfTwoNullOverlapOutsideMarksAllTimes
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfPositiveOverlapOutsideMarkCountsAllTimes
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
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B C : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hFA : n A < ⊤) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (r s t : NNReal) (k l : Nat) (hDistinct : B ≠ C)
    (hOverlap : ¬ Disjoint B C) :
    P {omega | N omega r A = 0 ∧
      N omega s B = k ∧ N omega t C = l} =
    P {omega | N omega r A = 0} *
    P {omega | N omega s B = k ∧ N omega t C = l} := by
  by_cases hNull : n (B ∩ C) = 0
  · exact
      Kyprianou.Ch06.zeroACountIndependentOfTwoNullOverlapOutsideMarksAllTimes
        P n N hPPP A B C hA hB hC hAB hAC hFA hFB hFC
        hNull r s t k l
  · exact
      Kyprianou.Ch06.zeroACountIndependentOfPositiveOverlapOutsideMarkCountsAllTimes
        P n N hPPP A B C hA hB hC hAB hAC hFA hFB hFC
        r s t k l hDistinct hOverlap hNull
