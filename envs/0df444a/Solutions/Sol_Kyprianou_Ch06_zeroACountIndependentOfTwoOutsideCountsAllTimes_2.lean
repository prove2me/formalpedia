-- Prove2me | solution 2 for Kyprianou.Ch06.zeroACountIndependentOfTwoOutsideCountsAllTimes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:44:27.014403+00:00
-- url     : https://prove2.me/submissions/25327e54-fc23-4d01-848e-5088f62d4eae

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfTwoOutsideCountsOrderedTimes
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
    (r s t : NNReal) (k l : Nat) :
    P {omega | N omega r A = 0 ∧
      N omega s B = k ∧ N omega t C = l} =
    P {omega | N omega r A = 0} *
    P {omega | N omega s B = k ∧ N omega t C = l} := by
  rcases le_total s t with hst | hts
  · exact
      Kyprianou.Ch06.zeroACountIndependentOfTwoOutsideCountsOrderedTimes
        P n N hPPP A B C hA hB hC hAB hAC hFA hFB hFC
        r s t hst k l
  · have hReverse :=
      Kyprianou.Ch06.zeroACountIndependentOfTwoOutsideCountsOrderedTimes
        P n N hPPP A C B hA hC hB hAC hAB hFA hFC hFB
        r t s hts l k
    simpa only [and_comm, and_left_comm, and_assoc] using hReverse
