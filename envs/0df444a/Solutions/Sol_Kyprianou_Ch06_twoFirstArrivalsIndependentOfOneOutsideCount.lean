-- Prove2me | solution 1 for Kyprianou.Ch06.twoFirstArrivalsIndependentOfOneOutsideCount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:25:29.908691+00:00
-- url     : https://prove2.me/submissions/05b23350-4a32-4f55-a275-02f53b5a7c4d

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_twoFirstArrivalsAndOutsideCountJointZeroIdentity
import Theorems.Thm_Kyprianou_Ch06_disjointTwoZeroCountsIndependentOfOutsideCount
import Theorems.Thm_Kyprianou_Ch06_firstArrivalTwoDisjointJointSurvivalIsZeroCount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B D C : Set E)
    (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hC : MeasurableSet C)
    (hBD : Disjoint B D) (hBC : Disjoint B C)
    (hDC : Disjoint D C)
    (hFB : n B < ⊤) (hFD : n D < ⊤) (hFC : n C < ⊤)
    (s t u : NNReal) (k : Nat) :
    P {omega |
      (s : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v B}) ∧
      (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v D}) ∧
      N omega u C = k} =
    P {omega | (s : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v B}) ∧
      (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v D})} *
      P {omega | N omega u C = k} := by
  rw [Kyprianou.Ch06.twoFirstArrivalsAndOutsideCountJointZeroIdentity
        P n N hPPP B D C hB hD hC hBD hBC hDC
        hFB hFD hFC s t u k,
      Kyprianou.Ch06.disjointTwoZeroCountsIndependentOfOutsideCount
        P n N hPPP B D C hB hD hC hBD hBC hDC
        hFB hFD hFC s t u k,
      ← Kyprianou.Ch06.firstArrivalTwoDisjointJointSurvivalIsZeroCount
        P n N hPPP B D hB hD hBD hFB hFD s t]
