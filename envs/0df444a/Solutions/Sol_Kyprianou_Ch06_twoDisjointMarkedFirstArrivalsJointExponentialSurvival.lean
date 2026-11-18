-- Prove2me | solution 1 for Kyprianou.Ch06.twoDisjointMarkedFirstArrivalsJointExponentialSurvival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:09:35.787985+00:00
-- url     : https://prove2.me/submissions/ea7769fe-72f7-4845-8b54-811db6b98cfd

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstArrivalTwoDisjointJointSurvivalIsZeroCount
import Theorems.Thm_Kyprianou_Ch06_disjointMarkedZeroCountsJointExponential
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
    (B D : Set E) (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hBD : Disjoint B D) (hFB : n B < ⊤) (hFD : n D < ⊤)
    (s t : NNReal) :
    P {omega |
      (s : WithTop NNReal) <
        sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u B}) ∧
      (t : WithTop NNReal) <
        sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u D})} =
    ENNReal.ofReal
      (Real.exp (-(((n B).toNNReal : Real) * (s : Real)))) *
    ENNReal.ofReal
      (Real.exp (-(((n D).toNNReal : Real) * (t : Real)))) := by
  rw [Kyprianou.Ch06.firstArrivalTwoDisjointJointSurvivalIsZeroCount
        P n N hPPP B D hB hD hBD hFB hFD s t,
      Kyprianou.Ch06.disjointMarkedZeroCountsJointExponential
        P n N hPPP B D hB hD hBD hFB hFD s t]
