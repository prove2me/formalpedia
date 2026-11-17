-- Prove2me | solution 1 for Kyprianou.Ch06.zeroCountEqualsFirstArrivalSurvivalProbability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:45:25.887292+00:00
-- url     : https://prove2.me/submissions/3bde8a92-6d84-46b2-b5a7-3a772601bff7

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_markedPoissonArrivalSurvival
import Theorems.Thm_Kyprianou_Ch06_markedPoissonMarginalCountLaw
import Theorems.Thm_Kyprianou_Ch06_poissonZeroCountAsExponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A) (hFA : n A < ⊤)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (t : NNReal) :
    P {omega | N omega t A = 0} =
      P {omega | (t : WithTop NNReal) <
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A})} := by
    have hFirst :=
      Kyprianou.Ch06.markedPoissonArrivalSurvival
        P n N A firstMark hPPP hA hFA hMark
    dsimp only at hFirst
    calc
      P {omega | N omega t A = 0} =
        ProbabilityTheory.poissonMeasure (t * (n A).toNNReal) {0} :=
          Kyprianou.Ch06.markedPoissonMarginalCountLaw
            P n N hPPP t A hA hFA 0
      _ = ENNReal.ofReal (Real.exp (-((n A).toReal * (t : Real)))) := by
        simpa [ENNReal.toReal] using
          (Kyprianou.Ch06.poissonZeroCountAsExponential
            (n A).toNNReal t)
      _ = P {omega | (t : WithTop NNReal) <
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A})} := by
        simpa using (hFirst t).symm
