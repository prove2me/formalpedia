-- Prove2me | solution 1 for Kyprianou.Ch06.markedPoissonArrivalSurvival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:05:05.912273+00:00
-- url     : https://prove2.me/submissions/18786ed9-cfa4-4edf-b708-65f076daf6b0

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_markedPoissonMarginalCountLaw
import Theorems.Thm_Kyprianou_Ch06_arrivalSurvivalUpperBound
import Theorems.Thm_Kyprianou_Ch06_arrivalSurvivalLowerBound
import Theorems.Thm_Kyprianou_Ch06_rightContinuousSandwich
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch06

theorem Kyprianou.Ch06.poissonZeroCountAsExponential
    (rate t : NNReal) :
    ProbabilityTheory.poissonMeasure (t * rate) {0} =
      ENNReal.ofReal
        (Real.exp (-((rate : Real) * (t : Real)))) := by
  simp [ProbabilityTheory.poissonMeasure_singleton, mul_comm]

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A)
    (hFinite : n A < ⊤)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x})) :
    let sigma : Omega → WithTop NNReal := fun omega =>
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A})
    (∀ t : NNReal,
      P {omega | (t : WithTop NNReal) < sigma omega} =
        ENNReal.ofReal
          (Real.exp (-((n A).toReal * (t : Real))))) := by
  dsimp only
  intro t
  let F : NNReal → ENNReal := fun s =>
    ENNReal.ofReal (Real.exp (-((n A).toReal * (s : Real))))
  have hZeroFormula : ∀ s : NNReal,
      P {omega | N omega s A = 0} = F s := by
    intro s
    calc
      P {omega | N omega s A = 0} =
          ProbabilityTheory.poissonMeasure
            (s * (n A).toNNReal) {0} := by
        exact Kyprianou.Ch06.markedPoissonMarginalCountLaw
          P n N hPPP s A hA hFinite 0
      _ = F s := by
        simpa [F, ENNReal.toReal] using
          (Kyprianou.Ch06.poissonZeroCountAsExponential
            (n A).toNNReal s)
  have hF : ContinuousAt F t := by
    apply Continuous.continuousAt
    dsimp [F]
    exact ENNReal.continuous_ofReal.comp (by fun_prop)
  have hInit : ∀ᵐ omega ∂P, N omega 0 A = 0 := by
    filter_upwards [hPPP.2.1] with omega h
    exact h.1 A
  have hMono : ∀ᵐ omega ∂P,
      Monotone (fun s : NNReal => N omega s A) := by
    filter_upwards [hPPP.2.1] with omega h
    exact h.2.2 A
  have hUpper :
      P {omega | (t : WithTop NNReal) <
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A})} ≤ F t := by
    rw [← hZeroFormula t]
    exact Kyprianou.Ch06.arrivalSurvivalUpperBound
      P N A hInit t
  have hLower : ∀ s : NNReal, t < s →
      F s ≤ P {omega | (t : WithTop NNReal) <
        sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u A})} := by
    intro s hts
    rw [← hZeroFormula s]
    exact Kyprianou.Ch06.arrivalSurvivalLowerBound
      P N A hMono s t hts
  have hEq :=
    Kyprianou.Ch06.rightContinuousSandwich F t
      (P {omega | (t : WithTop NNReal) <
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A})})
      hF hUpper hLower
  simpa only [F] using hEq
