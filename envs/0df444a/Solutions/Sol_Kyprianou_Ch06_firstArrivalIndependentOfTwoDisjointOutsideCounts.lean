-- Prove2me | solution 1 for Kyprianou.Ch06.firstArrivalIndependentOfTwoDisjointOutsideCounts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:45:59.972536+00:00
-- url     : https://prove2.me/submissions/d2caf137-acde-4cbb-a6fa-9c49b2104a60

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_twoOutsideJointZeroCountContinuous
import Theorems.Thm_Kyprianou_Ch06_firstArrivalJointEventFromContinuousZeroCount
import Theorems.Thm_Kyprianou_Ch06_markedPoissonMarginalCountLaw
import Theorems.Thm_Kyprianou_Ch06_poissonZeroCountAsExponential
import Theorems.Thm_Kyprianou_Ch06_zeroCountEqualsFirstArrivalSurvivalProbability
import Theorems.Thm_Kyprianou_Ch06_threeDisjointZeroCountFactorisation
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
    (B C : Set E) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (t u v : NNReal) (k l : Nat) :
    P {omega |
      (t : WithTop NNReal) <
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A}) ∧
      N omega u B = k ∧ N omega v C = l} =
    P {omega |
      (t : WithTop NNReal) <
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A})} *
    P {omega | N omega u B = k ∧ N omega v C = l} := by
  have hInit : ∀ᵐ omega ∂P, N omega 0 A = 0 := by
    filter_upwards [hPPP.2.1] with omega h
    exact h.1 A
  have hMono : ∀ᵐ omega ∂P,
      Monotone (fun s : NNReal => N omega s A) := by
    filter_upwards [hPPP.2.1] with omega h
    exact h.2.2 A
  have hCont :=
    Kyprianou.Ch06.twoOutsideJointZeroCountContinuous
      P n N hPPP A B C hA hB hC hAB hAC hBC
      hFA hFB hFC t u v k l
  have hJoint :=
    Kyprianou.Ch06.firstArrivalJointEventFromContinuousZeroCount
      P N A {omega | N omega u B = k ∧ N omega v C = l}
      t hInit hMono hCont
  have hMarg :=
    Kyprianou.Ch06.zeroCountEqualsFirstArrivalSurvivalProbability
      P n N A firstMark hPPP hA hFA hMark t
  calc
    P {omega | (t : WithTop NNReal) <
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A}) ∧
        N omega u B = k ∧ N omega v C = l} =
      P {omega | N omega t A = 0 ∧ N omega u B = k ∧
        N omega v C = l} := by
          simpa only [Set.mem_setOf_eq, and_assoc] using hJoint
    _ = P {omega | N omega t A = 0} *
        P {omega | N omega u B = k ∧ N omega v C = l} :=
      Kyprianou.Ch06.threeDisjointZeroCountFactorisation
        P n N hPPP A B C hA hB hC hAB hAC hBC
        hFA hFB hFC t u v k l
    _ = P {omega | (t : WithTop NNReal) <
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A})} *
        P {omega | N omega u B = k ∧ N omega v C = l} := by
          rw [hMarg]
