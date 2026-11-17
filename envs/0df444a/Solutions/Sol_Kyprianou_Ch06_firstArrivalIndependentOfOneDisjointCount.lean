-- Prove2me | solution 1 for Kyprianou.Ch06.firstArrivalIndependentOfOneDisjointCount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:36:00.503953+00:00
-- url     : https://prove2.me/submissions/236f48cf-c368-4e44-bd89-30e9d57a797f

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstArrivalJointEventFromContinuousZeroCount
import Theorems.Thm_Kyprianou_Ch06_disjointMarkedPoissonZeroCountJointContinuous
import Theorems.Thm_Kyprianou_Ch06_disjointMarkedPoissonCountIndependence
import Theorems.Thm_Kyprianou_Ch06_markedPoissonArrivalSurvival
import Theorems.Thm_Kyprianou_Ch06_markedPoissonMarginalCountLaw
import Theorems.Thm_Kyprianou_Ch06_poissonZeroCountAsExponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open Kyprianou.Ch06
open scoped NNReal ENNReal
set_option autoImplicit false

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
        0 < N omega (sigma.untopD 0) {x}))
    (B : Set E) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (hFiniteB : n B < ⊤) :
    let sigma : Omega → WithTop NNReal := fun omega =>
      sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
        {v : NNReal | 0 < v ∧ 0 < N omega v A})
    ∀ (t u : NNReal) (k : Nat),
      P {omega | (t : WithTop NNReal) < sigma omega ∧ N omega u B = k} =
      P {omega | (t : WithTop NNReal) < sigma omega} *
        P {omega | N omega u B = k}
 := by
  dsimp only
  intro t u k
  have hInit : ∀ᵐ omega ∂P, N omega 0 A = 0 := by
    filter_upwards [hPPP.2.1] with omega h
    exact h.1 A
  have hMono : ∀ᵐ omega ∂P,
      Monotone (fun s : NNReal => N omega s A) := by
    filter_upwards [hPPP.2.1] with omega h
    exact h.2.2 A
  have hCont :
      ContinuousAt (fun s : NNReal =>
        P {omega | N omega s A = 0 ∧ N omega u B = k}) t :=
    Kyprianou.Ch06.disjointMarkedPoissonZeroCountJointContinuous
      P n N hPPP A B hA hB hAB hFinite hFiniteB t u k
  have hJoint :=
    Kyprianou.Ch06.firstArrivalJointEventFromContinuousZeroCount
      P N A {omega | N omega u B = k} t hInit hMono hCont
  have hCount :=
    Kyprianou.Ch06.disjointMarkedPoissonCountIndependence
      P n N hPPP A B hA hB hAB hFinite hFiniteB t u 0 k
  have hMarg : P {omega | N omega t A = 0} =
      P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A})} := by
    have hFirst :=
      Kyprianou.Ch06.markedPoissonArrivalSurvival
        P n N A firstMark hPPP hA hFinite hMark
    dsimp only at hFirst
    calc
      P {omega | N omega t A = 0} =
          ProbabilityTheory.poissonMeasure
            (t * (n A).toNNReal) {0} :=
              Kyprianou.Ch06.markedPoissonMarginalCountLaw
                P n N hPPP t A hA hFinite 0
      _ = ENNReal.ofReal
          (Real.exp (-((n A).toReal * (t : Real)))) := by
            simpa [ENNReal.toReal] using
              (Kyprianou.Ch06.poissonZeroCountAsExponential
                (n A).toNNReal t)
      _ = P {omega | (t : WithTop NNReal) <
          sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
            {v : NNReal | 0 < v ∧ 0 < N omega v A})} := by
        simpa using (hFirst t).symm
  calc
    P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
        N omega u B = k} =
      P {omega | N omega t A = 0 ∧ N omega u B = k} := hJoint
    _ = P {omega | N omega t A = 0} *
      P {omega | N omega u B = k} := hCount
    _ = P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A})} *
      P {omega | N omega u B = k} := by
        rw [hMarg]
