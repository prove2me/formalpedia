-- Prove2me | solution 1 for Kyprianou.Ch06.firstArrivalIndependentOfEventFromZeroCountIndependence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:05:53.094204+00:00
-- url     : https://prove2.me/submissions/43253b3d-3837-4e95-ac31-00fc7cdf60e9

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_jointEventContinuousFromExponentialFactorisation
import Theorems.Thm_Kyprianou_Ch06_firstArrivalJointEventFromContinuousZeroCount
import Theorems.Thm_Kyprianou_Ch06_zeroCountEqualsFirstArrivalSurvivalProbability
import Theorems.Thm_Kyprianou_Ch06_markedPoissonMarginalCountLaw
import Theorems.Thm_Kyprianou_Ch06_poissonZeroCountAsExponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch06
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
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (D : Set Omega)
    (hJoint : ∀ s : NNReal,
      P ({omega | N omega s A = 0} ∩ D) =
      P {omega | N omega s A = 0} * P D)
    (t : NNReal) :
    P ({omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A})} ∩ D) =
    P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A})} * P D := by
  let f : NNReal → Set Omega := fun s => {omega | N omega s A = 0}
  have hZero : ∀ s : NNReal,
      P (f s) =
        ENNReal.ofReal (Real.exp (-((n A).toReal * (s : Real)))) := by
    intro s
    calc
      P (f s) =
        ProbabilityTheory.poissonMeasure
          (s * (n A).toNNReal) {0} :=
          Kyprianou.Ch06.markedPoissonMarginalCountLaw
            P n N hPPP s A hA hFA 0
      _ = ENNReal.ofReal
        (Real.exp (-((n A).toReal * (s : Real)))) := by
          simpa [ENNReal.toReal] using
            (Kyprianou.Ch06.poissonZeroCountAsExponential
              (n A).toNNReal s)
  have hCont :
      ContinuousAt (fun s : NNReal => P ((f s) ∩ D)) t :=
    Kyprianou.Ch06.jointEventContinuousFromExponentialFactorisation
      P D (n A).toReal f hZero hJoint t
  have hInit : ∀ᵐ omega ∂P, N omega 0 A = 0 := by
    filter_upwards [hPPP.2.1] with omega hw
    exact hw.1 A
  have hMono : ∀ᵐ omega ∂P,
      Monotone (fun s : NNReal => N omega s A) := by
    filter_upwards [hPPP.2.1] with omega hw
    exact hw.2.2 A
  have hBridge :=
    Kyprianou.Ch06.firstArrivalJointEventFromContinuousZeroCount
      P N A D t hInit hMono hCont
  have hSurv :=
    Kyprianou.Ch06.zeroCountEqualsFirstArrivalSurvivalProbability
      P n N A firstMark hPPP hA hFA hMark t
  calc
    P ({omega | (t : WithTop NNReal) <
      sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
        {v : NNReal | 0 < v ∧ 0 < N omega v A})} ∩ D) =
      P ((f t) ∩ D) := hBridge
    _ = P (f t) * P D := hJoint t
    _ = P {omega | (t : WithTop NNReal) <
      sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
        {v : NNReal | 0 < v ∧ 0 < N omega v A})} * P D := by
          rw [← hSurv]
