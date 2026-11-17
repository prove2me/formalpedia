-- Prove2me | solution 1 for Kyprianou.Ch06.firstArrivalIndependentOfArbitraryDisjointOutsideCylinder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:05:38.21651+00:00
-- url     : https://prove2.me/submissions/c38fccfb-b930-4f7d-8b9d-24f4b4f78e0e

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfDisjointOutsideCylinder
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
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (m : Nat) (times : Fin m → NNReal)
    (B : Fin m → Set E) (counts : Fin m → Nat)
    (hB : ∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤)
    (hDisj : ∀ i j : Fin m, i ≠ j → Disjoint (B i) (B j))
    (t : NNReal) :
    P {omega |
      (t : WithTop NNReal) <
        sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u A}) ∧
      ∀ i : Fin m, N omega (times i) (B i) = counts i} =
    P {omega |
      (t : WithTop NNReal) <
        sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u A})} *
    P {omega | ∀ i : Fin m, N omega (times i) (B i) = counts i} := by
  let D : Set Omega := {omega |
    ∀ i : Fin m, N omega (times i) (B i) = counts i}
  let f : NNReal → Set Omega := fun s =>
    {omega | N omega s A = 0}
  have hB' : ∀ i, MeasurableSet (B i) ∧ n (B i) < ⊤ := by
    intro i
    exact ⟨(hB i).1, (hB i).2.2⟩
  have hAB : ∀ i, Disjoint A (B i) := by
    intro i
    apply Set.disjoint_left.mpr
    intro x hxA hxB
    exact (hB i).2.1 hxB hxA
  have hJoint : ∀ s : NNReal,
      P ((f s) ∩ D) = P (f s) * P D := by
    intro s
    exact Kyprianou.Ch06.zeroACountIndependentOfDisjointOutsideCylinder
      P n N hPPP A hA hFA m times B counts hB' hAB hDisj s
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
  have hFact := hJoint t
  have hSurv :=
    Kyprianou.Ch06.zeroCountEqualsFirstArrivalSurvivalProbability
      P n N A firstMark hPPP hA hFA hMark t
  change P ({omega |
    (t : WithTop NNReal) <
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u A})} ∩ D) =
    P {omega |
      (t : WithTop NNReal) <
        sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u A})} * P D
  calc
    P ({omega |
      (t : WithTop NNReal) <
        sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u A})} ∩ D) =
      P ((f t) ∩ D) := hBridge
    _ = P (f t) * P D := hFact
    _ = P {omega |
      (t : WithTop NNReal) <
        sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u A})} * P D := by
        rw [← hSurv]
