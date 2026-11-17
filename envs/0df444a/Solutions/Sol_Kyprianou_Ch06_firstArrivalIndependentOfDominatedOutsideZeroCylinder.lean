-- Prove2me | solution 1 for Kyprianou.Ch06.firstArrivalIndependentOfDominatedOutsideZeroCylinder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T12:05:56.460719+00:00
-- url     : https://prove2.me/submissions/b11b5213-a8b4-49c2-88b9-0847c8543289

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_dominatedOutsideZeroCylinderIffSingleZeroAe
import Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfOneDisjointCount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
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
    (m : Nat) (times : Fin m → NNReal) (B : Fin m → Set E)
    (hB : ∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤)
    (u : Fin m) (hDom : ∀ i : Fin m,
      B i ⊆ B u ∧ times i ≤ times u) (t : NNReal) :
    P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
      (∀ i : Fin m, N omega (times i) (B i) = 0)} =
    P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A})} *
    P {omega | ∀ i : Fin m, N omega (times i) (B i) = 0} := by
  have hZero :=
    Kyprianou.Ch06.dominatedOutsideZeroCylinderIffSingleZeroAe
      P n N hPPP m times B u hDom
  have hCount :
      P {omega | ∀ i : Fin m, N omega (times i) (B i) = 0} =
      P {omega | N omega (times u) (B u) = 0} := by
    apply measure_congr
    filter_upwards [hZero] with omega hz
    exact propext hz
  have hEvent :
      P {omega | (t : WithTop NNReal) <
          sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
            {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
        (∀ i : Fin m, N omega (times i) (B i) = 0)} =
      P {omega | (t : WithTop NNReal) <
          sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
            {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
        N omega (times u) (B u) = 0} := by
    apply measure_congr
    filter_upwards [hZero] with omega hz
    exact propext (and_congr Iff.rfl hz)
  have hDisj : Disjoint A (B u) := by
    apply Set.disjoint_left.mpr
    intro x hxA hxB
    exact (hB u).2.1 hxB hxA
  have hOne :=
    Kyprianou.Ch06.firstArrivalIndependentOfOneDisjointCount
      P n N A firstMark hPPP hA hFA hMark
      (B u) (hB u).1 hDisj (hB u).2.2
  dsimp only at hOne
  calc
    P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
      (∀ i : Fin m, N omega (times i) (B i) = 0)} =
      P {omega | (t : WithTop NNReal) <
          sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
            {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
        N omega (times u) (B u) = 0} := hEvent
    _ = P {omega | (t : WithTop NNReal) <
          sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
            {v : NNReal | 0 < v ∧ 0 < N omega v A})} *
      P {omega | N omega (times u) (B u) = 0} :=
        hOne t (times u) 0
    _ = P {omega | (t : WithTop NNReal) <
          sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
            {v : NNReal | 0 < v ∧ 0 < N omega v A})} *
      P {omega | ∀ i : Fin m,
        N omega (times i) (B i) = 0} := by rw [hCount]
