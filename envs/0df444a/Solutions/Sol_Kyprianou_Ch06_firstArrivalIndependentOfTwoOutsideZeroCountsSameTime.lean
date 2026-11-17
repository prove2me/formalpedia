-- Prove2me | solution 1 for Kyprianou.Ch06.firstArrivalIndependentOfTwoOutsideZeroCountsSameTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:11:18.374727+00:00
-- url     : https://prove2.me/submissions/aa5f781f-3df0-4ae8-9d1b-4991f1b083d4

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_unionMarkedCountZeroIffBothZeroAe
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
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (B C : Set E) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hFB : n B < ⊤) (hFC : n C < ⊤)
    (t u : NNReal) :
    P {omega |
      (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
      N omega u B = 0 ∧ N omega u C = 0} =
    P {omega |
      (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A})} *
    P {omega | N omega u B = 0 ∧ N omega u C = 0} := by
  have hUnionMeas : MeasurableSet (B ∪ C) := hB.union hC
  have hUnionFinite : n (B ∪ C) < ⊤ := by
    apply lt_of_le_of_lt (measure_union_le B C)
    exact ENNReal.add_lt_top.mpr ⟨hFB, hFC⟩
  have hUnionDisj : Disjoint A (B ∪ C) := by
    apply Set.disjoint_left.mpr
    intro x hxA hxUnion
    rcases hxUnion with hxB | hxC
    · exact (Set.disjoint_left.mp hAB) hxA hxB
    · exact (Set.disjoint_left.mp hAC) hxA hxC
  have hZeroAe : ∀ᵐ omega ∂P,
      (N omega u B = 0 ∧ N omega u C = 0) ↔
      N omega u (B ∪ C) = 0 := by
    filter_upwards [Kyprianou.Ch06.unionMarkedCountZeroIffBothZeroAe
      P n N hPPP B C] with omega h
    exact h u
  have hEvent :
      P {omega |
        (t : WithTop NNReal) <
          sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
            {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
        N omega u B = 0 ∧ N omega u C = 0} =
      P {omega |
        (t : WithTop NNReal) <
          sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
            {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
        N omega u (B ∪ C) = 0} := by
    apply measure_congr
    filter_upwards [hZeroAe] with omega hz
    exact propext (and_congr Iff.rfl hz)
  have hCount :
      P {omega | N omega u B = 0 ∧ N omega u C = 0} =
      P {omega | N omega u (B ∪ C) = 0} := by
    apply measure_congr
    filter_upwards [hZeroAe] with omega hz
    exact propext hz
  have hOne :=
    Kyprianou.Ch06.firstArrivalIndependentOfOneDisjointCount
      P n N A firstMark hPPP hA hFA hMark
      (B ∪ C) hUnionMeas hUnionDisj hUnionFinite
  dsimp only at hOne
  calc
    P {omega |
      (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
      N omega u B = 0 ∧ N omega u C = 0} =
      P {omega |
        (t : WithTop NNReal) <
          sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
            {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
        N omega u (B ∪ C) = 0} := hEvent
    _ = P {omega |
        (t : WithTop NNReal) <
          sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
            {v : NNReal | 0 < v ∧ 0 < N omega v A})} *
      P {omega | N omega u (B ∪ C) = 0} := hOne t u 0
    _ = P {omega |
        (t : WithTop NNReal) <
          sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
            {v : NNReal | 0 < v ∧ 0 < N omega v A})} *
      P {omega | N omega u B = 0 ∧ N omega u C = 0} := by
        rw [hCount]
