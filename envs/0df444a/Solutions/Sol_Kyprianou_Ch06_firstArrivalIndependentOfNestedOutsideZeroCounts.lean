-- Prove2me | solution 1 for Kyprianou.Ch06.firstArrivalIndependentOfNestedOutsideZeroCounts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T11:56:55.437233+00:00
-- url     : https://prove2.me/submissions/509ad101-a7f5-4669-92c5-062d0fe581a7

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_markedPoissonCountMonotoneSpaceTimeAe
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
    (B C : Set E) (hC : MeasurableSet C)
    (hAC : Disjoint A C) (hFC : n C < ⊤)
    (hBC : B ⊆ C) (s u t : NNReal) (hsu : s ≤ u) :
    P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
      N omega s B = 0 ∧ N omega u C = 0} =
    P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A})} *
    P {omega | N omega s B = 0 ∧ N omega u C = 0} := by
  have hZero : ∀ᵐ omega ∂P,
      (N omega s B = 0 ∧ N omega u C = 0) ↔
      N omega u C = 0 := by
    filter_upwards [Kyprianou.Ch06.markedPoissonCountMonotoneSpaceTimeAe
      P n N hPPP B C hBC s u hsu] with omega hLe
    constructor
    · exact And.right
    · intro h
      constructor
      · omega
      · exact h
  have hJoint :
      P {omega | (t : WithTop NNReal) <
          sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
            {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
          N omega s B = 0 ∧ N omega u C = 0} =
      P {omega | (t : WithTop NNReal) <
          sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
            {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
          N omega u C = 0} := by
    apply measure_congr
    filter_upwards [hZero] with omega hz
    exact propext (and_congr Iff.rfl hz)
  have hCount :
      P {omega | N omega s B = 0 ∧ N omega u C = 0} =
        P {omega | N omega u C = 0} := by
    apply measure_congr
    filter_upwards [hZero] with omega hz
    exact propext hz
  have hSingle :=
    Kyprianou.Ch06.firstArrivalIndependentOfOneDisjointCount
      P n N A firstMark hPPP hA hFA hMark C hC hAC hFC
  dsimp only at hSingle
  calc
    P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
      N omega s B = 0 ∧ N omega u C = 0} =
      P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
        N omega u C = 0} := hJoint
    _ = P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A})} *
        P {omega | N omega u C = 0} := hSingle t u 0
    _ = P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A})} *
        P {omega | N omega s B = 0 ∧ N omega u C = 0} := by
          rw [hCount]
