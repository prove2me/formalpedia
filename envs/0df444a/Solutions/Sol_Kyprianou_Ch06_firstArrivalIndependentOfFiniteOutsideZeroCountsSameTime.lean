-- Prove2me | solution 1 for Kyprianou.Ch06.firstArrivalIndependentOfFiniteOutsideZeroCountsSameTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T11:50:42.152199+00:00
-- url     : https://prove2.me/submissions/4050acec-816a-4529-b927-3a452f7162cf

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_finiteUnionMarkedIntensityFinite
import Theorems.Thm_Kyprianou_Ch06_finiteUnionMarkedCountZeroIffAllZeroAe
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
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (m : Nat) (B : Fin m → Set E)
    (hB : ∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤)
    (t u : NNReal) :
    P {omega | (t : WithTop NNReal) <
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A}) ∧
      ∀ i : Fin m, N omega u (B i) = 0} =
    P {omega | (t : WithTop NNReal) <
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A})} *
    P {omega | ∀ i : Fin m, N omega u (B i) = 0} := by
  let U : Set E := ⋃ i : Fin m, B i
  have hB' : ∀ i, MeasurableSet (B i) ∧ n (B i) < ⊤ := by
    intro i
    exact ⟨(hB i).1, (hB i).2.2⟩
  have hUF :=
    Kyprianou.Ch06.finiteUnionMarkedIntensityFinite n m B hB'
  have hAU : Disjoint A U := by
    apply Set.disjoint_left.mpr
    intro x hxA hxU
    change x ∈ ⋃ i, B i at hxU
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
    exact (hB i).2.1 hi hxA
  have hZero : ∀ᵐ omega ∂P,
      (∀ i : Fin m, N omega u (B i) = 0) ↔
      N omega u U = 0 := by
    filter_upwards [Kyprianou.Ch06.finiteUnionMarkedCountZeroIffAllZeroAe
      P n N hPPP m B] with omega h
    exact h u
  have hEvent :
      P {omega | (t : WithTop NNReal) <
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A}) ∧
        ∀ i : Fin m, N omega u (B i) = 0} =
      P {omega | (t : WithTop NNReal) <
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A}) ∧
        N omega u U = 0} := by
    apply measure_congr
    filter_upwards [hZero] with omega hz
    exact propext (and_congr Iff.rfl hz)
  have hCount :
      P {omega | ∀ i : Fin m, N omega u (B i) = 0} =
        P {omega | N omega u U = 0} := by
    apply measure_congr
    filter_upwards [hZero] with omega hz
    exact propext hz
  have hOne :=
    Kyprianou.Ch06.firstArrivalIndependentOfOneDisjointCount
      P n N A firstMark hPPP hA hFA hMark U hUF.1 hAU hUF.2
  dsimp only at hOne
  calc
    P {omega | (t : WithTop NNReal) <
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A}) ∧
        ∀ i : Fin m, N omega u (B i) = 0} =
      P {omega | (t : WithTop NNReal) <
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A}) ∧
        N omega u U = 0} := hEvent
    _ = P {omega | (t : WithTop NNReal) <
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A})} *
        P {omega | N omega u U = 0} := hOne t u 0
    _ = P {omega | (t : WithTop NNReal) <
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A})} *
        P {omega | ∀ i : Fin m, N omega u (B i) = 0} := by rw [hCount]
