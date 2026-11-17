-- Prove2me | solution 1 for Kyprianou.Ch06.markedPoissonCountMonotoneInMarksAllTimesAe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T11:57:02.507403+00:00
-- url     : https://prove2.me/submissions/8e1e412c-1dda-45a8-8d6d-20e3cb515876

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N) :
    ∀ᵐ omega ∂P, ∀ (B C : Set E), B ⊆ C →
      ∀ t : NNReal, N omega t B ≤ N omega t C := by
  filter_upwards [hPPP.2.1] with omega hw
  intro B C hBC t
  have hDisj : Disjoint B (C \ B) := by
    apply Set.disjoint_left.mpr
    intro x hxB hxCB
    exact hxCB.2 hxB
  have hUnion : B ∪ (C \ B) = C := by
    ext x
    simp only [Set.mem_union, Set.mem_diff]
    constructor
    · rintro (hxB | hxCB)
      · exact hBC hxB
      · exact hxCB.1
    · intro hxC
      by_cases hxB : x ∈ B
      · exact Or.inl hxB
      · exact Or.inr ⟨hxC, hxB⟩
  have hAdd : N omega t C =
      N omega t B + N omega t (C \ B) := by
    calc
      N omega t C = N omega t (B ∪ (C \ B)) := by rw [hUnion]
      _ = N omega t B + N omega t (C \ B) :=
        hw.2.1 t B (C \ B) hDisj
  omega
