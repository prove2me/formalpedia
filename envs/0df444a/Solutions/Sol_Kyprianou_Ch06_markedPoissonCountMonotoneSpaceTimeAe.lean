-- Prove2me | solution 1 for Kyprianou.Ch06.markedPoissonCountMonotoneSpaceTimeAe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T11:56:46.892996+00:00
-- url     : https://prove2.me/submissions/09ea1e53-5a11-4397-ba02-6926c368ca09

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
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B C : Set E) (hBC : B ⊆ C)
    (s t : NNReal) (hst : s ≤ t) :
    ∀ᵐ omega ∂P, N omega s B ≤ N omega t C := by
  filter_upwards [hPPP.2.1] with omega hw
  have hDisj : Disjoint B (C \ B) := by
    apply Set.disjoint_left.mpr
    intro x hxB hxCB
    exact hxCB.2 hxB
  have hUnion : B ∪ (C \ B) = C := by
    ext x
    simp only [Set.mem_union, Set.mem_diff]
    constructor
    · rintro (h | h)
      · exact hBC h
      · exact h.1
    · intro h
      by_cases hx : x ∈ B
      · exact Or.inl hx
      · exact Or.inr ⟨h, hx⟩
  have hAdd := hw.2.1 t B (C \ B) hDisj
  have hSpace : N omega t B ≤ N omega t C := by
    have hCountC : N omega t C =
        N omega t B + N omega t (C \ B) := by
      calc
        N omega t C = N omega t (B ∪ (C \ B)) := by rw [hUnion]
        _ = N omega t B + N omega t (C \ B) := hAdd
    omega
  exact (hw.2.2 B hst).trans hSpace
