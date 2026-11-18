-- Prove2me | solution 1 for Kyprianou.Ch06.positiveSingletonMarkedCountForcesRegionCount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:44:18.121413+00:00
-- url     : https://prove2.me/submissions/ab39bc26-d37c-473d-9c37-3ed5f6d2aae6

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
set_option autoImplicit false

theorem solution
    {Omega E : Type}
    (N : Omega → NNReal → Set E → Nat)
    (omega : Omega) (t : NNReal)
    (x : E) (D : Set E) (hx : x ∈ D)
    (hAdd : ∀ A B : Set E, Disjoint A B →
      N omega t (A ∪ B) = N omega t A + N omega t B)
    (hPositive : 0 < N omega t ({x} : Set E)) :
    0 < N omega t D := by
  have hDisj : Disjoint ({x} : Set E) (D \ {x}) := by
    apply Set.disjoint_left.mpr
    intro y hy hz
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    exact hz.2 (by simp)
  have hUnion : ({x} : Set E) ∪ (D \ {x}) = D := by
    ext y
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_diff]
    constructor
    · rintro (rfl | ⟨hy, _⟩)
      · exact hx
      · exact hy
    · intro hy
      by_cases heq : y = x
      · exact Or.inl heq
      · exact Or.inr ⟨hy, by simpa using heq⟩
  have hCount := hAdd {x} (D \ {x}) hDisj
  rw [hUnion] at hCount
  omega
