-- Prove2me | solution 1 for NonmonotoneSubmod.LocalSearch.lemma_3_1_local_optimum
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:16:12.751985+00:00
-- url     : https://prove2.me/submissions/82e3007e-5b7b-4229-8d9a-b37a1386dab2

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_LocalSearch_IsLocalOptimum

namespace NonmonotoneSubmod.LocalSearch

theorem aux_l31_insert_le {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (S : Finset X) (hS : IsLocalOptimum f S) (a : X) : f (insert a S) ≤ f S := by
  by_cases ha : a ∈ S
  · rw [Finset.insert_eq_of_mem ha]
  · exact hS.1 a ha

theorem aux_l31_erase_le {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (S : Finset X) (hS : IsLocalOptimum f S) (a : X) : f (S.erase a) ≤ f S := by
  by_cases ha : a ∈ S
  · exact hS.2 a ha
  · rw [Finset.erase_eq_of_notMem ha]

theorem aux_l31_union {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (S : Finset X) (hS : IsLocalOptimum f S)
    (A : Finset X) : f (S ∪ A) ≤ f S := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A haA ih =>
    have h := hf (S ∪ A) (insert a S)
    have h1 : S ∪ A ∪ insert a S = S ∪ insert a A := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    have h2 : (S ∪ A) ∩ insert a S = S := by
      ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨hx | hx, hx' | hx'⟩
        · exact hx
        · exact hx'
        · subst hx'; exact absurd hx haA
        · exact hx'
      · intro hx; exact ⟨Or.inl hx, Or.inr hx⟩
    rw [h1, h2] at h
    have := aux_l31_insert_le f S hS a
    linarith

theorem aux_l31_sdiff {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (S : Finset X) (hS : IsLocalOptimum f S)
    (A : Finset X) : f (S \ A) ≤ f S := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A haA ih =>
    have h := hf (S \ A) (S.erase a)
    have h1 : S \ A ∪ S.erase a = S := by
      ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_erase]
      constructor
      · rintro (⟨hx, _⟩ | ⟨_, hx⟩) <;> exact hx
      · intro hx
        by_cases hxa : x = a
        · subst hxa; exact Or.inl ⟨hx, haA⟩
        · exact Or.inr ⟨hxa, hx⟩
    have h2 : S \ A ∩ S.erase a = S \ insert a A := by
      ext x; simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
      tauto
    rw [h1, h2] at h
    have := aux_l31_erase_le f S hS a
    linarith

end NonmonotoneSubmod.LocalSearch

open NonmonotoneSubmod.LocalSearch

theorem solution {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (S : Finset X) (hS : IsLocalOptimum f S) (T : Finset X)
    (hT : T ⊆ S ∨ S ⊆ T) :
    f T ≤ f S := by
  rcases hT with hT | hT
  · have := aux_l31_sdiff f hf S hS (S \ T)
    rwa [Finset.sdiff_sdiff_eq_self hT] at this
  · have := aux_l31_union f hf S hS (T \ S)
    rwa [Finset.union_sdiff_of_subset hT] at this
