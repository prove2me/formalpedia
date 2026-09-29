-- Prove2me | solution 1 for NonmonotoneSubmod.Nonadaptive.partition_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T23:55:37.138048+00:00
-- url     : https://prove2.me/submissions/6548938d-a977-4588-b8d4-9631c9f1af16

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

theorem solution {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (A C : Finset X) :
    f C ≤ f A + f (Aᶜ ∩ C) + f (Aᶜ ∪ C) := by
  have e1 : A ∪ (Aᶜ ∩ C) = A ∪ C := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl]; tauto
  have e2 : A ∩ (Aᶜ ∩ C) = ∅ := by
    ext x; simp only [Finset.mem_inter, Finset.mem_compl, Finset.notMem_empty, iff_false]
    tauto
  have e3 : (A ∪ C) ∪ (Aᶜ ∪ C) = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_compl, Finset.mem_univ, iff_true]
    by_cases hx : x ∈ A
    · exact Or.inl (Or.inl hx)
    · exact Or.inr (Or.inl hx)
  have e4 : (A ∪ C) ∩ (Aᶜ ∪ C) = C := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_compl]
    constructor
    · rintro ⟨h1 | h1, h2 | h2⟩
      · exact absurd h1 h2
      · exact h2
      · exact h1
      · exact h1
    · intro h; exact ⟨Or.inr h, Or.inr h⟩
  have s1 := hf A (Aᶜ ∩ C)
  rw [e1, e2] at s1
  have s2 := hf (A ∪ C) (Aᶜ ∪ C)
  rw [e3, e4] at s2
  have h0 := hf0 (∅ : Finset X)
  have h1 := hf0 (Finset.univ : Finset X)
  linarith
