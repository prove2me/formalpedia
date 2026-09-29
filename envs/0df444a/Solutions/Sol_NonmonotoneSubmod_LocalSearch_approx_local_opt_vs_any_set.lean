-- Prove2me | solution 1 for NonmonotoneSubmod.LocalSearch.approx_local_opt_vs_any_set
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:46:16.016649+00:00
-- url     : https://prove2.me/submissions/12ac8008-e0f8-4cc8-ad63-c85f06344622

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_LocalSearch_IsApproxLocalOptimum

namespace NonmonotoneSubmod.LocalSearch

theorem aux_alvs_down {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (α : ℝ) (S : Finset X) (hS : IsApproxLocalOptimum f α S) :
    ∀ D : Finset X, D ⊆ S → f (S \ D) ≤ (1 + (D.card : ℝ) * α) * f S := by
  intro D
  induction D using Finset.induction_on with
  | empty => intro _; simp
  | @insert a D ha ih =>
    intro hD
    have haS : a ∈ S := hD (Finset.mem_insert_self a D)
    have hD' : D ⊆ S := fun x hx => hD (Finset.mem_insert_of_mem hx)
    have h1 := ih hD'
    have h2 := hS.1 a haS
    have h3 := hf (S \ D) (S.erase a)
    have hu : S \ D ∪ S.erase a = S := by
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_erase]
      constructor
      · rintro (⟨h, _⟩ | ⟨_, h⟩) <;> exact h
      · intro hx
        by_cases hxa : x = a
        · subst hxa; exact Or.inl ⟨hx, ha⟩
        · exact Or.inr ⟨hxa, hx⟩
    have hi : S \ D ∩ S.erase a = S \ insert a D := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
      tauto
    rw [hu, hi] at h3
    rw [Finset.card_insert_of_notMem ha]
    push_cast
    linarith

theorem aux_alvs_up {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (α : ℝ) (S : Finset X) (hS : IsApproxLocalOptimum f α S) :
    ∀ D : Finset X, Disjoint D S → f (S ∪ D) ≤ (1 + (D.card : ℝ) * α) * f S := by
  intro D
  induction D using Finset.induction_on with
  | empty => intro _; simp
  | @insert a D ha ih =>
    intro hD
    have haS : a ∉ S := Finset.disjoint_left.mp hD (Finset.mem_insert_self a D)
    have hD' : Disjoint D S :=
      Finset.disjoint_left.mpr fun x hx => Finset.disjoint_left.mp hD (Finset.mem_insert_of_mem hx)
    have h1 := ih hD'
    have h2 := hS.2 a haS
    have h3 := hf (S ∪ D) (insert a S)
    have hu : S ∪ D ∪ insert a S = S ∪ insert a D := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    have hi : (S ∪ D) ∩ insert a S = S := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert]
      constructor
      · rintro ⟨hx1, hx2 | hx2⟩
        · subst hx2
          rcases hx1 with h | h
          · exact absurd h haS
          · exact absurd h ha
        · exact hx2
      · intro hx; exact ⟨Or.inl hx, Or.inr hx⟩
    rw [hu, hi] at h3
    rw [Finset.card_insert_of_notMem ha]
    push_cast
    linarith

end NonmonotoneSubmod.LocalSearch

open NonmonotoneSubmod.LocalSearch

theorem solution {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S : Finset X, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (α : ℝ) (hα : 0 ≤ α) (S : Finset X) (hS : IsApproxLocalOptimum f α S) (C : Finset X) :
    f C ≤ 2 * (1 + (Fintype.card X : ℝ) * α) * f S + f Sᶜ := by
  have h1 := hf (C ∩ S) (C \ S)
  have e1 : C ∩ S ∪ C \ S = C := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have e2 : C ∩ S ∩ (C \ S) = ∅ := by
    ext x; simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.notMem_empty, iff_false]; tauto
  have h2 := hf (S ∪ C) Sᶜ
  have e3 : S ∪ C ∪ Sᶜ = Finset.univ := by
    ext x; simp only [Finset.mem_union, Finset.mem_compl, Finset.mem_univ, iff_true]; tauto
  have e4 : (S ∪ C) ∩ Sᶜ = C \ S := by
    ext x; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_compl, Finset.mem_sdiff]; tauto
  rw [e1, e2] at h1
  rw [e3, e4] at h2
  have hd := aux_alvs_down f hf α S hS (S \ (C ∩ S)) Finset.sdiff_subset
  have e5 : S \ (S \ (C ∩ S)) = C ∩ S := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
  rw [e5] at hd
  have hdisj : Disjoint (C \ S) S := Finset.sdiff_disjoint
  have hu := aux_alvs_up f hf α S hS (C \ S) hdisj
  have e6 : S ∪ (C \ S) = S ∪ C := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  rw [e6] at hu
  have hc1 : ((S \ (C ∩ S)).card : ℝ) ≤ Fintype.card X := by
    exact_mod_cast Finset.card_le_univ _
  have hc2 : ((C \ S).card : ℝ) ≤ Fintype.card X := by
    exact_mod_cast Finset.card_le_univ _
  have hfS := hf0 S
  have hf1 := hf0 ∅
  have hf2 := hf0 Finset.univ
  have k1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc1 hα) hfS
  have k2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc2 hα) hfS
  nlinarith
