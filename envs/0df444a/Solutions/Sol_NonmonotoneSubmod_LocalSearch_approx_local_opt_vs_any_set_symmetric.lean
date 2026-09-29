-- Prove2me | solution 1 for NonmonotoneSubmod.LocalSearch.approx_local_opt_vs_any_set_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:52:32.872822+00:00
-- url     : https://prove2.me/submissions/69911e76-7957-43f8-a4a8-009fa1d2f3f7

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_SymmetricSetFun
import Definitions.Def_NonmonotoneSubmod_LocalSearch_IsApproxLocalOptimum

namespace NonmonotoneSubmod.LocalSearch

theorem aux_alovsym_sub {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f) (α : ℝ) (S : Finset X)
    (hS : IsApproxLocalOptimum f α S) :
    ∀ D : Finset X, D ⊆ S → f (S \ D) ≤ (1 + (D.card : ℝ) * α) * f S := by
  intro D
  induction D using Finset.induction_on with
  | empty => intro _; simp
  | insert a D haD ih =>
    intro hD
    have haS : a ∈ S := hD (Finset.mem_insert_self a D)
    have hDS : D ⊆ S := fun x hx => hD (Finset.mem_insert_of_mem hx)
    have h1 := ih hDS
    have h2 := hS.1 a haS
    have h3 := hf (S \ D) (S.erase a)
    have e1 : S \ D ∪ S.erase a = S := by
      ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_erase]
      constructor
      · rintro (⟨h, _⟩ | ⟨_, h⟩) <;> exact h
      · intro hx
        by_cases hxa : x = a
        · subst hxa; left; exact ⟨hx, haD⟩
        · right; exact ⟨hxa, hx⟩
    have e2 : S \ D ∩ S.erase a = S \ insert a D := by
      ext x; simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
      tauto
    rw [e1, e2] at h3
    rw [Finset.card_insert_of_notMem haD]
    push_cast
    nlinarith

theorem aux_alovsym_sup {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f) (α : ℝ) (S : Finset X)
    (hS : IsApproxLocalOptimum f α S) :
    ∀ D : Finset X, Disjoint D S → f (S ∪ D) ≤ (1 + (D.card : ℝ) * α) * f S := by
  intro D
  induction D using Finset.induction_on with
  | empty => intro _; simp
  | insert a D haD ih =>
    intro hD
    have haS : a ∉ S := Finset.disjoint_left.mp hD (Finset.mem_insert_self a D)
    have hDS : Disjoint D S := Finset.disjoint_of_subset_left (Finset.subset_insert a D) hD
    have h1 := ih hDS
    have h2 := hS.2 a haS
    have h3 := hf (S ∪ D) (insert a S)
    have e1 : S ∪ D ∪ insert a S = S ∪ insert a D := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    have e2 : (S ∪ D) ∩ insert a S = S := by
      ext x; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert]
      constructor
      · rintro ⟨h | h, h' | h'⟩
        · exact h
        · exact h'
        · subst h'; exact absurd h haD
        · exact h'
      · intro hx; exact ⟨Or.inl hx, Or.inr hx⟩
    rw [e1, e2] at h3
    rw [Finset.card_insert_of_notMem haD]
    push_cast
    nlinarith

end NonmonotoneSubmod.LocalSearch

open NonmonotoneSubmod.LocalSearch

theorem solution {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S : Finset X, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (hsym : NonmonotoneSubmod.Shared.SymmetricSetFun f) (α : ℝ) (hα : 0 ≤ α) (S : Finset X)
    (hS : IsApproxLocalOptimum f α S) (C : Finset X) :
    f C ≤ 2 * (1 + (Fintype.card X : ℝ) * α) * f S := by
  have hfS := hf0 S
  have hαS : 0 ≤ α * f S := mul_nonneg hα hfS
  -- f C ≤ f (C ∩ S) + f (C \ S)
  have hsplit := hf (C ∩ S) (C \ S)
  have eu : C ∩ S ∪ C \ S = C := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have ei : C ∩ S ∩ (C \ S) = ∅ := by
    ext x; simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.notMem_empty, iff_false]
    tauto
  rw [eu, ei] at hsplit
  have h0 := hf0 ∅
  -- subset part
  have hA := aux_alovsym_sub f hf α S hS (S \ C) Finset.sdiff_subset
  have eA : S \ (S \ C) = C ∩ S := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
  rw [eA] at hA
  have hcA : ((S \ C).card : ℝ) ≤ Fintype.card X := by exact_mod_cast Finset.card_le_univ _
  -- superset part
  have hB := aux_alovsym_sup f hf α S hS (Cᶜ \ S) Finset.sdiff_disjoint
  have eB : S ∪ (Cᶜ \ S) = (C \ S)ᶜ := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_compl]; tauto
  rw [eB, hsym] at hB
  have hcB : ((Cᶜ \ S).card : ℝ) ≤ Fintype.card X := by exact_mod_cast Finset.card_le_univ _
  nlinarith
