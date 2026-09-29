-- Prove2me | solution 1 for NonmonotoneSubmod.LocalSearch.lemma_3_3_approx_local_optimum
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:22:18.85703+00:00
-- url     : https://prove2.me/submissions/b7bcfd41-1ddd-423b-b098-ca09dcf6ffe8

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_LocalSearch_IsLocalOptimum
import Definitions.Def_NonmonotoneSubmod_LocalSearch_IsApproxLocalOptimum



namespace NonmonotoneSubmod.LocalSearch

theorem nsls_sub_chain {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (S : Finset X) (c : ℝ)
    (hc : ∀ a, a ∈ S → f (S.erase a) - f S ≤ c) :
    ∀ D : Finset X, D ⊆ S → f (S \ D) - f S ≤ D.card * c := by
  intro D
  induction D using Finset.induction_on with
  | empty => intro _; simp
  | insert a D ha ih =>
    intro hD
    have haS : a ∈ S := hD (Finset.mem_insert_self a D)
    have hDS : D ⊆ S := fun x hx => hD (Finset.mem_insert_of_mem hx)
    have h1 := ih hDS
    have h2 := hf (S \ D) (S.erase a)
    have e1 : S \ D ∪ S.erase a = S := by
      ext x
      by_cases hx : x = a
      · subst hx; simp [haS, ha]
      · simp [hx]; tauto
    have e2 : S \ D ∩ S.erase a = S \ insert a D := by
      ext x; simp; tauto
    rw [e1, e2] at h2
    rw [Finset.card_insert_of_notMem ha]; push_cast
    have := hc a haS
    linarith

theorem nsls_sup_chain {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (S : Finset X) (c : ℝ)
    (hc : ∀ a, a ∉ S → f (insert a S) - f S ≤ c) :
    ∀ D : Finset X, Disjoint S D → f (S ∪ D) - f S ≤ D.card * c := by
  intro D
  induction D using Finset.induction_on with
  | empty => intro _; simp
  | insert a D ha ih =>
    intro hD
    have haS : a ∉ S := fun h => Finset.disjoint_left.mp hD h (Finset.mem_insert_self a D)
    have hDS : Disjoint S D := Finset.disjoint_of_subset_right (Finset.subset_insert a D) hD
    have h1 := ih hDS
    have h2 := hf (S ∪ D) (insert a S)
    have e1 : S ∪ D ∪ insert a S = S ∪ insert a D := by
      ext x; simp; tauto
    have e2 : (S ∪ D) ∩ insert a S = S := by
      ext x
      by_cases hx : x = a
      · subst hx; simp [haS, ha]
      · simp [hx]; tauto
    rw [e1, e2] at h2
    rw [Finset.card_insert_of_notMem ha]; push_cast
    have := hc a haS
    linarith

theorem nsls_both {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (S : Finset X) (c : ℝ)
    (hc1 : ∀ a, a ∈ S → f (S.erase a) - f S ≤ c) (hc2 : ∀ a, a ∉ S → f (insert a S) - f S ≤ c)
    (T : Finset X) (hT : T ⊆ S ∨ S ⊆ T) : ∃ D : Finset X, f T - f S ≤ D.card * c := by
  rcases hT with h | h
  · refine ⟨S \ T, ?_⟩
    have := nsls_sub_chain f hf S c hc1 (S \ T) Finset.sdiff_subset
    rwa [Finset.sdiff_sdiff_eq_self h] at this
  · refine ⟨T \ S, ?_⟩
    have := nsls_sup_chain f hf S c hc2 (T \ S) Finset.disjoint_sdiff
    rwa [Finset.union_sdiff_of_subset h] at this

theorem lemma31_core {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (S : Finset X) (hS : IsLocalOptimum f S) (T : Finset X)
    (hT : T ⊆ S ∨ S ⊆ T) :
    f T ≤ f S := by
  obtain ⟨D, hD⟩ := nsls_both f hf S 0 (fun a ha => by linarith [hS.2 a ha])
    (fun a ha => by linarith [hS.1 a ha]) T hT
  simp at hD; linarith

theorem lemma33_core {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S : Finset X, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (α : ℝ) (hα : 0 ≤ α) (S : Finset X) (hS : IsApproxLocalOptimum f α S) (T : Finset X)
    (hT : T ⊆ S ∨ S ⊆ T) :
    f T ≤ (1 + (Fintype.card X : ℝ) * α) * f S := by
  obtain ⟨D, hD⟩ := nsls_both f hf S (α * f S) (fun a ha => by linarith [hS.1 a ha])
    (fun a ha => by linarith [hS.2 a ha]) T hT
  have hcard : (D.card : ℝ) ≤ Fintype.card X := by exact_mod_cast Finset.card_le_univ D
  have h0 : 0 ≤ α * f S := mul_nonneg hα (hf0 S)
  have : (D.card : ℝ) * (α * f S) ≤ Fintype.card X * (α * f S) := mul_le_mul_of_nonneg_right hcard h0
  nlinarith

end NonmonotoneSubmod.LocalSearch

open NonmonotoneSubmod.LocalSearch


theorem solution {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S : Finset X, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (α : ℝ) (hα : 0 ≤ α) (S : Finset X) (hS : IsApproxLocalOptimum f α S) (T : Finset X)
    (hT : T ⊆ S ∨ S ⊆ T) :
    f T ≤ (1 + (Fintype.card X : ℝ) * α) * f S := by
  exact lemma33_core f hf0 hf α hα S hS T hT
