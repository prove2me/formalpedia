-- Prove2me | solution 1 for LeeSviridenkoVondrak.LocalSearch.lemma_1_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:35:14.238859+00:00
-- url     : https://prove2.me/submissions/c97fe8ab-87ce-40d6-b18b-6e7a9eae519d

import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_LeeSviridenkoVondrak_LocalSearch_Model

open scoped symmDiff
open LeeSviridenkoVondrak.LocalSearch

theorem g78v_marg {n : ℕ} (f : Finset (Fin n) → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (A B : Finset (Fin n)) (hAB : A ⊆ B) (x : Fin n) (hx : x ∉ B) :
    f (insert x B) - f B ≤ f (insert x A) - f A := by
  have h := hf (insert x A) B
  have e1 : insert x A ∪ B = insert x B := by
    ext y; simp only [Finset.mem_union, Finset.mem_insert]; constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (hAB h)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
  have e2 : insert x A ∩ B = A := by
    ext y; simp only [Finset.mem_inter, Finset.mem_insert]; constructor
    · rintro ⟨h | h, hb⟩
      · subst h; exact absurd hb hx
      · exact h
    · intro h; exact ⟨Or.inr h, hAB h⟩
  rw [e1, e2] at h
  linarith

theorem g78v_main {n : ℕ} (f : Finset (Fin n) → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (S : Finset (Fin n)) (t q : ℕ) (D : Finset (Fin n)) :
    ∀ T : Fin t → Finset (Fin n), (∀ i, T i ⊆ D) → (∀ x ∈ D, multiplicity T x = q) →
      (∀ x ∈ D, x ∉ S) →
      (q : ℝ) * (f (S ∪ D) - f S) ≤ ∑ i, (f (S ∪ T i) - f S) := by
  induction D using Finset.induction_on with
  | empty =>
    intro T hT _ _
    have : ∀ i, T i = ∅ := fun i => Finset.subset_empty.1 (hT i)
    simp [this]
  | insert x D' hxD ih =>
    intro T hT hc hS
    set T' : Fin t → Finset (Fin n) := fun i => (T i).erase x
    have hT' : ∀ i, T' i ⊆ D' := fun i y hy => by
      have h1 := Finset.mem_erase.1 hy
      have := hT i h1.2
      rcases Finset.mem_insert.1 this with h | h
      · exact absurd h h1.1
      · exact h
    have hc' : ∀ y ∈ D', multiplicity T' y = q := by
      intro y hy
      have hyx : y ≠ x := fun h => hxD (h ▸ hy)
      rw [← hc y (Finset.mem_insert_of_mem hy)]
      unfold LeeSviridenkoVondrak.LocalSearch.multiplicity
      congr 1
      ext i
      simp [T', Finset.mem_erase, hyx]
    have hS' : ∀ y ∈ D', y ∉ S := fun y hy => hS y (Finset.mem_insert_of_mem hy)
    have IH := ih T' hT' hc' hS'
    have hxS : x ∉ S := hS x (Finset.mem_insert_self x D')
    have hxB : x ∉ S ∪ D' := by
      rw [Finset.mem_union]; rintro (h | h)
      · exact hxS h
      · exact hxD h
    -- per-index gain
    have hstep : ∀ i, (if x ∈ T i then f (insert x (S ∪ D')) - f (S ∪ D') else 0) ≤
        f (S ∪ T i) - f (S ∪ T' i) := by
      intro i
      split_ifs with hx
      · have e : S ∪ T i = insert x (S ∪ T' i) := by
          ext y; simp only [Finset.mem_union, Finset.mem_insert, T', Finset.mem_erase]
          constructor
          · rintro (h | h)
            · exact Or.inr (Or.inl h)
            · by_cases hy : y = x
              · exact Or.inl hy
              · exact Or.inr (Or.inr ⟨hy, h⟩)
          · rintro (h | h | ⟨_, h⟩)
            · subst h; exact Or.inr hx
            · exact Or.inl h
            · exact Or.inr h
        rw [e]
        exact g78v_marg f hf (S ∪ T' i) (S ∪ D') (Finset.union_subset_union le_rfl (hT' i)) x hxB
      · have : T' i = T i := Finset.erase_eq_of_notMem hx
        rw [this]; simp
    have hsum : (q : ℝ) * (f (insert x (S ∪ D')) - f (S ∪ D')) ≤
        ∑ i, (f (S ∪ T i) - f (S ∪ T' i)) := by
      refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun i _ => hstep i)
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      have := hc x (Finset.mem_insert_self x D')
      unfold LeeSviridenkoVondrak.LocalSearch.multiplicity at this
      rw [this]
    have e3 : S ∪ insert x D' = insert x (S ∪ D') := by
      ext y; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    rw [e3]
    have e4 : ∑ i, (f (S ∪ T i) - f S) = ∑ i, (f (S ∪ T i) - f (S ∪ T' i)) +
        ∑ i, (f (S ∪ T' i) - f S) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e4]
    nlinarith [IH, hsum]

theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (hf0 : Nonnegative f)
    (S C : Finset (Fin n)) (t q : ℕ) (T : Fin t → Finset (Fin n))
    (hT : ∀ i, T i ⊆ C \ S) (hcover : ∀ x ∈ C \ S, multiplicity T x = q) :
    (q : ℝ) * (f (S ∪ C) - f S) ≤ ∑ i, (f (S ∪ T i) - f S) := by
  have := g78v_main f hf S t q (C \ S) T hT hcover (fun x hx => (Finset.mem_sdiff.1 hx).2)
  rwa [Finset.union_sdiff_self_eq_union] at this
