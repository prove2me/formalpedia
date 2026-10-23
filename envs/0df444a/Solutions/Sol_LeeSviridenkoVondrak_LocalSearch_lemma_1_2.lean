-- Prove2me | solution 1 for LeeSviridenkoVondrak.LocalSearch.lemma_1_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:35:38.083842+00:00
-- url     : https://prove2.me/submissions/f3b4af10-d589-402c-8247-2de438b4bdf2

import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_LeeSviridenkoVondrak_LocalSearch_Model

open scoped symmDiff
open LeeSviridenkoVondrak.LocalSearch

theorem g78w_marg {n : ℕ} (f : Finset (Fin n) → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
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

theorem g78w_main {n : ℕ} (f : Finset (Fin n) → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (S : Finset (Fin n)) (t q : ℕ) (D : Finset (Fin n)) :
    D ⊆ S → ∀ T : Fin t → Finset (Fin n), (∀ i, T i ⊆ D) → (∀ x ∈ D, multiplicity T x = q) →
      ∑ i, (f S - f (S \ T i)) ≤ (q : ℝ) * (f S - f (S \ D)) := by
  induction D using Finset.induction_on with
  | empty =>
    intro _ T hT _
    have : ∀ i, T i = ∅ := fun i => Finset.subset_empty.1 (hT i)
    simp [this]
  | insert x D' hxD ih =>
    intro hDS T hT hc
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
    have hD'S : D' ⊆ S := fun y hy => hDS (Finset.mem_insert_of_mem hy)
    have IH := ih hD'S T' hT' hc'
    have hxS : x ∈ S := hDS (Finset.mem_insert_self x D')
    have eD : insert x (S \ insert x D') = S \ D' := by
      ext y; simp only [Finset.mem_insert, Finset.mem_sdiff]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · subst h; exact ⟨hxS, hxD⟩
        · exact ⟨h1, fun h => h2 (Or.inr h)⟩
      · rintro ⟨h1, h2⟩
        by_cases hy : y = x
        · exact Or.inl hy
        · exact Or.inr ⟨h1, by rintro (h | h); exact hy h; exact h2 h⟩
    have hstep : ∀ i, f (S \ T' i) - f (S \ T i) ≤
        (if x ∈ T i then f (S \ D') - f (S \ insert x D') else 0) := by
      intro i
      split_ifs with hx
      · have e : S \ T' i = insert x (S \ T i) := by
          ext y; simp only [Finset.mem_sdiff, Finset.mem_insert, T', Finset.mem_erase]
          constructor
          · rintro ⟨h1, h2⟩
            by_cases hy : y = x
            · exact Or.inl hy
            · exact Or.inr ⟨h1, fun h => h2 ⟨hy, h⟩⟩
          · rintro (h | ⟨h1, h2⟩)
            · subst h; exact ⟨hxS, fun h => h.1 rfl⟩
            · exact ⟨h1, fun h => h2 h.2⟩
        rw [e, ← eD]
        exact g78w_marg f hf (S \ insert x D') (S \ T i)
          (Finset.sdiff_subset_sdiff le_rfl (hT i)) x (fun h => (Finset.mem_sdiff.1 h).2 hx)
      · have : T' i = T i := Finset.erase_eq_of_notMem hx
        rw [this]; simp
    have hsum : ∑ i, (f (S \ T' i) - f (S \ T i)) ≤
        (q : ℝ) * (f (S \ D') - f (S \ insert x D')) := by
      refine le_trans (Finset.sum_le_sum fun i _ => hstep i) (le_of_eq ?_)
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      have := hc x (Finset.mem_insert_self x D')
      unfold LeeSviridenkoVondrak.LocalSearch.multiplicity at this
      rw [this]
    have e4 : ∑ i, (f S - f (S \ T i)) = ∑ i, (f S - f (S \ T' i)) +
        ∑ i, (f (S \ T' i) - f (S \ T i)) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e4]
    nlinarith [IH, hsum]

theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (hf0 : Nonnegative f)
    (S S' : Finset (Fin n)) (hS : S' ⊆ S) (t q : ℕ) (T : Fin t → Finset (Fin n))
    (hT : ∀ i, T i ⊆ S \ S') (hcover : ∀ x ∈ S \ S', multiplicity T x = q) :
    ∑ i, (f S - f (S \ T i)) ≤ (q : ℝ) * (f S - f S') := by
  have := g78w_main f hf S t q (S \ S') Finset.sdiff_subset T hT hcover
  rwa [Finset.sdiff_sdiff_eq_self hS] at this
