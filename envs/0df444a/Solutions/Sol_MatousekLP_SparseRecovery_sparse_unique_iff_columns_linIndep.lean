-- Prove2me | solution 1 for MatousekLP.SparseRecovery.sparse_unique_iff_columns_linIndep
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T04:35:55.258827+00:00
-- url     : https://prove2.me/submissions/28325514-7025-4527-ac58-6f41047714c3

import Definitions.Def_MatousekLP_SparseRecovery_BasisPursuit
import Mathlib

open Matrix MatousekLP.SparseRecovery

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : ℕ) :
    (∀ (b : Fin m → ℝ) (x' x'' : Fin n → ℝ),
        IsSparseSolution A b r x' → IsSparseSolution A b r x'' → x' = x'') ↔
      (∀ S : Finset (Fin n), S.card ≤ 2 * r →
        LinearIndependent ℝ (fun j : S => Aᵀ (j : Fin n))) := by
  classical
  -- `A d` as a combination of the columns on a superset of the support of `d`
  have hcomb : ∀ (S : Finset (Fin n)) (d : Fin n → ℝ), (∀ j, j ∉ S → d j = 0) →
      ∑ j : S, d j • Aᵀ (j : Fin n) = A *ᵥ d := by
    intro S d hd
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, transpose_apply, mulVec, dotProduct]
    rw [Finset.sum_coe_sort S (fun j => d j * A i j)]
    rw [Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => by simp [hd j hj])]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  constructor
  · intro huniq S hS
    by_contra hdep
    obtain ⟨g, hg, j₀, hj₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
    -- split S into two parts of size at most r
    obtain ⟨S₁, hS₁S, hS₁card⟩ := Finset.exists_subset_card_eq (s := S) (n := min r S.card)
      (min_le_right _ _)
    set S₂ := S \ S₁
    have hS₂card : S₂.card ≤ r := by
      rw [Finset.card_sdiff_of_subset hS₁S, hS₁card]; omega
    set G : Fin n → ℝ := fun j => if h : j ∈ S then g ⟨j, h⟩ else 0
    set x' : Fin n → ℝ := fun j => if j ∈ S₁ then G j else 0
    set x'' : Fin n → ℝ := fun j => if j ∈ S₂ then -G j else 0
    have hGS : ∀ j, j ∉ S → G j = 0 := fun j hj => by simp [G, hj]
    have hAG : A *ᵥ G = 0 := by
      rw [← hcomb S G hGS, ← hg]
      exact Finset.sum_congr rfl fun j _ => by simp [G, j.2]
    have hsplit : x' - x'' = G := by
      funext j
      by_cases h1 : j ∈ S₁
      · have : j ∉ S₂ := fun h => (Finset.mem_sdiff.mp h).2 h1
        simp [x', x'', h1, this]
      · by_cases h2 : j ∈ S
        · have : j ∈ S₂ := Finset.mem_sdiff.mpr ⟨h2, h1⟩
          simp [x', x'', h1, this]
        · have : j ∉ S₂ := fun h => h2 (Finset.mem_sdiff.mp h).1
          simp [x', x'', h1, this, hGS j h2]
    have hsupp : ∀ (T : Finset (Fin n)) (y : Fin n → ℝ), (∀ j, j ∉ T → y j = 0) →
        (supp y).card ≤ T.card := by
      intro T y hy
      apply Finset.card_le_card
      intro j hj
      simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      by_contra h; exact hj (hy j h)
    have heq : A *ᵥ x' = A *ᵥ x'' := by
      rw [← sub_eq_zero, ← mulVec_sub, hsplit, hAG]
    have := huniq (A *ᵥ x') x' x''
      ⟨rfl, (hsupp S₁ x' fun j hj => by simp [x', hj]).trans (hS₁card ▸ min_le_left _ _)⟩
      ⟨heq.symm, (hsupp S₂ x'' fun j hj => by simp [x'', hj]).trans hS₂card⟩
    have hG0 : G (j₀ : Fin n) = 0 := by rw [← hsplit, this, sub_self]; rfl
    exact hj₀ (by simpa [G, j₀.2] using hG0)
  · intro hli b x' x'' h' h''
    set S := supp x' ∪ supp x''
    have hS : S.card ≤ 2 * r := (Finset.card_union_le _ _).trans (by have := h'.2; have := h''.2; omega)
    set d := x' - x''
    have hd : ∀ j, j ∉ S → d j = 0 := by
      intro j hj
      simp only [S, Finset.mem_union, supp, Finset.mem_filter, Finset.mem_univ, true_and,
        not_or, not_not] at hj
      simp [d, hj.1, hj.2]
    have hAd : A *ᵥ d = 0 := by simp [d, mulVec_sub, h'.1, h''.1]
    have hz := (Fintype.linearIndependent_iff.mp (hli S hS)) (fun j => d j)
      (by rw [hcomb S d hd, hAd])
    funext j
    by_cases hj : j ∈ S
    · have := hz ⟨j, hj⟩; simpa [d, sub_eq_zero] using this
    · have := hd j hj; simpa [d, sub_eq_zero] using this
