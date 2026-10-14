-- Prove2me | solution 1 for IntMul.OpenAI.bruhat_rank_profile
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-12T14:03:09.03823+00:00
-- url     : https://prove2.me/submissions/e47e0a2a-f6bc-411b-9f57-b7a53a75d8dd

import Mathlib

open Matrix Finset

namespace BruhatRankAux

variable {K : Type*} [Field K] {m : ℕ}

/-- Rank of a rectangular 0/1 matrix with at most one `1` per row and column = number of ones. -/
lemma rank_pp {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [DecidableEq K]
    (P : Matrix ι κ K)
    (h01 : ∀ i j, P i j = 0 ∨ P i j = 1)
    (hrow : ∀ i j j', P i j = 1 → P i j' = 1 → j = j')
    (hcol : ∀ i i' j, P i j = 1 → P i' j = 1 → i = i') :
    P.rank = (univ.filter fun x : ι × κ => P x.1 x.2 = 1).card := by
  have hPPt : P * Pᵀ = diagonal fun i => if ∃ j, P i j = 1 then (1 : K) else 0 := by
    ext i i'
    rw [mul_apply, diagonal_apply]
    simp only [transpose_apply]
    by_cases hii : i = i'
    · subst hii
      rw [if_pos rfl]
      split_ifs with hex
      · obtain ⟨j, hj⟩ := hex
        rw [Finset.sum_eq_single j]
        · rw [hj, one_mul]
        · intro j' _ hj'
          rcases h01 i j' with h | h
          · rw [h, zero_mul]
          · exact absurd (hrow i j j' hj h).symm hj'
        · simp
      · push Not at hex
        refine Finset.sum_eq_zero fun j _ => ?_
        rcases h01 i j with h | h
        · rw [h, zero_mul]
        · exact absurd h (hex j)
    · rw [if_neg hii]
      refine Finset.sum_eq_zero fun j _ => ?_
      rcases h01 i j with h | h
      · rw [h, zero_mul]
      rcases h01 i' j with h' | h'
      · rw [h', mul_zero]
      · exact absurd (hcol i i' j h h') hii
  have hPPtP : P * Pᵀ * P = P := by
    rw [hPPt]
    ext i j
    rw [diagonal_mul]
    split_ifs with hex
    · rw [one_mul]
    · push Not at hex
      rw [zero_mul]
      rcases h01 i j with h | h
      · exact h.symm
      · exact absurd h (hex j)
  have hrank1 : P.rank = (P * Pᵀ).rank := by
    apply le_antisymm
    · calc P.rank = (P * Pᵀ * P).rank := by rw [hPPtP]
        _ ≤ (P * Pᵀ).rank := rank_mul_le_left _ _
    · exact rank_mul_le_left _ _
  rw [hrank1, hPPt, rank_diagonal, Fintype.card_subtype]
  refine (Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_).symm
  · intro x hx; simp only [mem_filter, mem_univ, true_and] at hx ⊢
    simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not]
    exact ⟨x.2, hx⟩
  · intro x hx y hy hxy
    simp only [mem_filter, mem_univ, true_and] at hx hy
    exact Prod.ext hxy (hrow x.1 x.2 y.2 hx (hxy ▸ hy))
  · intro i hi
    simp only [mem_filter, mem_univ, true_and, ne_eq, ite_eq_right_iff, one_ne_zero,
      imp_false, not_not] at hi
    obtain ⟨j, hj⟩ := hi
    exact ⟨(i, j), by simp [hj], rfl⟩

lemma sum_sub {p : Fin m → Prop} [DecidablePred p] (f : Fin m → K) (hf : ∀ a, ¬ p a → f a = 0) :
    ∑ a, f a = ∑ a : {a // p a}, f a.1 := by
  rw [← Finset.sum_subtype (univ.filter p) (by simp) f, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rfl
  · exact hf a h

end BruhatRankAux

open BruhatRankAux in
theorem solution {m : ℕ} {K : Type*} [Field K] [DecidableEq K]
    (E₁ P E₂ : Matrix (Fin m) (Fin m) K)
    (hE₁ : ∀ i j, i < j → E₁ i j = 0) (hd₁ : ∀ i, E₁ i i ≠ 0)
    (hE₂ : ∀ i j, i < j → E₂ i j = 0) (hd₂ : ∀ i, E₂ i i ≠ 0)
    (h01 : ∀ i j, P i j = 0 ∨ P i j = 1)
    (hrow : ∀ i j j', P i j = 1 → P i j' = 1 → j = j')
    (hcol : ∀ i i' j, P i j = 1 → P i' j = 1 → i = i') (i j : Fin m) :
    ((E₁ * P * E₂).submatrix (fun r : {r : Fin m // r ≤ i} => r.1)
        (fun c : {c : Fin m // j ≤ c} => c.1)).rank =
      (univ.filter fun x : Fin m × Fin m => x.1 ≤ i ∧ j ≤ x.2 ∧ P x.1 x.2 = 1).card := by
  classical
  have hfac : (E₁ * P * E₂).submatrix (fun r : {r : Fin m // r ≤ i} => r.1)
        (fun c : {c : Fin m // j ≤ c} => c.1) =
      E₁.submatrix (fun r : {r : Fin m // r ≤ i} => r.1) (fun r : {r : Fin m // r ≤ i} => r.1) *
        P.submatrix (fun r : {r : Fin m // r ≤ i} => r.1) (fun c : {c : Fin m // j ≤ c} => c.1) *
        E₂.submatrix (fun c : {c : Fin m // j ≤ c} => c.1) (fun c : {c : Fin m // j ≤ c} => c.1) := by
    ext r c
    simp only [submatrix_apply, mul_apply]
    rw [sum_sub (p := fun b => j ≤ b) (fun b => (∑ a, E₁ r.1 a * P a b) * E₂ b c.1)
      (fun b hb => by rw [hE₂ b c.1 (lt_of_lt_of_le (not_le.1 hb) c.2), mul_zero])]
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    exact sum_sub (p := fun a => a ≤ i) (fun a => E₁ r.1 a * P a b.1)
      (fun a ha => by rw [hE₁ r.1 a (lt_of_le_of_lt r.2 (not_le.1 ha)), zero_mul])
  have hdet : ∀ (p : Fin m → Prop) [DecidablePred p] (E : Matrix (Fin m) (Fin m) K),
      (∀ i j, i < j → E i j = 0) → (∀ i, E i i ≠ 0) →
      IsUnit (E.submatrix (fun r : {r // p r} => r.1) (fun r : {r // p r} => r.1)).det := by
    intro p _ E hE hd
    have hl : (E.submatrix (fun r : {r // p r} => r.1) (fun r : {r // p r} => r.1)).IsLowerTriangular :=
      fun a b hab => hE _ _ (show a.1 < b.1 from hab)
    rw [det_of_isLowerTriangular _ hl, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hd a.1
  rw [hfac, rank_mul_eq_left_of_isUnit_det _ _ (hdet (fun c => j ≤ c) E₂ hE₂ hd₂),
    rank_mul_eq_right_of_isUnit_det _ _ (hdet (fun r => r ≤ i) E₁ hE₁ hd₁)]
  rw [rank_pp (P.submatrix (fun r : {r : Fin m // r ≤ i} => r.1) (fun c : {c : Fin m // j ≤ c} => c.1)) (fun a b => h01 _ _) (fun a b b' h h' => Subtype.ext (hrow _ _ _ h h'))
    (fun a a' b h h' => Subtype.ext (hcol _ _ _ h h'))]
  refine Finset.card_bij (fun x _ => (x.1.1, x.2.1)) ?_ ?_ ?_
  · intro x hx
    have hx' : P x.1.1 x.2.1 = 1 := (Finset.mem_filter.1 hx).2
    simpa using ⟨x.1.2, x.2.2, hx'⟩
  · intro x _ y _ hxy
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext (Subtype.ext hxy.1) (Subtype.ext hxy.2)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    refine ⟨(⟨x.1, hx.1⟩, ⟨x.2, hx.2.1⟩), ?_, rfl⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hx.2.2⟩
