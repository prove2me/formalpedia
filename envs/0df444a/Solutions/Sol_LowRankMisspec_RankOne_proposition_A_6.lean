-- Prove2me | solution 1 for LowRankMisspec.RankOne.proposition_A_6
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-12T16:28:44.052576+00:00
-- url     : https://prove2.me/submissions/65fab04d-5976-4a1b-9bd1-054ef718fca1

import Mathlib

set_option autoImplicit false

/-- A rank-one nonnegative probability matrix is the outer product of its row and column sums. -/
theorem solution {m n : Type} [Fintype m] [Fintype n] (A : Matrix m n ℝ)
    (hnonneg : ∀ i j, 0 ≤ A i j) (hsum : ∑ i, ∑ j, A i j = 1) (hrank : A.rank = 1) :
    ∀ i j, A i j = (∑ k, A i k) * (∑ l, A l j) := by
  classical
  let S : Submodule ℝ (m → ℝ) := Submodule.span ℝ (Set.range A.col)
  have hS : Module.finrank ℝ S = 1 := by
    rw [← Matrix.rank_eq_finrank_span_cols]
    exact hrank
  have hSne : S ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hS
    norm_num at hS
  obtain ⟨v, hvS, hv0⟩ := (Submodule.ne_bot_iff S).mp hSne
  have hspan : ∀ w : S, ∃ c : ℝ, c • v = (w : m → ℝ) := by
    intro w
    have hvS' : (⟨v, hvS⟩ : S) ≠ 0 := by
      intro h
      exact hv0 (congrArg Subtype.val h)
    have h := (finrank_eq_one_iff_of_nonzero' (⟨v, hvS⟩ : S) hvS').mp hS w
    obtain ⟨c, hc⟩ := h
    exact ⟨c, congrArg Subtype.val hc⟩
  have hcol : ∀ j, ∃ c : ℝ, ∀ i, c * v i = A i j := by
    intro j
    obtain ⟨c, hc⟩ := hspan ⟨A.col j, Submodule.subset_span (Set.mem_range_self j)⟩
    exact ⟨c, fun i => by simpa [Pi.smul_apply, Matrix.col_apply] using congrFun hc i⟩
  choose c hc using hcol
  have hAeq : ∀ i j, A i j = c j * v i := by
    intro i j
    exact (hc j i).symm
  let U : ℝ := ∑ j, c j
  let V : ℝ := ∑ i, v i
  have hrow : ∀ i, (∑ k, A i k) = v i * U := by
    intro i
    simp_rw [hAeq i]
    rw [← Finset.sum_mul]
    ring
  have hcolsum : ∀ j, (∑ l, A l j) = c j * V := by
    intro j
    simp_rw [hAeq _ j]
    rw [Finset.mul_sum]
  have htotal : (∑ i, ∑ j, A i j) = V * U := by
    calc (∑ i, ∑ j, A i j) = ∑ i, (v i * U) := by
          exact Finset.sum_congr rfl fun i _ => hrow i
      _ = (∑ i, v i) * U := by rw [Finset.sum_mul]
      _ = V * U := rfl
  have hUV : U * V = 1 := by
    rw [mul_comm]
    exact htotal.symm.trans hsum
  intro i j
  rw [hrow i, hcolsum j, hAeq i j]
  calc c j * v i = (c j * v i) * (U * V) := by rw [hUV, mul_one]
    _ = (v i * U) * (c j * V) := by ring
