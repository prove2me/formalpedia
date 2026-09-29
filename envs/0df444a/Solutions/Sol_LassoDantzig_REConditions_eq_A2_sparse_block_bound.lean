-- Prove2me | solution 1 for LassoDantzig.REConditions.eq_A2_sparse_block_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:46:38.611873+00:00
-- url     : https://prove2.me/submissions/c67d7a8b-0877-4d42-9c4d-3392cbf498af

import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE
import Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues

namespace LassoDantzig.REConditions

theorem aux_a2sbb_bdd {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (u : ℕ) :
    BddAbove (rayleighSet X u) := by
  refine ⟨(1 / (n:ℝ)) * ∑ i, ∑ j, X i j ^ 2, ?_⟩
  rintro q ⟨x, -, -, rfl⟩
  have hC : 0 ≤ (1 / (n:ℝ)) * ∑ i, ∑ j, X i j ^ 2 := by positivity
  rcases eq_or_lt_of_le (Finset.sum_nonneg (fun j _ => sq_nonneg (x j)) :
      (0:ℝ) ≤ ∑ j, x j ^ 2) with h | h
  · rw [← h, div_zero]; exact hC
  · rw [div_le_iff₀ h]
    unfold gramQuad
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

end LassoDantzig.REConditions

open LassoDantzig.REConditions

theorem solution {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hn : 1 ≤ n) (hM : 2 ≤ M) (m : ℕ) (hm : 1 ≤ m)
    (δ : Fin M → ℝ) (J J' : Finset (Fin M)) (hJ : J.card ≤ m) :
    1 / Real.sqrt n * projNorm X J' (X.mulVec (restrict δ J)) ≤
        1 / Real.sqrt n * euclNorm (X.mulVec (restrict δ J)) ∧
    1 / Real.sqrt n * euclNorm (X.mulVec (restrict δ J)) ≤
        Real.sqrt (phiMax X m) * l2On δ J := by
  constructor
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    unfold projNorm euclNorm
    calc _ ≤ ‖WithLp.toLp 2 (X.mulVec (restrict δ J))‖ :=
          Submodule.norm_starProjection_apply_le _ _
      _ = _ := by rw [EuclideanSpace.norm_eq]; simp
  · set x := restrict δ J with hx
    have hsumx : ∑ j, x j ^ 2 = ∑ j ∈ J, δ j ^ 2 := by
      rw [hx]
      simp only [restrict, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn
    have key : (1 / (n:ℝ)) * ∑ i, (X.mulVec x i) ^ 2 ≤ phiMax X m * ∑ j ∈ J, δ j ^ 2 := by
      rcases eq_or_lt_of_le (Finset.sum_nonneg (fun j _ => sq_nonneg (x j)) :
          (0:ℝ) ≤ ∑ j, x j ^ 2) with h | h
      · have hx0 : x = 0 := by
          funext j
          have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j))).1 h.symm j
            (Finset.mem_univ _)
          simpa using this
        rw [← hsumx, ← h, hx0]
        simp
      · have hmem : gramQuad X x / ∑ j, x j ^ 2 ∈ rayleighSet X m := by
          refine ⟨x, ?_, ?_, rfl⟩
          · unfold sparsity
            apply Finset.card_pos.2
            by_contra hc
            rw [Finset.not_nonempty_iff_eq_empty] at hc
            have : ∀ j, x j = 0 := by
              intro j
              by_contra hj
              have : j ∈ supp x := by simp [supp, hj]
              rw [hc] at this
              simp at this
            simp [this] at h
          · unfold sparsity
            refine le_trans (Finset.card_le_card ?_) hJ
            intro j hj
            simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at hj
            by_contra hjJ
            apply hj
            simp [hx, restrict, hjJ]
        have hle := le_csSup (aux_a2sbb_bdd X m) hmem
        rw [div_le_iff₀ h] at hle
        rw [← hsumx]
        exact hle
    unfold euclNorm l2On
    rw [one_div, ← Real.sqrt_inv, ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul' _
      (Finset.sum_nonneg (fun j _ => sq_nonneg (δ j)))]
    apply Real.sqrt_le_sqrt
    rw [← one_div]
    exact key
