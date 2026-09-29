-- Prove2me | solution 1 for LassoDantzig.Equivalence.eq_2_3_lasso_dantzig_feasible
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:04:23.042381+00:00
-- url     : https://prove2.me/submissions/cd622da8-77d7-45da-9f8b-f9ce1a4398bc

import Mathlib
import Definitions.Def_LassoDantzig_Equivalence_Model

namespace LassoDantzig.Equivalence

lemma aux_ldf_colNorm_nonneg {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (j : Fin M) :
    0 ≤ colNorm X j := Real.sqrt_nonneg _

lemma aux_ldf_final (c A a r : ℝ) (hA : 0 ≤ A)
    (h : ∀ t : ℝ, 2 * t * c ≤ t ^ 2 * A + 2 * r * a * |t|) : |c| ≤ r * a := by
  by_contra hc
  push Not at hc
  set d := |c| - r * a with hd
  have hdpos : 0 < d := by linarith
  set s := d / (A + 1) with hs
  have hspos : 0 < s := div_pos hdpos (by linarith)
  have hsA : s * A < d := by
    rw [hs, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  have key : 2 * s * |c| ≤ s ^ 2 * A + 2 * r * a * s := by
    rcases le_or_gt 0 c with h0 | h0
    · have := h s
      rw [abs_of_pos hspos] at this
      rw [abs_of_nonneg h0]; exact this
    · have := h (-s)
      rw [abs_neg, abs_of_pos hspos] at this
      rw [abs_of_neg h0]; nlinarith
  have h3 : 2 * |c| ≤ s * A + 2 * r * a := by
    have h2 : s * (2 * |c|) ≤ s * (s * A + 2 * r * a) := by nlinarith
    exact le_of_mul_le_mul_left h2 hspos
  linarith

end LassoDantzig.Equivalence

open LassoDantzig.Equivalence

theorem solution {n M : ℕ} (hn : 1 ≤ n)
    (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (βL : Fin M → ℝ) (hL : IsLasso X y r βL) :
    DantzigFeasible X y r βL := by
  intro j
  apply aux_ldf_final _ ((1 / (n:ℝ)) * ∑ i, X i j ^ 2) _ _ (by positivity)
  intro t
  have hmin := hL (fun k => βL k + if k = j then t else 0)
  unfold lassoObj at hmin
  have hmv : ∀ i, X.mulVec (fun k => βL k + if k = j then t else 0) i
      = X.mulVec βL i + X i j * t := by
    intro i
    simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  have hres : ∑ i, (y i - X.mulVec (fun k => βL k + if k = j then t else 0) i) ^ 2
      = ∑ i, (y i - X.mulVec βL i) ^ 2 - 2 * t * ∑ i, X i j * (y i - X.mulVec βL i)
        + t ^ 2 * ∑ i, X i j ^ 2 := by
    simp only [hmv]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hpen : ∑ k, colNorm X k * |βL k + if k = j then t else 0|
      ≤ ∑ k, colNorm X k * |βL k| + colNorm X j * |t| := by
    have hk' : ∀ k, colNorm X k * |βL k + if k = j then t else 0|
        ≤ colNorm X k * |βL k| + (if k = j then colNorm X j * |t| else 0) := by
      intro k
      by_cases hk : k = j
      · subst hk
        simp only [if_true]
        nlinarith [abs_add_le (βL k) t, aux_ldf_colNorm_nonneg X k]
      · simp [hk]
    calc _ ≤ ∑ k, (colNorm X k * |βL k| + (if k = j then colNorm X j * |t| else 0)) :=
          Finset.sum_le_sum (fun k _ => hk' k)
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_ite_eq']; simp
  rw [hres] at hmin
  nlinarith [mul_le_mul_of_nonneg_left hpen (by positivity : (0:ℝ) ≤ 2 * r)]
