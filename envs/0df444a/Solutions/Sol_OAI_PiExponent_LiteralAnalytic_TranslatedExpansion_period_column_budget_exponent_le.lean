-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period_column_budget_exponent_le
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T12:34:17.280736+00:00
-- url     : https://prove2.me/submissions/5ff1230c-1d3f-446a-b320-c3d040670934

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers

open scoped BigOperators

theorem solution
    {m : ℕ} (h : ℕ) (a : Fin m → ℕ)
    (w : Fin m → ℝ) {R H w0 wstar : ℝ}
    (hR : 1 ≤ R) (hH : 0 ≤ H) (hw0 : 0 < w0) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i)
    (hcol : w0 * (h : ℝ) + ∑ i, w i * (a i : ℝ) ≤ H) :
    (h : ℝ) * R + (∑ i, (a i : ℝ)) * Real.log (2 * R) ≤
      H * (R / w0 + Real.log (2 * R) / wstar) := by
  have hsum_weight_nonneg : 0 ≤ ∑ i, w i * (a i : ℝ) := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (le_trans (le_of_lt hws) (hw i)) (Nat.cast_nonneg _)
  have hperiod_budget : w0 * (h : ℝ) ≤ H := by
    linarith
  have hdegree_budget : ∑ i, w i * (a i : ℝ) ≤ H := by
    have hperiod_nonneg : 0 ≤ w0 * (h : ℝ) :=
      mul_nonneg (le_of_lt hw0) (Nat.cast_nonneg _)
    linarith
  have hweighted_degree :
      wstar * (∑ i, (a i : ℝ)) ≤ ∑ i, w i * (a i : ℝ) := by
    calc
      wstar * (∑ i, (a i : ℝ)) = ∑ i, wstar * (a i : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ i, w i * (a i : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right (hw i) (Nat.cast_nonneg _)
  have hperiod_coeff : (h : ℝ) ≤ H / w0 := by
    apply (le_div_iff₀ hw0).2
    nlinarith [hperiod_budget]
  have hdegree_coeff : (∑ i, (a i : ℝ)) ≤ H / wstar := by
    apply (le_div_iff₀ hws).2
    nlinarith [hweighted_degree, hdegree_budget]
  have hR_nonneg : 0 ≤ R := le_trans (by norm_num) hR
  have hlog_nonneg : 0 ≤ Real.log (2 * R) := by
    apply Real.log_nonneg
    nlinarith
  have hperiod_scaled :
      (h : ℝ) * R ≤ H * (R / w0) := by
    calc
      (h : ℝ) * R ≤ (H / w0) * R :=
        mul_le_mul_of_nonneg_right hperiod_coeff hR_nonneg
      _ = H * (R / w0) := by
        simp only [div_eq_mul_inv]
        ring
  have hdegree_scaled :
      (∑ i, (a i : ℝ)) * Real.log (2 * R) ≤
        H * (Real.log (2 * R) / wstar) := by
    calc
      (∑ i, (a i : ℝ)) * Real.log (2 * R) ≤
          (H / wstar) * Real.log (2 * R) :=
        mul_le_mul_of_nonneg_right hdegree_coeff hlog_nonneg
      _ = H * (Real.log (2 * R) / wstar) := by
        simp only [div_eq_mul_inv]
        ring
  calc
    (h : ℝ) * R + (∑ i, (a i : ℝ)) * Real.log (2 * R) ≤
        H * (R / w0) + H * (Real.log (2 * R) / wstar) :=
      add_le_add hperiod_scaled hdegree_scaled
    _ = H * (R / w0 + Real.log (2 * R) / wstar) := by
      rw [mul_add]