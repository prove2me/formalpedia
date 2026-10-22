-- Prove2me | solution 1 for NatureSLT.Kernels.poisson_kernel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:22:08.979784+00:00
-- url     : https://prove2.me/submissions/0b5db1f5-28bd-4842-84e7-dd3607d5e6eb

import Mathlib

theorem g69f_poisson_hasSum (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (t : ℝ) :
    HasSum (fun k : ℕ => q ^ (k + 1) * Real.cos ((k + 1) * t))
      ((q * Real.cos t - q ^ 2) / (1 - 2 * q * Real.cos t + q ^ 2)) := by
  set w : ℂ := (q : ℂ) * Complex.exp (t * Complex.I) with hw_def
  have hw : ‖w‖ < 1 := by
    rw [hw_def, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hq0, mul_one]; exact hq1
  have h3 := Complex.hasSum_re ((hasSum_geometric_of_norm_lt_one hw).mul_left w)
  have hwre : w.re = q * Real.cos t := by
    rw [hw_def, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hwim : w.im = q * Real.sin t := by
    rw [hw_def, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  convert h3 using 1
  · funext k
    have : w * w ^ k = ((q ^ (k + 1) : ℝ) : ℂ) * Complex.exp ((((k + 1 : ℝ)) * t : ℝ) * Complex.I) := by
      rw [← pow_succ', hw_def, mul_pow, ← Complex.exp_nat_mul]
      push_cast; ring_nf
    rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  · have hD : 0 < 1 - 2 * q * Real.cos t + q ^ 2 := by
      nlinarith [Real.cos_le_one t, Real.neg_one_le_cos t]
    have hns : Complex.normSq (1 - w) = 1 - 2 * q * Real.cos t + q ^ 2 := by
      rw [Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, hwre, hwim]
      nlinarith [Real.sin_sq_add_cos_sq t]
    rw [Complex.mul_re, Complex.inv_re, Complex.inv_im, hns]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, hwre, hwim]
    have hsc := Real.sin_sq_add_cos_sq t
    field_simp
    congr 1
    first | linear_combination q * hsc | linear_combination (-q) * hsc

theorem solution (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (xi xj : ℝ) :
    Summable (fun k : ℕ => q ^ (k + 1) *
        (Real.cos ((k + 1) * xi) * Real.cos ((k + 1) * xj) +
          Real.sin ((k + 1) * xi) * Real.sin ((k + 1) * xj))) ∧
    Summable (fun k : ℕ => q ^ (k + 1) * Real.cos ((k + 1) * (xi - xj))) ∧
    1 / 2 + ∑' k : ℕ, q ^ (k + 1) *
        (Real.cos ((k + 1) * xi) * Real.cos ((k + 1) * xj) +
          Real.sin ((k + 1) * xi) * Real.sin ((k + 1) * xj)) =
      1 / 2 + ∑' k : ℕ, q ^ (k + 1) * Real.cos ((k + 1) * (xi - xj)) ∧
    1 / 2 + ∑' k : ℕ, q ^ (k + 1) * Real.cos ((k + 1) * (xi - xj)) =
      (1 - q ^ 2) / (2 * (1 - 2 * q * Real.cos (xi - xj) + q ^ 2)) := by
  have hfun : (fun k : ℕ => q ^ (k + 1) *
        (Real.cos ((k + 1) * xi) * Real.cos ((k + 1) * xj) +
          Real.sin ((k + 1) * xi) * Real.sin ((k + 1) * xj))) =
      (fun k : ℕ => q ^ (k + 1) * Real.cos ((k + 1) * (xi - xj))) := by
    funext k
    rw [mul_sub, Real.cos_sub]
  have hs := g69f_poisson_hasSum q hq0 hq1 (xi - xj)
  rw [hfun]
  refine ⟨hs.summable, hs.summable, rfl, ?_⟩
  rw [hs.tsum_eq]
  have hD : 0 < 1 - 2 * q * Real.cos (xi - xj) + q ^ 2 := by
    nlinarith [Real.cos_le_one (xi - xj), Real.neg_one_le_cos (xi - xj)]
  field_simp
  ring
