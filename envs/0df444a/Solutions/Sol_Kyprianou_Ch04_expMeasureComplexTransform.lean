-- Prove2me | solution 1 for Kyprianou.Ch04.expMeasureComplexTransform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T08:06:22.710866+00:00
-- url     : https://prove2.me/submissions/f981ba06-fef2-4bcf-808d-0edc26b0f8b0

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution (q : ℝ) (hq : 0 < q) (z : ℂ) (hz : z.re < q) :
    (∫ t : ℝ, Complex.exp (z * t) ∂expMeasure q) =
      (q : ℂ) / ((q : ℂ) - z) := by
  have hd : expMeasure q =
      (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun x => ENNReal.ofReal (q * Real.exp (-q * x))) := by
    change volume.withDensity (exponentialPDF q) = _
    rw [← withDensity_indicator measurableSet_Ioi]
    apply withDensity_congr_ae
    filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
    rw [exponentialPDF_eq]
    by_cases hp : 0 < x
    · simp [hp, hp.le, neg_mul]
    · have hn : x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hx
      simp [not_le.mpr hn, hp]
  rw [hd, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (mul_nonneg hq.le (Real.exp_nonneg _))]
  have he : (fun x : ℝ => (q * Real.exp (-q * x)) • Complex.exp (z * x)) =
      (fun x : ℝ => (q : ℂ) * Complex.exp ((z - (q : ℂ)) * x)) := by
    funext x
    rw [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he, integral_const_mul,
    integral_exp_mul_complex_Ioi (by simpa using sub_neg.mpr hz) 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show z - (q : ℂ) = -((q : ℂ) - z) by ring, div_neg, neg_div, neg_neg]
  rw [← mul_div_assoc, mul_one]
