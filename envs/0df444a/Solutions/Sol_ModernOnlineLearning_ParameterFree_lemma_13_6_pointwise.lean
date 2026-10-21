-- Prove2me | solution 1 for ModernOnlineLearning.ParameterFree.lemma_13_6_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T05:36:10.102596+00:00
-- url     : https://prove2.me/submissions/a119d6e9-5958-4d6d-a73a-a6a2826dcc80

import Mathlib

private lemma exp_square_ge (r : ℝ) : r ≤ Real.exp (r ^ 2 / 2) := by
  have h := Real.add_one_le_exp (r ^ 2 / 2)
  nlinarith [sq_nonneg (r - 1)]

theorem solution (a b x y : ℝ) (ha : 0 < a) (hb : 0 < b) :
    x * y - b * Real.exp (x ^ 2 / (2 * a)) ≤
      |y| * Real.sqrt (2 * a * Real.log (1 + Real.sqrt a * |y| / b)) - b := by
  let R := Real.sqrt (2 * a * Real.log (1 + Real.sqrt a * |y| / b))
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hs2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have harg : 0 < 1 + Real.sqrt a * |y| / b := by positivity
  have hlog : 0 ≤ Real.log (1 + Real.sqrt a * |y| / b) := by
    apply Real.log_nonneg
    have : 0 ≤ Real.sqrt a * |y| / b := by positivity
    linarith
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = 2 * a * Real.log (1 + Real.sqrt a * |y| / b) :=
    Real.sq_sqrt (by positivity)
  have hExpR : Real.exp (R ^ 2 / (2 * a)) = 1 + Real.sqrt a * |y| / b := by
    rw [hR2, mul_div_cancel_left₀ _ (by positivity : 2 * a ≠ 0), Real.exp_log harg]
  have hxy : x * y ≤ |x| * |y| := by
    simpa only [abs_mul] using le_abs_self (x * y)
  change _ ≤ |y| * R - b
  by_cases hx : |x| ≤ R
  · have hm := mul_le_mul_of_nonneg_right hx (abs_nonneg y)
    have he : b ≤ b * Real.exp (x ^ 2 / (2 * a)) := by
      have h := Real.one_le_exp_iff.mpr (by positivity : 0 ≤ x ^ 2 / (2 * a))
      simpa using mul_le_mul_of_nonneg_left h hb.le
    nlinarith
  · have hxR : R < |x| := lt_of_not_ge hx
    let δ := |x| - R
    have hδ : 0 < δ := sub_pos.mpr hxR
    have hq : δ / Real.sqrt a ≤ Real.exp (δ ^ 2 / (2 * a)) := by
      convert exp_square_ge (δ / Real.sqrt a) using 1
      congr 1
      rw [div_pow, hs2]
      ring
    have hsplit : R ^ 2 / (2 * a) + δ ^ 2 / (2 * a) ≤ x ^ 2 / (2 * a) := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      dsimp [δ]
      nlinarith [sq_abs x]
    have he := Real.exp_le_exp.mpr hsplit
    rw [Real.exp_add, hExpR] at he
    have hm := mul_le_mul_of_nonneg_left hq (mul_nonneg hs.le (abs_nonneg y))
    have hid : Real.sqrt a * |y| * (δ / Real.sqrt a) = |y| * δ := by field_simp
    rw [hid] at hm
    have he0 : 1 ≤ Real.exp (δ ^ 2 / (2 * a)) := Real.one_le_exp_iff.mpr (by positivity)
    have hb0 : b ≤ b * Real.exp (δ ^ 2 / (2 * a)) := by
      simpa using mul_le_mul_of_nonneg_left he0 hb.le
    have htotal := mul_le_mul_of_nonneg_left he hb.le
    have hdist : b * ((1 + Real.sqrt a * |y| / b) * Real.exp (δ ^ 2 / (2 * a))) =
        b * Real.exp (δ ^ 2 / (2 * a)) + Real.sqrt a * |y| * Real.exp (δ ^ 2 / (2 * a)) := by
      field_simp
    rw [hdist] at htotal
    dsimp [δ] at hm
    nlinarith

