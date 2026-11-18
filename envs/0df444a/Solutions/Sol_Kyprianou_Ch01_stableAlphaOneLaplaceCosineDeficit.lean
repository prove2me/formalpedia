-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneLaplaceCosineDeficit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T09:28:47.665625+00:00
-- url     : https://prove2.me/submissions/e2181283-5c36-49ee-9006-866805c20df1

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLaplaceCosine
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Real Set
set_option autoImplicit false
/-! A positive Laplace kernel integrates to the rational Cauchy density. -/
theorem solution
    (a : ℝ) (ha : 0 < a) :
    (∫ x in Set.Ioi (0 : ℝ),
      a * Real.exp (-(a * x)) * (1 - Real.cos x)) =
        (1 + a ^ 2)⁻¹ := by
  have hExp : IntegrableOn
      (fun x : ℝ => Real.exp (-(a * x))) (Ioi (0 : ℝ)) := by
    simpa only [neg_mul] using
      (integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0)
  have hCos : IntegrableOn
      (fun x : ℝ => Real.exp (-(a * x)) * Real.cos x)
      (Ioi (0 : ℝ)) := by
    apply hExp.mono'
    · have hm : Measurable
        (fun x : ℝ => Real.exp (-(a * x)) * Real.cos x) := by fun_prop
      exact hm.aestronglyMeasurable
    · filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one x) (Real.exp_pos _).le
  have hExpValue :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(a * x))) = a⁻¹ := by
    have h := integral_exp_mul_Ioi (a := -a) (by linarith) (0 : ℝ)
    simpa [Real.exp_zero, neg_mul, div_eq_mul_inv] using h
  have hCosValue :=
    Kyprianou.Ch01.stableAlphaOneLaplaceCosine a ha
  have hpoint (x : ℝ) :
      a * Real.exp (-(a * x)) * (1 - Real.cos x) =
        a * Real.exp (-(a * x)) -
          a * (Real.exp (-(a * x)) * Real.cos x) := by ring
  simp_rw [hpoint]
  rw [integral_sub (hExp.const_mul a) (hCos.const_mul a),
      integral_const_mul, integral_const_mul, hExpValue, hCosValue]
  field_simp [ne_of_gt ha, show 1 + a ^ 2 ≠ 0 by positivity]
  ring
