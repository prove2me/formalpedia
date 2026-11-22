-- Prove2me | solution 1 for LevyStochCalc.Examples.Nonvacuity.abs_expWeightClamp_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T13:41:26.965154+00:00
-- url     : https://prove2.me/submissions/b4ada443-0805-4e8a-9baf-8ac691b372fe

import Definitions.Def_NonvacuityBSDEJRate_F000

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open LevyStochCalc.Examples.Nonvacuity

theorem solution (s t : ℝ) :
    |expWeightClamp s - expWeightClamp t| ≤ Real.exp 1 * |s - t| := by
  rw [expWeightClamp, expWeightClamp]
  have hconv : Convex ℝ (Set.Iic (1 : ℝ)) := convex_Iic 1
  have hdiff : ∀ x ∈ Set.Iic (1 : ℝ), DifferentiableAt ℝ Real.exp x :=
    fun x _ => Real.differentiableAt_exp
  have hbound : ∀ x ∈ Set.Iic (1 : ℝ), ‖deriv Real.exp x‖ ≤ Real.exp 1 := by
    intro x hx
    rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
    exact Real.exp_le_exp.mpr hx
  have hA : 1 - max s 0 ∈ Set.Iic (1 : ℝ) := by simp
  have hB : 1 - max t 0 ∈ Set.Iic (1 : ℝ) := by simp
  have h1 := hconv.norm_image_sub_le_of_norm_deriv_le hdiff hbound hA hB
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h1
  have h3 : |max t 0 - max s 0| ≤ |t - s| := abs_max_sub_max_le_abs t s 0
  calc |Real.exp (1 - max s 0) - Real.exp (1 - max t 0)|
      = |Real.exp (1 - max t 0) - Real.exp (1 - max s 0)| := abs_sub_comm _ _
    _ ≤ Real.exp 1 * |(1 - max t 0) - (1 - max s 0)| := h1
    _ = Real.exp 1 * |max t 0 - max s 0| := by
        congr 1
        rw [show (1 - max t 0) - (1 - max s 0) = max s 0 - max t 0 by ring]
        exact abs_sub_comm _ _
    _ ≤ Real.exp 1 * |t - s| := mul_le_mul_of_nonneg_left h3 (Real.exp_pos 1).le
    _ = Real.exp 1 * |s - t| := by rw [abs_sub_comm]
