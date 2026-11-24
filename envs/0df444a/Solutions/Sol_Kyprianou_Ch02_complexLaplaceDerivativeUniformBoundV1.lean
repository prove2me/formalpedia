-- Prove2me | solution 1 for Kyprianou.Ch02.complexLaplaceDerivativeUniformBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-23T23:52:52.506851+00:00
-- url     : https://prove2.me/submissions/573e75e2-daaa-45a8-a9d8-ad4d52025d83

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false



theorem solution (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : r ≤ z.re)
    (x : ℝ) (hx : 0 ≤ x) :
    ‖(x : ℂ) * Complex.exp (-z * (x : ℂ))‖ ≤ max 1 (1 / r) * min 1 |x| := by
  have hz0 := le_trans hr.le hz
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx, Complex.norm_exp]
  have he : (-z * (x : ℂ)).re = -(z.re * x) := by simp [Complex.mul_re]
  rw [he]
  have hu : Real.exp (-(z.re * x)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hz0 hx))
  by_cases h : x ≤ 1
  · rw [min_eq_right h]; exact (mul_le_mul_of_nonneg_left hu hx).trans (by simpa [mul_comm] using mul_le_mul_of_nonneg_right (le_max_left 1 (1/r)) hx)
  · rw [min_eq_left (le_of_not_ge h), mul_one]
    apply le_trans _ (le_max_right _ _)
    rw [le_div_iff₀ hr, Real.exp_neg, ← div_eq_mul_inv, div_mul_eq_mul_div, div_le_iff₀ (Real.exp_pos _), one_mul]
    have ht := Real.add_one_le_exp (z.re*x)
    nlinarith [mul_le_mul_of_nonneg_right hz hx]
