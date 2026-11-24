-- Prove2me | solution 2 for Kyprianou.Ch02.complexLaplaceDerivativeUniformBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:53:22.876499+00:00
-- url     : https://prove2.me/submissions/7639452f-761d-4a76-a092-f1f8dbcd89cd

import Theorems.Thm_Kyprianou_Ch02_complexLaplaceKernelNormLeOneV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : r ≤ z.re)
    (x : ℝ) (hx : 0 ≤ x) :
    ‖(x : ℂ) * Complex.exp (-z * (x : ℂ))‖ ≤ max 1 (1 / r) * min 1 |x| := by
  have hn := Kyprianou.Ch02.complexLaplaceKernelNormLeOneV1 z (hr.le.trans hz) x hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
  by_cases h : x ≤ 1
  · rw [min_eq_right h]
    have hmax : 1 ≤ max 1 (1 / r) := le_max_left _ _
    nlinarith
  · rw [min_eq_left (le_of_lt (not_le.mp h)), mul_one]
    have he : ‖Complex.exp (-z * (x : ℂ))‖ ≤ Real.exp (-(r*x)) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      nlinarith
    have hle : x * Real.exp (-(r*x)) ≤ 1/r := by
      apply (le_div_iff₀ hr).2
      have hb := Real.mul_exp_neg_le_exp_neg_one (r*x)
      have h1 : Real.exp (-1) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by norm_num)
      nlinarith
    exact (mul_le_mul_of_nonneg_left he hx).trans (hle.trans (le_max_right _ _))
