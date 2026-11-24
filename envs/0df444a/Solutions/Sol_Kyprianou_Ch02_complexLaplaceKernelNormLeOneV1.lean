-- Prove2me | solution 1 for Kyprianou.Ch02.complexLaplaceKernelNormLeOneV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:50:23.429357+00:00
-- url     : https://prove2.me/submissions/b37041ee-313c-42db-a913-6f921ff16329

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (z : ℂ) (hz : 0 ≤ z.re) (x : ℝ) (hx : 0 ≤ x) :
    ‖Complex.exp (-z * (x : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp, ← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  rw [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  exact neg_nonpos.mpr (mul_nonneg hz hx)
