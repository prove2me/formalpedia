-- Prove2me | solution 1 for Kyprianou.Ch02.levyPointwiseCosExpAbsBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:27:23.321865+00:00
-- url     : https://prove2.me/submissions/5564c490-541b-43fe-8cd1-9a3c47dc13e0

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic.Positivity
import Theorems.Thm_GlobalTheory_CharFormDeriv_norm_cexp_mul_I_sub_one_le
import Theorems.Thm_Kyprianou_Ch02_levyPointwiseExpAbsBoundV1
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (ξ x : ℝ) :
    1 - Real.cos (ξ * x) ≤ 4 * (1 + |ξ|) * (1 - Real.exp (-|x|)) := by
  have hn := GlobalTheory.CharFormDeriv.norm_cexp_mul_I_sub_one_le (ξ * x)
  have hr := Complex.abs_re_le_norm (Complex.exp (↑(ξ * x) * I) - 1)
  rw [Complex.sub_re, Complex.exp_ofReal_mul_I_re, Complex.one_re] at hr
  have hlin : 1 - Real.cos (ξ * x) ≤ 2 * |ξ| * |x| := by
    rw [abs_mul] at hn
    linarith [neg_le_abs (Real.cos (ξ * x) - 1)]
  have htwo : 1 - Real.cos (ξ * x) ≤ 2 := by
    linarith [Real.neg_one_le_cos (ξ * x)]
  have hm : 1 - Real.cos (ξ * x) ≤ 2 * (1 + |ξ|) * min 1 |x| := by
    rcases le_total |x| 1 with ha | ha
    · rw [min_eq_right ha]
      nlinarith [abs_nonneg x]
    · rw [min_eq_left ha]
      linarith [abs_nonneg ξ]
  have hmul := mul_le_mul_of_nonneg_left
    (Kyprianou.Ch02.levyPointwiseExpAbsBoundV1 x)
    (show 0 ≤ 2 * (1 + |ξ|) by positivity)
  linarith
