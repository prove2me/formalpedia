-- Prove2me | solution 1 for Kyprianou.Ch02.complexLaplaceKernelUniformBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:50:28.029235+00:00
-- url     : https://prove2.me/submissions/86c84fe8-2250-4b5d-8712-40ab608b8d88

import Theorems.Thm_Kyprianou_Ch02_complexLaplaceKernelNormLeOneV1
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (z : ℂ) (hz : 0 ≤ z.re) (x : ℝ) (hx : 0 ≤ x) :
    ‖1 - Complex.exp (-z * (x : ℂ))‖ ≤ 2 * max 1 ‖z‖ * min 1 |x| := by
  have hn := Kyprianou.Ch02.complexLaplaceKernelNormLeOneV1 z hz x hx
  have htwo : ‖1 - Complex.exp (-z * (x : ℂ))‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (-z * (x : ℂ))‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  rw [abs_of_nonneg hx]
  by_cases hx1 : 1 ≤ x
  · rw [min_eq_left hx1]
    nlinarith [le_max_left (1 : ℝ) ‖z‖]
  · rw [min_eq_right (le_of_lt (not_le.mp hx1))]
    by_cases hsmall : ‖-z * (x : ℂ)‖ ≤ 1
    · have h := Complex.norm_exp_sub_one_le hsmall
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx] at h
      rw [norm_sub_rev]
      exact h.trans (by nlinarith [le_max_right (1 : ℝ) ‖z‖])
    · have hgt : 1 < ‖z‖ * x := by
        simpa [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hx] using not_le.mp hsmall
      exact htwo.trans (by nlinarith [le_max_right (1 : ℝ) ‖z‖])
