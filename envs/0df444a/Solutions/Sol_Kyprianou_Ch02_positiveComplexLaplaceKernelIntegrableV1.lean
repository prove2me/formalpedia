-- Prove2me | solution 1 for Kyprianou.Ch02.positiveComplexLaplaceKernelIntegrableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:39:53.533264+00:00
-- url     : https://prove2.me/submissions/6630ec8d-fde7-4727-9409-602e8ec3371a

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ)
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (ν.restrict (Set.Ioi (0 : ℝ)))) (z : ℂ) (hz : 0 ≤ z.re) :
    Integrable (fun x : ℝ => 1 - Complex.exp (-z * (x : ℂ)))
      (ν.restrict (Set.Ioi (0 : ℝ))) := by
  let μ := ν.restrict (Set.Ioi (0 : ℝ))
  let C : ℝ := 2 * max 1 ‖z‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply (hint.const_mul C).mono'
  · exact (show Continuous (fun x : ℝ => 1 - Complex.exp (-z * (x : ℂ))) by
      fun_prop).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := le_of_lt hx
    have hn : ‖Complex.exp (-z * (x : ℂ))‖ ≤ 1 := by
      rw [Complex.norm_exp, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      rw [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      exact neg_nonpos.mpr (mul_nonneg hz hx0)
    have htwo : ‖1 - Complex.exp (-z * (x : ℂ))‖ ≤ 2 := by
      calc
        _ ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (-z * (x : ℂ))‖ := norm_sub_le _ _
        _ ≤ 2 := by rw [norm_one]; linarith
    rw [abs_of_nonneg hx0]
    by_cases hx1 : 1 ≤ x
    · rw [min_eq_left hx1]
      dsimp [C]
      nlinarith [le_max_left (1 : ℝ) ‖z‖]
    · rw [min_eq_right (le_of_lt (not_le.mp hx1))]
      by_cases hsmall : ‖-z * (x : ℂ)‖ ≤ 1
      · have h := Complex.norm_exp_sub_one_le hsmall
        rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0] at h
        rw [norm_sub_rev]
        exact h.trans (by dsimp [C]; nlinarith [le_max_right (1 : ℝ) ‖z‖])
      · have hgt : 1 < ‖z‖ * x := by
          simpa [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hx0] using not_le.mp hsmall
        exact htwo.trans (by dsimp [C]; nlinarith [le_max_right (1 : ℝ) ‖z‖])
