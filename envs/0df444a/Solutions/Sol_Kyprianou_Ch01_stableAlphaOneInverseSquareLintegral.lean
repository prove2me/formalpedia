-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneInverseSquareLintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T09:27:00.943204+00:00
-- url     : https://prove2.me/submissions/5d6b6bf9-cc44-4773-a2b5-0284647908d3

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneInverseSquareLaplace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Real Set
open scoped ENNReal
set_option autoImplicit false
/-! The Gamma inverse-square identity in the extended nonnegative Tonelli integral. -/
theorem solution
    (x : ℝ) (hx : 0 < x) :
    (∫⁻ t in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (t * Real.exp (-(x * t)))) =
      ENNReal.ofReal ((x ^ 2)⁻¹) := by
  have hInt : IntegrableOn
      (fun t : ℝ => t * Real.exp (-(x * t))) (Ioi (0 : ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (1 : ℝ)) (b := x)
      (by norm_num) (by norm_num) hx
    simpa [Real.rpow_one, neg_mul] using h
  have hPos : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ => t * Real.exp (-(x * t))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg ht.le (Real.exp_pos _).le
  calc
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
      (t * Real.exp (-(x * t)))) =
      ENNReal.ofReal (∫ t in Ioi (0 : ℝ),
        t * Real.exp (-(x * t))) :=
          (ofReal_integral_eq_lintegral_ofReal hInt hPos).symm
    _ = ENNReal.ofReal ((x ^ 2)⁻¹) := by
      rw [Kyprianou.Ch01.stableAlphaOneInverseSquareLaplace x hx]
