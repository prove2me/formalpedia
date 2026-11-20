-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianDensityMassOne
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:01:42.022178+00:00
-- url     : https://prove2.me/submissions/39ae5e5e-7562-4100-a2b5-11c8c5d4a190
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianDensityLaplaceIntegralValue
open MeasureTheory Set Complex Kyprianou.Ch01
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (s b : ℝ) (hs : 0 < s) (hb : 0 < b) :
    let IG : Measure ℝ := (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((s / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-((s - b * x) ^ 2 / (2 * x)))))
    IG Set.univ = 1 := by
  intro IG
  have hlap := Kyprianou.Ch01.inverseGaussianDensityLaplaceIntegralValue
    s b hs hb 0 (le_refl 0)
  have hbroot : Real.sqrt (b ^ 2) = b := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hb]
  have hzero : (∫ x : ℝ, (1 : ℝ) ∂IG) = 1 := by
    simpa only [IG, mul_zero, zero_mul, add_zero, hbroot,
      sub_self, neg_zero, Real.exp_zero] using hlap
  have hreal : (IG Set.univ).toReal = 1 := by
    simpa only [integral_const, MeasureTheory.measureReal_def,
      smul_eq_mul, mul_one] using hzero
  exact (ENNReal.toReal_eq_one_iff (IG Set.univ)).mp hreal
