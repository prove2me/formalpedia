-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneLaplaceCosine
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T09:21:48.35318+00:00
-- url     : https://prove2.me/submissions/c81568cc-3648-4476-8b6b-c3c01adcca7e

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneComplexLaplaceFrequencyOne
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Real Set
set_option autoImplicit false
/-! Evaluate the real Laplace transform of cos by real-part extraction. -/
theorem solution
    (a : ℝ) (ha : 0 < a) :
    (∫ x in Set.Ioi (0 : ℝ),
      Real.exp (-(a * x)) * Real.cos x) = a / (a ^ 2 + 1) := by
  let c : ℂ := (-(a : ℂ)) + Complex.I
  have hc : c.re < 0 := by simpa [c] using neg_neg_of_pos ha
  have hint : IntegrableOn
      (fun x : ℝ => Complex.exp (c * (x : ℂ))) (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_complex_Ioi hc 0
  have hpoint (x : ℝ) :
      (Complex.exp (c * (x : ℂ))).re =
        Real.exp (-(a * x)) * Real.cos x := by
    rw [Complex.exp_re]
    simp [c, Complex.mul_re, Complex.mul_im, mul_add, add_mul]
  have hcomplex := Kyprianou.Ch01.stableAlphaOneComplexLaplaceFrequencyOne a ha
  calc
    (∫ x in Ioi (0 : ℝ), Real.exp (-(a * x)) * Real.cos x) =
      ∫ x in Ioi (0 : ℝ), (Complex.exp (c * (x : ℂ))).re := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact (hpoint x).symm
    _ = (∫ x in Ioi (0 : ℝ), Complex.exp (c * (x : ℂ))).re := by
      exact integral_re hint
    _ = (((a : ℂ) - Complex.I)⁻¹).re := by
      rw [hcomplex]
    _ = a / (a ^ 2 + 1) := by
      rw [Complex.inv_re, Complex.normSq_apply]
      simp [Complex.sub_re, Complex.sub_im]
      ring
