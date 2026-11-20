-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianComplexHalfGammaDeficit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:27:50.879204+00:00
-- url     : https://prove2.me/submissions/4e178623-e2cf-4b85-ad7d-b8aa2cd54abc

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitValueStrictLeft
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
set_option autoImplicit false

theorem solution
    (b : ℝ) (hb : 0 < b) (theta : ℝ) :
    let w : ℂ := ((-(b ^ 2 / 2 : ℝ) : ℝ) : ℂ) +
      Complex.I * (theta : ℂ)
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (w * (r : ℂ)) - 1) *
        ((r ^ (-(1 / 2 : ℝ) - 1) : ℝ) : ℂ) ∂volume) =
      ((Real.Gamma (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (((1 / 2 : ℝ) : ℂ) * Complex.log (-w)) := by
  intro w
  have hwre : w.re < 0 := by
    dsimp [w]
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [sq_pos_of_pos hb]
  have hw : w ≠ 0 := by
    intro hz
    have hzero : w.re = 0 := by rw [hz]; rfl
    linarith
  simpa only using
    (Kyprianou.Ch01.stableGammaComplexDeficitValueStrictLeft
      (1 / 2 : ℝ) (by norm_num) (by norm_num) w hw hwre)
