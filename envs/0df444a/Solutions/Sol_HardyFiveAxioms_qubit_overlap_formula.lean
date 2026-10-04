-- Prove2me | solution 1 for HardyFiveAxioms.qubit_overlap_formula
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T11:12:57.762906+00:00
-- url     : https://prove2.me/submissions/7f356ebe-fb99-4c7e-b79a-15c301d46c48

import Mathlib
import Definitions.Def_hardy2001_projectors

open HardyFiveAxioms in
theorem solution (a b φ₃ φ₄ : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) :
    (proj ![(Real.sqrt (1 - a) : ℂ), (Real.sqrt a : ℂ) * Complex.exp (φ₃ * Complex.I)] *
        proj ![(Real.sqrt (1 - b) : ℂ), (Real.sqrt b : ℂ) * Complex.exp (φ₄ * Complex.I)]).trace =
      ((1 - a - b + 2 * a * b + 2 * Real.cos (φ₄ - φ₃) * Real.sqrt (a * b * (1 - a) * (1 - b)) :
        ℝ) : ℂ) := by
  have h1a : 0 ≤ 1 - a := sub_nonneg.2 ha₁
  have h1b : 0 ≤ 1 - b := sub_nonneg.2 hb₁
  have hs : Real.sqrt (a * b * (1 - a) * (1 - b))
      = Real.sqrt a * Real.sqrt b * Real.sqrt (1 - a) * Real.sqrt (1 - b) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul ha₀]
  have sa := Real.sq_sqrt ha₀
  have sb := Real.sq_sqrt hb₀
  have s1a := Real.sq_sqrt h1a
  have s1b := Real.sq_sqrt h1b
  have e3 : Complex.exp (φ₃ * Complex.I) = ((Real.cos φ₃ : ℝ) : ℂ) + ((Real.sin φ₃ : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have e4 : Complex.exp (φ₄ * Complex.I) = ((Real.cos φ₄ : ℝ) : ℂ) + ((Real.sin φ₄ : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [hs, Real.cos_sub, e3, e4]
  simp only [proj, Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply, Matrix.vecMulVec_apply,
    Matrix.diag_apply, Pi.star_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have p3 := Real.sin_sq_add_cos_sq φ₃
  have p4 := Real.sin_sq_add_cos_sq φ₄
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re,
      Complex.conj_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    linear_combination (√(1 - b))^2 * s1a + (1 - a) * s1b
      + (√b)^2 * (Real.sin φ₃ ^ 2 + Real.cos φ₃ ^ 2) * (Real.sin φ₄ ^ 2 + Real.cos φ₄ ^ 2) * sa
      + a * (Real.sin φ₃ ^ 2 + Real.cos φ₃ ^ 2) * (Real.sin φ₄ ^ 2 + Real.cos φ₄ ^ 2) * sb
      + a * b * (Real.sin φ₄ ^ 2 + Real.cos φ₄ ^ 2) * p3 + a * b * p4
  · simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re,
      Complex.conj_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    ring
