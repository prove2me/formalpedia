-- Prove2me | solution 1 for Kyprianou.Ch01.complexSqrtNegativeImaginaryStableFormulaPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T10:59:39.013458+00:00
-- url     : https://prove2.me/submissions/9c3d5c32-d858-468f-a1e5-948d9de18033

import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Complex
set_option autoImplicit false

theorem solution (ξ : ℝ) :
    Complex.sqrt ((-2 : ℂ) * Complex.I * (ξ : ℂ)) =
      ((Real.sqrt (|ξ|) : ℝ) : ℂ) *
        (1 - Complex.I *
          (((if 0 < ξ then (1 : ℝ)
              else if ξ < 0 then -1 else 0) : ℝ) : ℂ)) := by
  let z : ℂ := (-2 : ℂ) * Complex.I * (ξ : ℂ)
  have hre : z.re = 0 := by
    simp [z]
  have him : z.im = -2 * ξ := by
    simp [z]
  have hnorm : ‖z‖ = 2 * |ξ| := by
    simp [z, norm_mul, Complex.norm_I, Complex.norm_real]
  change z.sqrt = _
  rw [Complex.sqrt_eq_real_add_ite]
  simp only [hnorm, hre, him, add_zero, sub_zero]
  have hhalf : (2 * |ξ|) / 2 = |ξ| := by ring
  rw [hhalf]
  rcases lt_trichotomy ξ 0 with hneg | heq | hpos
  · have hnonpos : ¬ 0 < ξ := not_lt.mpr hneg.le
    have himag : 0 ≤ -2 * ξ := by linarith
    simp only [if_pos himag, if_neg hnonpos, if_pos hneg]
    norm_num <;> ring
  · subst ξ
    simp
  · have hnonneg : ¬ ξ < 0 := not_lt.mpr hpos.le
    have himag : ¬ 0 ≤ -2 * ξ := by linarith
    simp only [if_neg himag, if_pos hpos, if_neg hnonneg]
    norm_num <;> ring
