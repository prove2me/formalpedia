-- Prove2me | solution 1 for NicaiseDelayWave.BoundaryInstab.eq5_5_5_7_delay_choice
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:39:59.497725+00:00
-- url     : https://prove2.me/submissions/da0b2505-0e30-45ab-a568-c8c68c887d44

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic
set_option autoImplicit false

theorem solution (μ1 μ2 b : ℝ) (hμ1 : 0 < μ1) (h18 : μ1 ≤ μ2) (hb : 0 < b)
    (l : ℕ) :
    let τ := (Real.arccos (-μ1 / μ2) + 2 * l * Real.pi) / b
    0 < τ ∧ Real.cos (b * τ) = -μ1 / μ2 ∧
      μ2 * Real.sin (b * τ) = Real.sqrt (μ2 ^ 2 - μ1 ^ 2) ∧
      ((μ1 : ℂ) + (μ2 : ℂ) * Complex.exp (-(Complex.I * b) * τ)) * (Complex.I * b) =
        ((b * Real.sqrt (μ2 ^ 2 - μ1 ^ 2) : ℝ) : ℂ) := by
  dsimp only
  let τ := (Real.arccos (-μ1 / μ2) + 2 * l * Real.pi) / b
  have hμ2 : 0 < μ2 := hμ1.trans_le h18
  have hm : μ2 ≠ 0 := ne_of_gt hμ2
  have ht : b * τ = Real.arccos (-μ1 / μ2) + l * (2 * Real.pi) := by
    dsimp [τ]
    field_simp <;> ring
  have hlo : -1 ≤ -μ1 / μ2 := (le_div_iff₀ hμ2).2 (by linarith)
  have hhi : -μ1 / μ2 < 1 := (div_lt_iff₀ hμ2).2 (by linarith)
  have hτ : 0 < τ := by
    dsimp [τ]
    apply div_pos _ hb
    have := Real.arccos_pos.mpr hhi
    positivity
  have hc : Real.cos (b * τ) = -μ1 / μ2 := by
    rw [ht, Real.cos_add_nat_mul_two_pi, Real.cos_arccos hlo hhi.le]
  have hs : μ2 * Real.sin (b * τ) = Real.sqrt (μ2 ^ 2 - μ1 ^ 2) := by
    rw [ht, Real.sin_add_nat_mul_two_pi, Real.sin_arccos]
    have he : 1 - (-μ1 / μ2) ^ 2 = (μ2 ^ 2 - μ1 ^ 2) / μ2 ^ 2 := by
      field_simp <;> ring
    rw [he, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hμ2.le]
    field_simp
  refine ⟨hτ, hc, hs, ?_⟩
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.neg_re, Complex.neg_im, Complex.exp_re, Complex.exp_im]
    simp only [zero_mul, one_mul, zero_add, add_zero, mul_zero, sub_zero,
      zero_sub, neg_zero, Real.exp_zero, neg_mul, Real.sin_neg, Real.cos_neg]
    change -((μ2 * -Real.sin (b * τ)) * b) = b * Real.sqrt (μ2 ^ 2 - μ1 ^ 2)
    nlinarith [hs]
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.neg_re, Complex.neg_im, Complex.exp_re, Complex.exp_im]
    simp only [zero_mul, one_mul, zero_add, add_zero, mul_zero, sub_zero,
      zero_sub, neg_zero, Real.exp_zero, neg_mul, Real.sin_neg, Real.cos_neg]
    change (μ1 + μ2 * Real.cos (b * τ)) * b = 0
    rw [hc]
    field_simp <;> ring
