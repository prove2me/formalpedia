-- Prove2me | solution 1 for NicaiseDelayWave.InternalInstab.eq5_24_characteristic_reduction
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:37:06.676981+00:00
-- url     : https://prove2.me/submissions/e7e289bf-f534-4ce0-8797-9c3fb2ada0a7

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic
set_option autoImplicit false

theorem solution (α β τ μ₁ μ₂ Λ : ℝ) (l : ℕ)
    (hβτ : β * τ = (2 * l + 1) * Real.pi) :
    ((⟨α, β⟩ : ℂ) ^ 2 + ((μ₁ : ℂ) + (μ₂ : ℂ) * Complex.exp (-(⟨α, β⟩ : ℂ) * τ)) * ⟨α, β⟩
        = -((Λ : ℂ) ^ 2)) ↔
      (α ^ 2 + β ^ 2 = Λ ^ 2 ∧ μ₂ * Real.exp (-α * τ) = 2 * α + μ₁) := by
  have hβ : β ≠ 0 := by
    intro h
    have hpos : (0 : ℝ) < (2 * l + 1) * Real.pi := by positivity
    rw [h, zero_mul] at hβτ
    linarith
  have hcos : Real.cos (β * τ) = -1 := by
    rw [hβτ]
    convert Real.cos_nat_mul_two_pi_add_pi l using 1 <;> congr 1 <;> ring
  have hsin : Real.sin (β * τ) = 0 := by
    rw [hβτ]
    convert Real.sin_nat_mul_pi (2*l+1) using 1 <;> push_cast <;> ring
  have hexp : Complex.exp (-(⟨α, β⟩ : ℂ) * τ) = (-(Real.exp (-α * τ)) : ℝ) := by
    apply Complex.ext <;>
      simp [Complex.exp_re, Complex.exp_im, neg_mul, hcos, hsin]
  rw [hexp, Complex.ext_iff]
  simp only [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, add_zero, sub_zero, neg_zero]
  constructor
  · rintro ⟨hr, hi⟩
    have he : μ₂ * Real.exp (-α * τ) = 2 * α + μ₁ := by
      have hz : β * (2 * α + μ₁ - μ₂ * Real.exp (-α * τ)) = 0 := by nlinarith [hi]
      have := (mul_eq_zero.mp hz).resolve_left hβ
      linarith
    simp only [mul_neg, he] at hr
    exact ⟨by nlinarith [hr], he⟩
  · rintro ⟨h1,h2⟩
    simp only [mul_neg, h2]
    constructor <;> nlinarith
