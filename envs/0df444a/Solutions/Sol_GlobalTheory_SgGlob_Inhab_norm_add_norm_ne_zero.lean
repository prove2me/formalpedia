-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.norm_add_norm_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T04:23:55.103075+00:00
-- url     : https://prove2.me/submissions/720cbfa8-d3ea-4005-9e9e-b31a82705bfa

import Mathlib
variable {E : Type} [Field E]


theorem solution (σ : E →+* E) (τ : E →+* ℂ) (hτ : ∀ x, τ (σ x) = starRingEnd ℂ (τ x))
    {a : E} (ha : a ≠ 0) (b : E) : a * σ a + b * σ b ≠ 0 := by
  intro h; have hz := congrArg τ h
  simp only [map_add,map_mul,map_zero,hτ,Complex.mul_conj] at hz
  have H := congrArg Complex.re hz; simp at H
  have hτa : τ a ≠ 0 := by simpa only [map_zero] using τ.injective.ne ha
  have hpos := Complex.normSq_pos.mpr hτa
  linarith [Complex.normSq_nonneg (τ b)]
