-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_stable_integrated_term_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:40:25.990899+00:00
-- url     : https://prove2.me/submissions/2f78df9e-550c-40a2-9f26-2164d52d8f70

import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false

theorem solution (α q β : ℝ) (hβ : 0 < β) :
    ∀ n : ℕ,
      q ^ n * β ^ (-(α * ((n : ℝ) + 1) + 1)) =
        β ^ (-(α + 1)) * (q / β ^ α) ^ n := by
  intro n
  have hexp : -(α * ((n : ℝ) + 1) + 1) =
      -(α + 1) + (-α) * (n : ℝ) := by ring
  rw [hexp, Real.rpow_add hβ, Real.rpow_mul_natCast hβ.le]
  rw [div_eq_mul_inv, mul_pow]
  simp only [Real.rpow_neg hβ.le]
  ring
