-- Prove2me | solution 1 for HighResODE.NAGSCODE.coeff_lt_two
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:46:22.971132+00:00
-- url     : https://prove2.me/submissions/f97e8bdd-946e-4f85-895b-c6414e1c7602

import Mathlib

set_option autoImplicit false

theorem solution (μ s : ℝ) (hμ : 0 < μ) (hs : 0 < s) (hμs : μ * s ≤ 1) :
    1 / 2 + (3 - 2 * Real.sqrt (μ * s) + μ * s) / (2 * (1 + Real.sqrt (μ * s)) ^ 3)
      + 2 * μ * s / (1 + Real.sqrt (μ * s)) < 2 := by
  have hms : 0 < μ * s := mul_pos hμ hs
  obtain ⟨u, hu0, hu⟩ : ∃ u : ℝ, 0 < u ∧ u = Real.sqrt (μ * s) :=
    ⟨Real.sqrt (μ * s), Real.sqrt_pos.2 hms, rfl⟩
  have hu2 : u ^ 2 = μ * s := by rw [hu]; exact Real.sq_sqrt hms.le
  have hu1 : u ≤ 1 := by
    rw [hu]; calc Real.sqrt (μ * s) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hμs
      _ = 1 := Real.sqrt_one
  rw [← hu]
  have e : 2 * μ * s = 2 * u ^ 2 := by rw [hu2]; ring
  rw [e, ← hu2]
  have h1 : (3 - 2 * u + u ^ 2) / (2 * (1 + u) ^ 3) + 2 * u ^ 2 / (1 + u) < 3 / 2 := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos (mul_pos hu0 (by linarith : 0 < 1 + u))
      (show 0 < 11 + 4 * u - 5 * u ^ 2 - 4 * u ^ 3 by nlinarith [sq_nonneg u, mul_pos hu0 hu0])]
  linarith
