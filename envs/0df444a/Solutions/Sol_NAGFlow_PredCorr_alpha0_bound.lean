-- Prove2me | solution 1 for NAGFlow.PredCorr.alpha0_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T19:33:45.574828+00:00
-- url     : https://prove2.me/submissions/a4b67c0f-17af-45a6-8d5a-fb57635b0eba

import Mathlib

set_option autoImplicit false

theorem solution (L γ0 α0 : ℝ) (hL : 0 < L) (hγ0 : 0 < γ0) (hα0 : 0 < α0)
    (hrel : L * α0 ^ 2 = γ0 * (1 + α0)) :
    α0 = (γ0 + Real.sqrt (4 * γ0 * L + γ0 ^ 2)) / (2 * L) ∧
      1 / (1 + α0) = 2 * L / (γ0 + 2 * L + Real.sqrt (4 * γ0 * L + γ0 ^ 2)) ∧
      1 / (1 + α0) ≤ L / γ0 := by
  have hLa : γ0 < L * α0 := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_pos hL hα0, mul_pos hγ0 hα0]
  have hs : Real.sqrt (4 * γ0 * L + γ0 ^ 2) = 2 * L * α0 - γ0 := by
    have : 4 * γ0 * L + γ0 ^ 2 = (2 * L * α0 - γ0) ^ 2 := by nlinarith
    rw [this]
    exact Real.sqrt_sq (by linarith)
  rw [hs]
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    ring
  · have : γ0 + 2 * L + (2 * L * α0 - γ0) = 2 * L * (1 + α0) := by ring
    rw [this]
    field_simp
  · rw [div_le_div_iff₀ (by positivity) hγ0]
    nlinarith
