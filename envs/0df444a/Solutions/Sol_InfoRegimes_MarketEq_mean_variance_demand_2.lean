-- Prove2me | solution 2 for InfoRegimes.MarketEq.mean_variance_demand
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:27:07.432835+00:00
-- url     : https://prove2.me/submissions/8e3ef45f-588b-4835-982a-0263028e26ef

import Mathlib
set_option autoImplicit false

theorem solution (γ qD qN q : ℝ) (hγ : 0 < γ) (hqD : 0 < qD) :
    IsMaxOn (fun x : ℝ => x * qN - γ / 2 * x ^ 2 * qD) Set.univ q ↔ q = qN / (γ * qD) := by
  have hc : 0 < γ * qD := mul_pos hγ hqD
  set q0 := qN / (γ * qD) with hq0def
  have hq0 : qN = q0 * (γ * qD) := by rw [hq0def]; field_simp
  have key : ∀ x : ℝ, x * qN - γ / 2 * x ^ 2 * qD
      = q0 * qN - γ / 2 * q0 ^ 2 * qD - (γ * qD / 2) * (x - q0) ^ 2 := by
    intro x
    rw [hq0]
    ring
  rw [isMaxOn_iff]
  constructor
  · intro h
    have h1 := h q0 (Set.mem_univ _)
    rw [key q, key q0] at h1
    have : (γ * qD / 2) * (q - q0) ^ 2 ≤ 0 := by nlinarith
    have h2 : (q - q0) ^ 2 ≤ 0 := by
      by_contra hh
      push_neg at hh
      have : 0 < (γ * qD / 2) * (q - q0) ^ 2 := mul_pos (by positivity) hh
      linarith
    have : q - q0 = 0 := by nlinarith [sq_nonneg (q - q0)]
    linarith
  · intro h x _
    subst h
    rw [key x, key q0]
    have : 0 ≤ (γ * qD / 2) * (x - q0) ^ 2 := by positivity
    nlinarith
