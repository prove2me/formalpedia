-- Prove2me | solution 1 for LL_Decomp1528b.neg_log_one_sub_inv_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:07.166975+00:00
-- url     : https://prove2.me/submissions/11957dbd-31d0-4b3e-b1b1-be5b05f85f0e

import Mathlib

open Real Finset Filter Topology

theorem ChMeAux.log_le_half_sub_inv {y : ℝ} (hy : 1 ≤ y) : log y ≤ (y - y⁻¹) / 2 := by
  have hmono : MonotoneOn (fun y : ℝ => (y - y⁻¹) / 2 - log y) (Set.Ici 1) := by
    have hd : ∀ y : ℝ, 1 < y → HasDerivAt (fun y : ℝ => (y - y⁻¹) / 2 - log y)
        ((1 + (y ^ 2)⁻¹) / 2 - y⁻¹) y := by
      intro y hy
      have hy0 : y ≠ 0 := by positivity
      have h1 := ((hasDerivAt_id y).sub (hasDerivAt_inv hy0)).div_const 2
      have h2 := h1.sub (Real.hasDerivAt_log hy0)
      exact h2.congr_deriv (by ring)
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · intro y hy
      have : 1 ≤ y := hy
      have hy0 : y ≠ 0 := by positivity
      have h1 := ((hasDerivAt_id y).sub (hasDerivAt_inv hy0)).div_const 2
      have h2 := h1.sub (Real.hasDerivAt_log hy0)
      exact h2.continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact (hd y hy).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hy' : (1 : ℝ) < y := hy
      rw [(hd y hy').deriv]
      have hy0 : 0 < y := by positivity
      have : (1 + (y ^ 2)⁻¹) / 2 - y⁻¹ = (1 - y⁻¹) ^ 2 / 2 := by
        field_simp
        ring
      rw [this]
      positivity
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy) hy
  simp at this
  linarith

theorem solution {p : ℝ} (hp : 2 ≤ p) :
    0 ≤ -log (1 - 1 / p) - 1 / p ∧ -log (1 - 1 / p) - 1 / p ≤ 1 / (2 * p * (p - 1)) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hq : 0 < 1 - 1 / p := by
    rw [sub_pos, div_lt_one hp0]; linarith
  constructor
  · have := Real.log_le_sub_one_of_pos hq
    linarith
  · have hy : (1 : ℝ) ≤ p / (p - 1) := by
      rw [le_div_iff₀ hp1]; linarith
    have h := ChMeAux.log_le_half_sub_inv hy
    have e1 : -log (1 - 1 / p) = log (p / (p - 1)) := by
      rw [← Real.log_inv]
      congr 1
      field_simp
    rw [e1]
    have e2 : (p / (p - 1) - (p / (p - 1))⁻¹) / 2 - 1 / p = 1 / (2 * p * (p - 1)) := by
      field_simp
      ring
    linarith
