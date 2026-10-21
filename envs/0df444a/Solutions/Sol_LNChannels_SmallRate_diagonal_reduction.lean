-- Prove2me | solution 1 for LNChannels.SmallRate.diagonal_reduction
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:17:49.712968+00:00
-- url     : https://prove2.me/submissions/a4dffdfd-c4df-4b9c-b06c-b46e221b9ee6

import Mathlib

set_option autoImplicit false

theorem solution (a B l₁ l₂ : ℝ) (ha : 1 < a) (hB : 0 ≤ B)
    (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) :
    let G : ℝ → ℝ → ℝ := fun x y =>
      x + y + B * (a ^ x + a ^ y) / ((a ^ x - 1) * (a ^ y - 1))
    let m := (l₁ + l₂) / 2
    G m m ≤ G l₁ l₂ ∧
      G m m = 2 * m + 2 * B * a ^ m / (a ^ m - 1) ^ 2 := by
  intro G m
  have hm : 0 < m := by simp only [m]; linarith
  have hu : 1 < a ^ l₁ := Real.one_lt_rpow ha hl₁
  have hv : 1 < a ^ l₂ := Real.one_lt_rpow ha hl₂
  have hw : 1 < a ^ m := Real.one_lt_rpow ha hm
  generalize hu' : a ^ l₁ = u at hu
  generalize hv' : a ^ l₂ = v at hv
  have hww : a ^ m * a ^ m = u * v := by
    rw [← Real.rpow_add (by linarith), ← hu', ← hv', ← Real.rpow_add (by linarith)]
    congr 1
    simp only [m]; ring
  have hGmm : G m m = 2 * m + 2 * B * a ^ m / (a ^ m - 1) ^ 2 := by
    simp only [G]
    have : a ^ m - 1 ≠ 0 := by linarith
    field_simp
    ring
  refine ⟨?_, hGmm⟩
  rw [hGmm]
  simp only [G, hu', hv']
  have hmsum : m + m = l₁ + l₂ := by simp only [m]; ring
  have hsum : l₁ + l₂ = l₁ + l₂ := rfl
  generalize a ^ m = w at hw hww
  have hamgm : 2 * w ≤ u + v := by nlinarith [sq_nonneg (u - v), sq_nonneg (u + v - 2 * w)]
  have key : 2 * w * ((u - 1) * (v - 1)) ≤ (u + v) * (w - 1) ^ 2 := by
    have h1 : (u + v) * (w - 1) ^ 2 - 2 * w * ((u - 1) * (v - 1))
        = (u + v - 2 * w) * (w ^ 2 + 1) + 2 * w * (w * w - u * v) := by ring
    have h2 : 0 ≤ (u + v - 2 * w) * (w ^ 2 + 1) :=
      mul_nonneg (by linarith) (by positivity)
    rw [hww] at h1
    nlinarith
  have hfrac : 2 * B * w / (w - 1) ^ 2 ≤ B * (u + v) / ((u - 1) * (v - 1)) := by
    rw [div_le_div_iff₀ (by have : 0 < w - 1 := by linarith
                            positivity) (by have : 0 < u - 1 := by linarith
                                            have : 0 < v - 1 := by linarith
                                            positivity)]
    nlinarith [mul_le_mul_of_nonneg_left key hB]
  have : 2 * m = l₁ + l₂ := by simp only [m]; ring
  linarith
