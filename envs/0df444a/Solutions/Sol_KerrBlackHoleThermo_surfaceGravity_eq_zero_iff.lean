-- Prove2me | solution 1 for KerrBlackHoleThermo.surfaceGravity_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T17:49:33.244729+00:00
-- url     : https://prove2.me/submissions/f98b98b2-1a69-459c-b35f-0c226ff18a13

import Mathlib
import Definitions.Def_KerrBlackHoleThermo_Defs

open Real KerrBlackHoleThermo in
theorem solution (M a : ℝ) (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) :
    surfaceGravity M a = 0 ↔ |angMom M a| = M ^ 2 := by
  have hs := Real.sqrt_nonneg (M ^ 2 - a ^ 2)
  have hden : 0 < 2 * M * (M + √(M ^ 2 - a ^ 2)) := by positivity
  unfold surfaceGravity angMom
  rw [div_eq_zero_iff, abs_mul, abs_of_pos hM]
  constructor
  · rintro (h | h)
    · rw [Real.sqrt_eq_zero'] at h
      have h2 : a ^ 2 = M ^ 2 := by linarith
      have h3 : |a| = M := by
        rw [← abs_of_pos hM]
        exact sq_eq_sq_iff_abs_eq_abs a M |>.mp h2
      rw [h3]; ring
    · exact absurd h hden.ne'
  · intro h
    left
    have h1 : |a| = M := by
      have h' : M * |a| = M * M := by rw [h]; ring
      exact mul_left_cancel₀ hM.ne' h'
    rw [Real.sqrt_eq_zero']
    have h2 : a ^ 2 = M ^ 2 := by rw [← sq_abs, h1]
    linarith
