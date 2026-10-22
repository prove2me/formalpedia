-- Prove2me | solution 1 for NonsmoothQN.Secant.armijo_wolfe_sign_flip
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:41:38.89326+00:00
-- url     : https://prove2.me/submissions/16100ae0-28e4-4e98-81f7-36e43cf61fea

import Mathlib
import Definitions.Def_NonsmoothQN_Secant_Basic
import Definitions.Def_NonsmoothQN_Secant_Expansion
set_option autoImplicit false
open NonsmoothQN.Secant

theorem solution (x p t : ℝ) (hx : x ≠ 0) (hpx : p * x < 0)
    (hA : secA x p t) (hW : secW x p t) (hx' : x + t * p ≠ 0) :
    |x + t * p| < |x| ∧ x * (x + t * p) < 0 := by
  unfold secA at hA
  unfold secW at hW
  have hp : p ≠ 0 := by rintro rfl; simp at hpx
  rcases lt_or_gt_of_ne hp with hp | hp
  · -- p < 0, hence x > 0
    have hxpos : 0 < x := by nlinarith
    rw [lt_div_iff_of_neg hp] at hA
    rw [div_le_iff_of_neg hp] at hW
    have h1 : x + t * p ≤ 0 := by nlinarith
    have h2 : -x < x + t * p := by nlinarith
    have h3 : x + t * p < 0 := lt_of_le_of_ne h1 hx'
    refine ⟨?_, by nlinarith⟩
    rw [abs_of_pos hxpos, abs_of_neg h3]; linarith
  · -- p > 0, hence x < 0
    have hxneg : x < 0 := by nlinarith
    rw [lt_div_iff₀ hp] at hA
    rw [div_le_iff₀ hp] at hW
    have h1 : 0 ≤ x + t * p := by nlinarith
    have h2 : x + t * p < -x := by nlinarith
    have h3 : 0 < x + t * p := lt_of_le_of_ne h1 (Ne.symm hx')
    refine ⟨?_, by nlinarith⟩
    rw [abs_of_neg hxneg, abs_of_pos h3]; linarith
