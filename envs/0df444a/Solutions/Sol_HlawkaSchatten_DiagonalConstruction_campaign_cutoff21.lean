-- Prove2me | solution 1 for HlawkaSchatten.DiagonalConstruction.campaign_cutoff21
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-17T13:42:07.431725+00:00
-- url     : https://prove2.me/submissions/ff1e7441-f309-4dbf-818c-d22a272a1abb

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_real_three_window21
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_real_three_window26
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_complex_least_of_real_three
import Mathlib.Tactic.Linarith
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_campaign_cutoff32
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff21

theorem solution :
    ∀ p : ℝ, 21 ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C}
        (cyclicConstant p) := by
  intro p hp
  by_cases hp32 : 32 ≤ p
  · exact campaign_cutoff32 p hp32
  · apply complex_least_of_real_three p (by linarith)
    by_cases hp26 : p ≤ 26
    · exact real_three_window21 p hp hp26
    · exact real_three_window26 p (by linarith) (by linarith)

#print axioms solution
