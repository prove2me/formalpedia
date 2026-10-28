-- Prove2me | solution 1 for HlawkaSchatten.DiagonalConstruction.campaign_cutoff2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T18:08:43.642759+00:00
-- url     : https://prove2.me/submissions/e091e1d6-c89c-453b-83e7-e2c44fab8936
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff_real_bound2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff_cutoff16
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_complex_least_of_real_three

set_option autoImplicit false

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

/-- Reduction to the existing real admissibility milestone below 16.
The imported real_bound2 theorem is still open. -/
theorem solution :
    ∀ p : ℝ, 2 ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C}
        (cyclicConstant p) := by
  intro p hp
  by_cases hp16 : 16 ≤ p
  · exact HlawkaSchatten.DiagonalCutoff.cutoff16 p hp16
  · apply HlawkaSchatten.DiagonalCutoff21.complex_least_of_real_three p
    · linarith
    · exact HlawkaSchatten.DiagonalCutoff.real_bound2 p hp 3
