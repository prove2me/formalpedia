-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff16.real_three_window00
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T00:29:15.256476+00:00
-- url     : https://prove2.me/submissions/e4d163b7-4aa7-4a2f-a4d5-5c796ba2c3c0

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w000_s000_000
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w000_s001_002
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w000_s003_004
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w000_s005_006
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w000_s007_008
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w000_s009_010
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w000_s011_012
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w000_s013_014
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w000_s015_015
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution :
    ∀ p : ℝ, (16 : ℝ) ≤ p → p ≤ (513/32 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by

  intro p hpa hpb
  by_cases h0 : p ≤ (8193/512 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w000_s000_000 p (by linarith) h0
  by_cases h1 : p ≤ (8195/512 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w000_s001_002 p (by linarith) h1
  by_cases h2 : p ≤ (8197/512 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w000_s003_004 p (by linarith) h2
  by_cases h3 : p ≤ (8199/512 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w000_s005_006 p (by linarith) h3
  by_cases h4 : p ≤ (8201/512 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w000_s007_008 p (by linarith) h4
  by_cases h5 : p ≤ (8203/512 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w000_s009_010 p (by linarith) h5
  by_cases h6 : p ≤ (8205/512 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w000_s011_012 p (by linarith) h6
  by_cases h7 : p ≤ (8207/512 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w000_s013_014 p (by linarith) h7
  exact HlawkaSchatten.DiagonalCutoff16.real_three_w000_s015_015 p (by linarith) hpb
#print axioms solution
