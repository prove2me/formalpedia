-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff16.real_three_window23
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:15:36.02466+00:00
-- url     : https://prove2.me/submissions/7a3d69b4-1857-4cd8-bfaf-997cb772ea6e

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w023_s000_001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w023_s002_003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w023_s004_005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w023_s006_007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w023_s008_009
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w023_s010_011
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w023_s012_013
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w023_s014_015
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution :
    ∀ p : ℝ, (39/2 : ℝ) ≤ p → p ≤ (20 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by

  intro p hpa hpb
  by_cases h0 : p ≤ (313/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w023_s000_001 p (by linarith) h0
  by_cases h1 : p ≤ (157/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w023_s002_003 p (by linarith) h1
  by_cases h2 : p ≤ (315/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w023_s004_005 p (by linarith) h2
  by_cases h3 : p ≤ (79/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w023_s006_007 p (by linarith) h3
  by_cases h4 : p ≤ (317/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w023_s008_009 p (by linarith) h4
  by_cases h5 : p ≤ (159/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w023_s010_011 p (by linarith) h5
  by_cases h6 : p ≤ (319/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w023_s012_013 p (by linarith) h6
  exact HlawkaSchatten.DiagonalCutoff16.real_three_w023_s014_015 p (by linarith) hpb
#print axioms solution
