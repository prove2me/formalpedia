-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff16.real_three_window13
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:08:51.68132+00:00
-- url     : https://prove2.me/submissions/4ceacc99-2705-46b0-b438-b4c148fdeb98

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w013_s000_001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w013_s002_003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w013_s004_005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w013_s006_007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w013_s008_009
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w013_s010_011
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w013_s012_013
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w013_s014_015
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution :
    ∀ p : ℝ, (133/8 : ℝ) ≤ p → p ≤ (67/4 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by

  intro p hpa hpb
  by_cases h0 : p ≤ (1065/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w013_s000_001 p (by linarith) h0
  by_cases h1 : p ≤ (533/32 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w013_s002_003 p (by linarith) h1
  by_cases h2 : p ≤ (1067/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w013_s004_005 p (by linarith) h2
  by_cases h3 : p ≤ (267/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w013_s006_007 p (by linarith) h3
  by_cases h4 : p ≤ (1069/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w013_s008_009 p (by linarith) h4
  by_cases h5 : p ≤ (535/32 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w013_s010_011 p (by linarith) h5
  by_cases h6 : p ≤ (1071/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w013_s012_013 p (by linarith) h6
  exact HlawkaSchatten.DiagonalCutoff16.real_three_w013_s014_015 p (by linarith) hpb
#print axioms solution
