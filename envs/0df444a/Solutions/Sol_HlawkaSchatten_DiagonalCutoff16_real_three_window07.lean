-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff16.real_three_window07
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T00:47:40.742017+00:00
-- url     : https://prove2.me/submissions/ff5f8ffd-57d5-4431-8cf1-c4a68806bff8

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w007_s000_001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w007_s002_003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w007_s004_005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w007_s006_007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w007_s008_009
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w007_s010_011
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w007_s012_013
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w007_s014_015
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution :
    ∀ p : ℝ, (519/32 : ℝ) ≤ p → p ≤ (65/4 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by

  intro p hpa hpb
  by_cases h0 : p ≤ (4153/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w007_s000_001 p (by linarith) h0
  by_cases h1 : p ≤ (2077/128 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w007_s002_003 p (by linarith) h1
  by_cases h2 : p ≤ (4155/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w007_s004_005 p (by linarith) h2
  by_cases h3 : p ≤ (1039/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w007_s006_007 p (by linarith) h3
  by_cases h4 : p ≤ (4157/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w007_s008_009 p (by linarith) h4
  by_cases h5 : p ≤ (2079/128 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w007_s010_011 p (by linarith) h5
  by_cases h6 : p ≤ (4159/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w007_s012_013 p (by linarith) h6
  exact HlawkaSchatten.DiagonalCutoff16.real_three_w007_s014_015 p (by linarith) hpb
#print axioms solution
