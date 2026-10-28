-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff16.real_three_window14
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:09:11.301992+00:00
-- url     : https://prove2.me/submissions/89adda96-c7b9-43d1-9add-7b9d859bf471

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w014_s000_001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w014_s002_003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w014_s004_005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w014_s006_007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w014_s008_009
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w014_s010_011
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w014_s012_013
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w014_s014_015
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution :
    ∀ p : ℝ, (67/4 : ℝ) ≤ p → p ≤ (135/8 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by

  intro p hpa hpb
  by_cases h0 : p ≤ (1073/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w014_s000_001 p (by linarith) h0
  by_cases h1 : p ≤ (537/32 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w014_s002_003 p (by linarith) h1
  by_cases h2 : p ≤ (1075/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w014_s004_005 p (by linarith) h2
  by_cases h3 : p ≤ (269/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w014_s006_007 p (by linarith) h3
  by_cases h4 : p ≤ (1077/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w014_s008_009 p (by linarith) h4
  by_cases h5 : p ≤ (539/32 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w014_s010_011 p (by linarith) h5
  by_cases h6 : p ≤ (1079/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w014_s012_013 p (by linarith) h6
  exact HlawkaSchatten.DiagonalCutoff16.real_three_w014_s014_015 p (by linarith) hpb
#print axioms solution
