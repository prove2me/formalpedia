-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff16.real_three_window21
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:14:04.668602+00:00
-- url     : https://prove2.me/submissions/b698ac8d-ec6a-4b3e-ba81-eadcad4fc9b7

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w021_s000_001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w021_s002_003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w021_s004_005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w021_s006_007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w021_s008_009
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w021_s010_011
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w021_s012_013
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w021_s014_015
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution :
    ∀ p : ℝ, (37/2 : ℝ) ≤ p → p ≤ (19 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by

  intro p hpa hpb
  by_cases h0 : p ≤ (297/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w021_s000_001 p (by linarith) h0
  by_cases h1 : p ≤ (149/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w021_s002_003 p (by linarith) h1
  by_cases h2 : p ≤ (299/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w021_s004_005 p (by linarith) h2
  by_cases h3 : p ≤ (75/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w021_s006_007 p (by linarith) h3
  by_cases h4 : p ≤ (301/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w021_s008_009 p (by linarith) h4
  by_cases h5 : p ≤ (151/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w021_s010_011 p (by linarith) h5
  by_cases h6 : p ≤ (303/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w021_s012_013 p (by linarith) h6
  exact HlawkaSchatten.DiagonalCutoff16.real_three_w021_s014_015 p (by linarith) hpb
#print axioms solution
