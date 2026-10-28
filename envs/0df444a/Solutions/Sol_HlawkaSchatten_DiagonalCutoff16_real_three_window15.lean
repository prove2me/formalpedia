-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff16.real_three_window15
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:10:14.298785+00:00
-- url     : https://prove2.me/submissions/443a87d4-f155-44bc-8ab4-b23691186f49

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w015_s000_001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w015_s002_003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w015_s004_005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w015_s006_007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w015_s008_009
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w015_s010_011
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w015_s012_013
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w015_s014_015
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution :
    ∀ p : ℝ, (135/8 : ℝ) ≤ p → p ≤ (17 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by

  intro p hpa hpb
  by_cases h0 : p ≤ (1081/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w015_s000_001 p (by linarith) h0
  by_cases h1 : p ≤ (541/32 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w015_s002_003 p (by linarith) h1
  by_cases h2 : p ≤ (1083/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w015_s004_005 p (by linarith) h2
  by_cases h3 : p ≤ (271/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w015_s006_007 p (by linarith) h3
  by_cases h4 : p ≤ (1085/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w015_s008_009 p (by linarith) h4
  by_cases h5 : p ≤ (543/32 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w015_s010_011 p (by linarith) h5
  by_cases h6 : p ≤ (1087/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w015_s012_013 p (by linarith) h6
  exact HlawkaSchatten.DiagonalCutoff16.real_three_w015_s014_015 p (by linarith) hpb
#print axioms solution
