-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff16.real_three_window20
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:12:57.576849+00:00
-- url     : https://prove2.me/submissions/bacb1fa6-dd51-4348-85a2-cfaddd08ff17

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w020_s000_001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w020_s002_003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w020_s004_005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w020_s006_007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w020_s008_009
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w020_s010_011
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w020_s012_013
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w020_s014_015
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution :
    ∀ p : ℝ, (18 : ℝ) ≤ p → p ≤ (37/2 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by

  intro p hpa hpb
  by_cases h0 : p ≤ (289/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w020_s000_001 p (by linarith) h0
  by_cases h1 : p ≤ (145/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w020_s002_003 p (by linarith) h1
  by_cases h2 : p ≤ (291/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w020_s004_005 p (by linarith) h2
  by_cases h3 : p ≤ (73/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w020_s006_007 p (by linarith) h3
  by_cases h4 : p ≤ (293/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w020_s008_009 p (by linarith) h4
  by_cases h5 : p ≤ (147/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w020_s010_011 p (by linarith) h5
  by_cases h6 : p ≤ (295/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w020_s012_013 p (by linarith) h6
  exact HlawkaSchatten.DiagonalCutoff16.real_three_w020_s014_015 p (by linarith) hpb
#print axioms solution
