-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff16.real_three_window03
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T00:39:57.332279+00:00
-- url     : https://prove2.me/submissions/d05658a7-8920-485a-b365-2a940daea2f7

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w003_s000_001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w003_s002_003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w003_s004_005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w003_s006_007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w003_s008_009
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w003_s010_011
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w003_s012_013
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w003_s014_015
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution :
    ∀ p : ℝ, (515/32 : ℝ) ≤ p → p ≤ (129/8 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by

  intro p hpa hpb
  by_cases h0 : p ≤ (4121/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w003_s000_001 p (by linarith) h0
  by_cases h1 : p ≤ (2061/128 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w003_s002_003 p (by linarith) h1
  by_cases h2 : p ≤ (4123/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w003_s004_005 p (by linarith) h2
  by_cases h3 : p ≤ (1031/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w003_s006_007 p (by linarith) h3
  by_cases h4 : p ≤ (4125/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w003_s008_009 p (by linarith) h4
  by_cases h5 : p ≤ (2063/128 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w003_s010_011 p (by linarith) h5
  by_cases h6 : p ≤ (4127/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w003_s012_013 p (by linarith) h6
  exact HlawkaSchatten.DiagonalCutoff16.real_three_w003_s014_015 p (by linarith) hpb
#print axioms solution
