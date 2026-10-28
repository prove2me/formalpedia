-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff16.real_three_window06
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T00:47:19.905112+00:00
-- url     : https://prove2.me/submissions/f4b6b354-6aa8-4f0f-8bb9-ef03036e2a4d

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w006_s000_001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w006_s002_003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w006_s004_005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w006_s006_007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w006_s008_009
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w006_s010_011
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w006_s012_013
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w006_s014_015
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution :
    ∀ p : ℝ, (259/16 : ℝ) ≤ p → p ≤ (519/32 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by

  intro p hpa hpb
  by_cases h0 : p ≤ (4145/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w006_s000_001 p (by linarith) h0
  by_cases h1 : p ≤ (2073/128 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w006_s002_003 p (by linarith) h1
  by_cases h2 : p ≤ (4147/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w006_s004_005 p (by linarith) h2
  by_cases h3 : p ≤ (1037/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w006_s006_007 p (by linarith) h3
  by_cases h4 : p ≤ (4149/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w006_s008_009 p (by linarith) h4
  by_cases h5 : p ≤ (2075/128 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w006_s010_011 p (by linarith) h5
  by_cases h6 : p ≤ (4151/256 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w006_s012_013 p (by linarith) h6
  exact HlawkaSchatten.DiagonalCutoff16.real_three_w006_s014_015 p (by linarith) hpb
#print axioms solution
