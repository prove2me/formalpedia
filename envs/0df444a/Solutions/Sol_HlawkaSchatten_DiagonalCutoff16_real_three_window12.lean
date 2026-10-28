-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff16.real_three_window12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:07:49.835084+00:00
-- url     : https://prove2.me/submissions/4ebbe50e-0874-4735-bb4e-1bab898b7ab3

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w012_s000_001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w012_s002_003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w012_s004_005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w012_s006_007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w012_s008_009
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w012_s010_011
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w012_s012_013
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w012_s014_015
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution :
    ∀ p : ℝ, (33/2 : ℝ) ≤ p → p ≤ (133/8 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by

  intro p hpa hpb
  by_cases h0 : p ≤ (1057/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w012_s000_001 p (by linarith) h0
  by_cases h1 : p ≤ (529/32 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w012_s002_003 p (by linarith) h1
  by_cases h2 : p ≤ (1059/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w012_s004_005 p (by linarith) h2
  by_cases h3 : p ≤ (265/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w012_s006_007 p (by linarith) h3
  by_cases h4 : p ≤ (1061/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w012_s008_009 p (by linarith) h4
  by_cases h5 : p ≤ (531/32 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w012_s010_011 p (by linarith) h5
  by_cases h6 : p ≤ (1063/64 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w012_s012_013 p (by linarith) h6
  exact HlawkaSchatten.DiagonalCutoff16.real_three_w012_s014_015 p (by linarith) hpb
#print axioms solution
