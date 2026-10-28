-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff16.real_three_window24
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:15:50.875834+00:00
-- url     : https://prove2.me/submissions/db90ad08-fbb1-42ad-a3f9-a07d96e7b8e0

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w024_s000_001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w024_s002_003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w024_s004_005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w024_s006_007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w024_s008_009
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w024_s010_011
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w024_s012_013
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w024_s014_015
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution :
    ∀ p : ℝ, (20 : ℝ) ≤ p → p ≤ (21 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by

  intro p hpa hpb
  by_cases h0 : p ≤ (161/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w024_s000_001 p (by linarith) h0
  by_cases h1 : p ≤ (81/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w024_s002_003 p (by linarith) h1
  by_cases h2 : p ≤ (163/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w024_s004_005 p (by linarith) h2
  by_cases h3 : p ≤ (41/2 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w024_s006_007 p (by linarith) h3
  by_cases h4 : p ≤ (165/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w024_s008_009 p (by linarith) h4
  by_cases h5 : p ≤ (83/4 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w024_s010_011 p (by linarith) h5
  by_cases h6 : p ≤ (167/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w024_s012_013 p (by linarith) h6
  exact HlawkaSchatten.DiagonalCutoff16.real_three_w024_s014_015 p (by linarith) hpb
#print axioms solution
