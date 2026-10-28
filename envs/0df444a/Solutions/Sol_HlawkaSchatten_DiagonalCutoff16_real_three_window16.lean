-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff16.real_three_window16
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:10:32.957056+00:00
-- url     : https://prove2.me/submissions/139c5362-8e7c-4350-b7c6-9a8a9fae089b

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w016_s000_001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w016_s002_003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w016_s004_005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w016_s006_007
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution :
    ∀ p : ℝ, (17 : ℝ) ≤ p → p ≤ (69/4 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by

  intro p hpa hpb
  by_cases h0 : p ≤ (273/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w016_s000_001 p (by linarith) h0
  by_cases h1 : p ≤ (137/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w016_s002_003 p (by linarith) h1
  by_cases h2 : p ≤ (275/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w016_s004_005 p (by linarith) h2
  exact HlawkaSchatten.DiagonalCutoff16.real_three_w016_s006_007 p (by linarith) hpb
#print axioms solution
