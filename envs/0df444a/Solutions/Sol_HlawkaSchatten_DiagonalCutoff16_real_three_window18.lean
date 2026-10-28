-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff16.real_three_window18
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:11:51.753845+00:00
-- url     : https://prove2.me/submissions/dea8b54f-4c99-4167-9331-97a595640a4e

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w018_s000_001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w018_s002_003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w018_s004_005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w018_s006_007
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution :
    ∀ p : ℝ, (35/2 : ℝ) ≤ p → p ≤ (71/4 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by

  intro p hpa hpb
  by_cases h0 : p ≤ (281/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w018_s000_001 p (by linarith) h0
  by_cases h1 : p ≤ (141/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w018_s002_003 p (by linarith) h1
  by_cases h2 : p ≤ (283/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w018_s004_005 p (by linarith) h2
  exact HlawkaSchatten.DiagonalCutoff16.real_three_w018_s006_007 p (by linarith) hpb
#print axioms solution
