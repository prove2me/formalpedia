-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff16.real_three_window17
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:11:32.942748+00:00
-- url     : https://prove2.me/submissions/a017a30a-a3d5-4ec8-9b8e-86203acb4597

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w017_s000_001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w017_s002_003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w017_s004_005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w017_s006_007
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution :
    ∀ p : ℝ, (69/4 : ℝ) ≤ p → p ≤ (35/2 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by

  intro p hpa hpb
  by_cases h0 : p ≤ (277/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w017_s000_001 p (by linarith) h0
  by_cases h1 : p ≤ (139/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w017_s002_003 p (by linarith) h1
  by_cases h2 : p ≤ (279/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w017_s004_005 p (by linarith) h2
  exact HlawkaSchatten.DiagonalCutoff16.real_three_w017_s006_007 p (by linarith) hpb
#print axioms solution
