-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff16.real_three_window19
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:12:42.441351+00:00
-- url     : https://prove2.me/submissions/707d7979-8628-47cb-b56a-604063fd3578

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w019_s000_001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w019_s002_003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w019_s004_005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w019_s006_007
import Mathlib.Tactic.Linarith
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution :
    ∀ p : ℝ, (71/4 : ℝ) ≤ p → p ≤ (18 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by

  intro p hpa hpb
  by_cases h0 : p ≤ (285/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w019_s000_001 p (by linarith) h0
  by_cases h1 : p ≤ (143/8 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w019_s002_003 p (by linarith) h1
  by_cases h2 : p ≤ (287/16 : ℝ)
  · exact HlawkaSchatten.DiagonalCutoff16.real_three_w019_s004_005 p (by linarith) h2
  exact HlawkaSchatten.DiagonalCutoff16.real_three_w019_s006_007 p (by linarith) hpb
#print axioms solution
