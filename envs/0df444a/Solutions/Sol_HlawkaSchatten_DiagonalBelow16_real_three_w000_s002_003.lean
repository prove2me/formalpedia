-- Prove2me | solution 1 for HlawkaSchatten.DiagonalBelow16.real_three_w000_s002_003
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T00:42:32.224112+00:00
-- url     : https://prove2.me/submissions/b7d6bf69-9fc0-4677-87f8-26bc1ce20d19

import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w000_s002_002
import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w000_s003_003
import Mathlib.Tactic.Linarith
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem solution :
    ∀ p : ℝ, (4081/256 : ℝ) ≤ p → p ≤ (2041/128 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  intro p hp hq
  by_cases h : p ≤ (8163/512 : ℝ)
  · exact HlawkaSchatten.DiagonalBelow16.real_three_w000_s002_002 p (by linarith) h
  exact HlawkaSchatten.DiagonalBelow16.real_three_w000_s003_003 p (by linarith) hq

#print axioms solution
