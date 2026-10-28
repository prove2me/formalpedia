-- Prove2me | solution 1 for HlawkaSchatten.DiagonalBelow16.real_three_w003_s002_003
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T00:51:37.991916+00:00
-- url     : https://prove2.me/submissions/fb83fefe-8cf0-41b7-ae51-f5cc09a721a7

import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w003_s002_002
import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w003_s003_003
import Mathlib.Tactic.Linarith
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem solution :
    ∀ p : ℝ, (4093/256 : ℝ) ≤ p → p ≤ (2047/128 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  intro p hp hq
  by_cases h : p ≤ (8187/512 : ℝ)
  · exact HlawkaSchatten.DiagonalBelow16.real_three_w003_s002_002 p (by linarith) h
  exact HlawkaSchatten.DiagonalBelow16.real_three_w003_s003_003 p (by linarith) hq

#print axioms solution
