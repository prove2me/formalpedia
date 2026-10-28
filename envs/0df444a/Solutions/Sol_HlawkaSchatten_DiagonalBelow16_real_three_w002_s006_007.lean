-- Prove2me | solution 1 for HlawkaSchatten.DiagonalBelow16.real_three_w002_s006_007
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T00:49:32.48112+00:00
-- url     : https://prove2.me/submissions/c3b14459-1f12-4c87-9a51-bff389ed2633

import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w002_s006_006
import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w002_s007_007
import Mathlib.Tactic.Linarith
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem solution :
    ∀ p : ℝ, (4091/256 : ℝ) ≤ p → p ≤ (1023/64 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  intro p hp hq
  by_cases h : p ≤ (8183/512 : ℝ)
  · exact HlawkaSchatten.DiagonalBelow16.real_three_w002_s006_006 p (by linarith) h
  exact HlawkaSchatten.DiagonalBelow16.real_three_w002_s007_007 p (by linarith) hq

#print axioms solution
