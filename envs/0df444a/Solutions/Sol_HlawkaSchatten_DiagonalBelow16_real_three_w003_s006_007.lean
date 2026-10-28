-- Prove2me | solution 1 for HlawkaSchatten.DiagonalBelow16.real_three_w003_s006_007
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T00:51:39.229106+00:00
-- url     : https://prove2.me/submissions/0a8b236e-8615-4c07-8302-31e12191b4d6

import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w003_s006_006
import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w003_s007_007
import Mathlib.Tactic.Linarith
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem solution :
    ∀ p : ℝ, (4095/256 : ℝ) ≤ p → p ≤ (16 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  intro p hp hq
  by_cases h : p ≤ (8191/512 : ℝ)
  · exact HlawkaSchatten.DiagonalBelow16.real_three_w003_s006_006 p (by linarith) h
  exact HlawkaSchatten.DiagonalBelow16.real_three_w003_s007_007 p (by linarith) hq

#print axioms solution
