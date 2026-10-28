-- Prove2me | solution 1 for HlawkaSchatten.DiagonalBelow16.real_three_w003_s004_005
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T00:51:38.65491+00:00
-- url     : https://prove2.me/submissions/0dbc4bb0-aedc-44c6-98f2-90faadb32be7

import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w003_s004_004
import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w003_s005_005
import Mathlib.Tactic.Linarith
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem solution :
    ∀ p : ℝ, (2047/128 : ℝ) ≤ p → p ≤ (4095/256 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  intro p hp hq
  by_cases h : p ≤ (8189/512 : ℝ)
  · exact HlawkaSchatten.DiagonalBelow16.real_three_w003_s004_004 p (by linarith) h
  exact HlawkaSchatten.DiagonalBelow16.real_three_w003_s005_005 p (by linarith) hq

#print axioms solution
