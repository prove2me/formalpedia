-- Prove2me | solution 1 for HlawkaSchatten.DiagonalBelow16.real_three_w002_s004_005
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T00:49:31.913429+00:00
-- url     : https://prove2.me/submissions/af2ba825-112d-472a-be17-327f131ed71e

import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w002_s004_004
import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w002_s005_005
import Mathlib.Tactic.Linarith
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem solution :
    ∀ p : ℝ, (2045/128 : ℝ) ≤ p → p ≤ (4091/256 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  intro p hp hq
  by_cases h : p ≤ (8181/512 : ℝ)
  · exact HlawkaSchatten.DiagonalBelow16.real_three_w002_s004_004 p (by linarith) h
  exact HlawkaSchatten.DiagonalBelow16.real_three_w002_s005_005 p (by linarith) hq

#print axioms solution
