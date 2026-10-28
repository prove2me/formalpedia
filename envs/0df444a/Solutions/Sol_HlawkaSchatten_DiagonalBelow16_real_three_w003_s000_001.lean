-- Prove2me | solution 1 for HlawkaSchatten.DiagonalBelow16.real_three_w003_s000_001
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T00:51:37.028798+00:00
-- url     : https://prove2.me/submissions/9bc35884-486a-4bfd-9a42-4ed9a7f85cd2

import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w003_s000_000
import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w003_s001_001
import Mathlib.Tactic.Linarith
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem solution :
    ∀ p : ℝ, (1023/64 : ℝ) ≤ p → p ≤ (4093/256 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  intro p hp hq
  by_cases h : p ≤ (8185/512 : ℝ)
  · exact HlawkaSchatten.DiagonalBelow16.real_three_w003_s000_000 p (by linarith) h
  exact HlawkaSchatten.DiagonalBelow16.real_three_w003_s001_001 p (by linarith) hq

#print axioms solution
