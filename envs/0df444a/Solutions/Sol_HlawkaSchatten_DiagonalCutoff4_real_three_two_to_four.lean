-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_three_two_to_four
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-28T01:37:03.671098+00:00
-- url     : https://prove2.me/submissions/5baa99a4-f95b-472e-9ede-d8fb6cd89643
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HlawkaSchatten_LpThreshold_cyclicConstant_le_one_below
import Theorems.Thm_HlawkaSchatten_LpThreshold_hlawka_holds_below
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_threshold_to_four
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclicConstant_ge_one

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem solution :
    ∀ p : ℝ, 2 ≤ p → p ≤ 4 →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  intro p hp2 hp4
  by_cases hT : p ≤ Real.log 3 / Real.log (3 / 2)
  · have hle : cyclicConstant p ≤ 1 :=
      HlawkaSchatten.LpThreshold.cyclicConstant_le_one_below p hp2 hT
    have hge : 1 ≤ cyclicConstant p :=
      HlawkaSchatten.DiagonalConstruction.cyclicConstant_ge_one (by linarith)
    rw [le_antisymm hle hge]
    exact HlawkaSchatten.LpThreshold.hlawka_holds_below p hp2 hT 3
  · push Not at hT
    exact HlawkaSchatten.DiagonalCutoff4.real_three_threshold_to_four p (le_of_lt hT) hp4
