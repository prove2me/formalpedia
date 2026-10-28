-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff.real_bound_below6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-28T01:35:07.084852+00:00
-- url     : https://prove2.me/submissions/5fb977b8-b72a-40b1-9263-ade21093b9e9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclicConstant_ge_one
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_real_bound_of_fin_three
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_two_to_four
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_four_to_six

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem solution :
    ∀ p : ℝ, 2 ≤ p → p ≤ 6 → ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ) (cyclicConstant p) := by
  intro p hp2 hp6 n
  have hp1 : (1 : ℝ) < p := by linarith
  have hhalf : (1 / 2 : ℝ) ≤ cyclicConstant p := by
    have h := HlawkaSchatten.DiagonalConstruction.cyclicConstant_ge_one hp1
    linarith
  by_cases h4 : p ≤ 4
  · exact HlawkaSchatten.DiagonalConstruction.real_bound_of_fin_three hp1 hhalf
      (HlawkaSchatten.DiagonalCutoff4.real_three_two_to_four p hp2 h4)
  · push Not at h4
    exact HlawkaSchatten.DiagonalConstruction.real_bound_of_fin_three hp1 hhalf
      (HlawkaSchatten.DiagonalCutoff4.real_three_four_to_six p (le_of_lt h4) hp6)
