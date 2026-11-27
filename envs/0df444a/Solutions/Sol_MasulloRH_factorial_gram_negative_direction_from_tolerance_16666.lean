-- Prove2me | solution 1 for MasulloRH.factorial_gram_negative_direction_from_tolerance_16666
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T00:18:46.149333+00:00
-- url     : https://prove2.me/submissions/8b1f04a0-67ff-42dc-8313-d51bb81a18d7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_factorial_grid_four_passes_first_32_billion_gaussian_tests
import Theorems.Thm_MasulloRH_factorial_gram_negative_direction_from_32_billion

open MasulloRH MasulloRH.RationalThetaGrid
theorem solution : ∀ j : ℕ, 16666 ≤ j → ∃ n : ℕ, passes j n := by
  intro j _
  by_cases h : j < 32000000000
  · exact ⟨4,factorial_grid_four_passes_first_32_billion_gaussian_tests j h⟩
  · exact factorial_gram_negative_direction_from_32_billion j (by omega)
