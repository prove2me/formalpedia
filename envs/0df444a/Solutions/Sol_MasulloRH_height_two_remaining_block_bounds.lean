-- Prove2me | solution 1 for MasulloRH.height_two_remaining_block_bounds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T11:28:21.819909+00:00
-- url     : https://prove2.me/submissions/e94cae4c-f21a-4ed7-9fba-820fd58daf50
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_height_two_exterior_energy_bounds
import Theorems.Thm_MasulloRH_height_two_interior_block_bounds
import Definitions.Def_MasulloRH_HeightTwoComputedGrid
import Definitions.Def_MasulloRH_HeightTwoBlockBudgets

open MasulloRH.ComputedGrid MasulloRH.BlockBudgets
open scoped BigOperators
set_option autoImplicit false

theorem solution :
    ∀ b ∈ Finset.range 1024, b ≠ 512 →
      (∑ j ∈ Finset.range 64, energyTerm (b*64+j)) ≤ cap b := by 
  intro b hb hmid
  by_cases houter : b < 80 ∨ 1008 ≤ b
  · exact MasulloRH.height_two_exterior_energy_bounds.2.1 b hb houter
  · apply MasulloRH.height_two_interior_block_bounds b _ hmid
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
