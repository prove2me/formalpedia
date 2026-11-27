-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.progY_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:45:59.407651+00:00
-- url     : https://prove2.me/submissions/ba4f33da-e5d0-41ee-af74-08ed7eb08474

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_ProgYInjective
import Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_progY_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.BlockD GroundTheory.BlockD.FourierDecayAlt GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
open Finset
namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
theorem _root_.solution (y0 : ℝ) (M : ℕ) : (progY y0 M).card = M := by
  unfold progY
  rw [card_image_of_injective _ (progY_injective y0), card_range]
end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
