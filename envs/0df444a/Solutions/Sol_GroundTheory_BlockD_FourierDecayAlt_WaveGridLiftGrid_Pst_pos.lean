-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.Pst_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:44:41.441328+00:00
-- url     : https://prove2.me/submissions/b2c53fdf-75f8-4cb7-a1ee-82cde5b99411

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_PairOKOfInterlace

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
theorem _root_.solution (k r : ℕ) (lam : ℕ → ℝ) {c : ℝ} (hc : 0 < c) (Y : ℝ) : 0 < Pst k r lam c Y := by
  unfold Pst
  exact Finset.prod_pos fun s _ => add_pos_of_nonneg_of_pos (abs_nonneg _) hc
end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
