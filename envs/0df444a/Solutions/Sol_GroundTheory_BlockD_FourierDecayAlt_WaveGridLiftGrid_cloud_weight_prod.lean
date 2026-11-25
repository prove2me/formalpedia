-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.cloud_weight_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:11:30.737841+00:00
-- url     : https://prove2.me/submissions/ff72d6ad-de48-402c-8aeb-cc872a8529e9

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_CloudProd

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
theorem _root_.solution (c : ℝ) (n : ℕ) :
    ∏ j ∈ range (n + 1), (if j = 0 then 2 + c else 1 + 1 / (j : ℝ)) = (2 + c) * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ih, if_neg (Nat.succ_ne_zero n)]
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
