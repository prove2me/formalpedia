-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.cloud_pair_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:11:09.321267+00:00
-- url     : https://prove2.me/submissions/18ce3d1c-78ee-4477-8c35-113d76f29f71

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_PairOKOfInterlace
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_CloudPair

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
theorem _root_.solution (a d c D : ℝ) (hc : 0 ≤ c) (ha : a ≤ d + 1 + c) (hD1 : d ≤ D)
    (hD2 : 1 ≤ D) : a ≤ (1 + (1 + c) / max d 1) * D := by
  have hm : 0 < max d 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hmD : max d 1 ≤ D := max_le hD1 hD2
  have h1 : 1 + c ≤ (1 + c) / max d 1 * D := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hm]
    exact mul_le_mul_of_nonneg_left hmD (by linarith)
  have h2 : (1 + (1 + c) / max d 1) * D = D + (1 + c) / max d 1 * D := by ring
  rw [h2]
  linarith
end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
