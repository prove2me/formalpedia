-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.progY_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:37:17.873045+00:00
-- url     : https://prove2.me/submissions/f2937885-eae0-453d-8c35-88e054399959

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_ProgYInjective

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
theorem _root_.solution (y0 : ℝ) : Function.Injective fun i : ℕ => y0 + 5 * (i : ℝ) := by
  intro i j h
  have : (i : ℝ) = j := by simpa using h
  exact_mod_cast this
end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
