-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.bracket_const_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:58:35.33535+00:00
-- url     : https://prove2.me/submissions/89f0c94e-ed47-4d6f-9ad0-9d3db4922041

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_PairOKOfInterlace
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_Bracket
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_PstMul

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
theorem _root_.solution (k r : ℕ) (c b : ℝ) (hc : 0 ≤ c) (hb : 3 ≤ b) (hkb : (k : ℝ) ≤ b)
    (hcb : c + 2 ≤ b) :
    (2 + c) ^ 2 * (k : ℝ) ^ 2 * (3 * b) ^ (2 * r + 3) ≤ b ^ (4 * r + 10) := by
  have hb0 : 0 ≤ b := by linarith
  have h1 : (2 + c) ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h2 : (k : ℝ) ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg k) hkb 2
  have h3 : (3 * b) ^ (2 * r + 3) ≤ (b * b) ^ (2 * r + 3) :=
    pow_le_pow_left₀ (by linarith) (by nlinarith) _
  calc (2 + c) ^ 2 * (k : ℝ) ^ 2 * (3 * b) ^ (2 * r + 3)
      ≤ b ^ 2 * b ^ 2 * (b * b) ^ (2 * r + 3) := by
        apply mul_le_mul (mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)) h3
          (pow_nonneg (by linarith) _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = b ^ (4 * r + 10) := by ring
end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
