-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.cloud_factor_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:11:26.478135+00:00
-- url     : https://prove2.me/submissions/b752b5ad-6d54-4e4e-b22b-cb740c5d4a26

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
theorem _root_.solution (c g d : ℝ) (j : ℕ) (hc : 0 ≤ c) (hg : 1 + c ≤ g) (hd : (j : ℝ) * g ≤ d) :
    1 + (1 + c) / max d 1 ≤ (if j = 0 then 2 + c else 1 + 1 / (j : ℝ)) := by
  split_ifs with hj
  · have : (1 + c) / max d 1 ≤ 1 + c := div_le_self (by linarith) (le_max_right _ _)
    linarith
  · have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
    have hpos : 0 < (j : ℝ) * (1 + c) := by positivity
    have h1 : (j : ℝ) * (1 + c) ≤ (j : ℝ) * g := mul_le_mul_of_nonneg_left hg (by positivity)
    have h2 : (j : ℝ) * (1 + c) ≤ max d 1 := le_trans (h1.trans hd) (le_max_left _ _)
    have h3 : (1 + c) / max d 1 ≤ (1 + c) / ((j : ℝ) * (1 + c)) :=
      div_le_div_of_nonneg_left (by linarith) hpos h2
    have h4 : (1 + c) / ((j : ℝ) * (1 + c)) = 1 / j := by
      have : (1 + c) ≠ 0 := by linarith
      have : (j : ℝ) ≠ 0 := by linarith
      field_simp
    linarith
end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
