-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.lag_abs_sum_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:44:47.556697+00:00
-- url     : https://prove2.me/submissions/616dde5f-f044-41ee-a8c6-5851e65f9573

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_LagSum
import Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_lag_abs_term_le

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
theorem _root_.solution {d : ℕ} (y : Fin (d + 1) → ℝ) (h : ∀ i j, i ≠ j → 5 ≤ |y i - y j|) :
    ∑ j, |∏ i ∈ (univ : Finset (Fin (d + 1))).erase j, (y j - y i)⁻¹| ≤ 1 := by
  have hn : (d : ℝ) + 1 ≤ 5 ^ d := by
    have : d + 1 ≤ 5 ^ d := Nat.lt_pow_self (by norm_num)
    exact_mod_cast this
  calc ∑ j, |∏ i ∈ (univ : Finset (Fin (d + 1))).erase j, (y j - y i)⁻¹|
      ≤ ∑ _j : Fin (d + 1), (1 / 5 : ℝ) ^ d :=
        Finset.sum_le_sum (fun j _ => lag_abs_term_le y h j)
    _ = ((d : ℝ) + 1) / 5 ^ d := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_pow, one_pow]
        push_cast; ring
    _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact hn
end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
