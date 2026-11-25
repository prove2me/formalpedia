-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.lag_abs_term_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:11:35.187728+00:00
-- url     : https://prove2.me/submissions/6c24e01d-f2ce-4cae-b863-3bbacb2c52c3

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_LagSum

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
theorem _root_.solution {d : ℕ} (y : Fin (d + 1) → ℝ) (h : ∀ i j, i ≠ j → 5 ≤ |y i - y j|)
    (j : Fin (d + 1)) :
    |∏ i ∈ (univ : Finset (Fin (d + 1))).erase j, (y j - y i)⁻¹| ≤ (1 / 5 : ℝ) ^ d := by
  rw [abs_prod]
  have hcard : ((univ : Finset (Fin (d + 1))).erase j).card = d := by
    rw [Finset.card_erase_of_mem (mem_univ j)]; simp
  calc ∏ i ∈ (univ : Finset (Fin (d + 1))).erase j, |(y j - y i)⁻¹|
      ≤ ∏ _i ∈ (univ : Finset (Fin (d + 1))).erase j, (1 / 5 : ℝ) := by
        apply Finset.prod_le_prod
        · intro i _; exact abs_nonneg _
        · intro i hi
          have hij : j ≠ i := (Finset.ne_of_mem_erase hi).symm
          rw [abs_inv, one_div]
          exact inv_anti₀ (by norm_num) (h j i hij)
    _ = (1 / 5 : ℝ) ^ d := by rw [Finset.prod_const, hcard]
end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
