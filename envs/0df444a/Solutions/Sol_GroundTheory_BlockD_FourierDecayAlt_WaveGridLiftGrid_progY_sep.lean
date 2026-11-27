-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.progY_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:47:10.502376+00:00
-- url     : https://prove2.me/submissions/ba1d8b4a-37e4-46e1-bbc0-ba03373ab58e

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
theorem _root_.solution (y0 : ℝ) (M : ℕ) : ∀ y ∈ progY y0 M, ∀ y' ∈ progY y0 M, y ≠ y' → 5 ≤ |y - y'| := by
  intro y hy y' hy' hne
  simp only [progY, mem_image, mem_range] at hy hy'
  obtain ⟨i, -, rfl⟩ := hy
  obtain ⟨j, -, rfl⟩ := hy'
  have hij : i ≠ j := by
    rintro rfl
    exact hne rfl
  have hsub : y0 + 5 * (i : ℝ) - (y0 + 5 * (j : ℝ)) = 5 * ((i : ℤ) - (j : ℤ) : ℤ) := by
    push_cast; ring
  rw [hsub, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 5)]
  have h1 : (1 : ℝ) ≤ |(((i : ℤ) - (j : ℤ) : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    have : (1 : ℤ) ≤ |(i : ℤ) - (j : ℤ)| := by
      exact Int.one_le_abs (sub_ne_zero.mpr (by exact_mod_cast hij))
    exact_mod_cast this
  linarith
end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
