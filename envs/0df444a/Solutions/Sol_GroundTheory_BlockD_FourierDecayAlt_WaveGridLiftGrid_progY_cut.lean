-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.progY_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:48:06.26359+00:00
-- url     : https://prove2.me/submissions/40570e38-0673-48bb-b71e-8e7ca05b0108

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
theorem _root_.solution (lo hi : ℝ) (M : ℕ) (hlen : 5 * (M : ℝ) ≤ hi - lo) :
    ∀ y ∈ progY (2 - hi) M, (lo + 2 ≤ -y ∧ -y ≤ hi - 2) ∧ (lo + 2 ≤ -(y + 1) ∧ -(y + 1) ≤ hi - 2) := by
  intro y hy
  simp only [progY, mem_image, mem_range] at hy
  obtain ⟨i, hi', rfl⟩ := hy
  have hiM : (i : ℝ) + 1 ≤ M := by exact_mod_cast hi'
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
