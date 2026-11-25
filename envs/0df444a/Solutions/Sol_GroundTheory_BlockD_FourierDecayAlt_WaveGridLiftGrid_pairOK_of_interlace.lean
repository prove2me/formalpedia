-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.pairOK_of_interlace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:21:47.087704+00:00
-- url     : https://prove2.me/submissions/2c4d7401-1f82-4eae-a66d-14bfd9ae7c77

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
theorem _root_.solution (k : ℕ) (lam v : ℕ → ℝ) (e : ℕ) (x : ℝ)
    (h : ∀ s, 1 ≤ s → s ≤ k - 1 → lam s + 1 / 2 ≤ v s ∧ v (s + 1) ≤ lam s - 1 / 2) :
    PairOK k lam v e x := by
  intro s hs1 hsk _
  exact ⟨fun _ => (h s hs1 hsk).1, fun _ => (h s hs1 hsk).2⟩
end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
