-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.pairOK_moved
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:45:56.194857+00:00
-- url     : https://prove2.me/submissions/74ab64e0-113a-442a-a7f3-eb80c511fcd1

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
theorem _root_.solution (k l : ℕ) (lam u v : ℕ → ℝ) (x : ℝ)
    (h : ∀ s, 1 ≤ s → s ≤ k - 1 → lam s + 1 / 2 ≤ u s ∧ u (s + 1) ≤ lam s - 1 / 2)
    (hv : ∀ i, i ≠ l → i ≠ l + 1 → v i = u i)
    (hlow : ∀ s, 1 ≤ s → s < l → x < lam s) (hhigh : ∀ s, l < s → s ≤ k - 1 → lam s ≤ x) :
    PairOK k lam v l x := by
  intro s hs1 hsk hsl
  rcases lt_or_gt_of_ne hsl with hlt | hgt
  · have hx := hlow s hs1 hlt
    refine ⟨fun _ => ?_, fun hle => absurd hx (not_lt.mpr hle)⟩
    rw [hv s (by omega) (by omega)]
    exact (h s hs1 hsk).1
  · have hx := hhigh s hgt hsk
    refine ⟨fun hlt => absurd hx (not_le.mpr hlt), fun _ => ?_⟩
    rw [hv (s + 1) (by omega) (by omega)]
    exact (h s hs1 hsk).2
end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
