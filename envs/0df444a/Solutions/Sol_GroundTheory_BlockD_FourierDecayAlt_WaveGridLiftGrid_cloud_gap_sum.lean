-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.cloud_gap_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:11:28.018903+00:00
-- url     : https://prove2.me/submissions/aeea9a90-c10d-4687-8550-2dfe4c581adb

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
theorem _root_.solution (k : ℕ) (lam : ℕ → ℝ) (g : ℝ)
    (hgap : ∀ s, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + g ≤ lam s) (s : ℕ) (hs : 1 ≤ s) :
    ∀ s', s ≤ s' → s' ≤ k - 1 → lam s' + ((s' : ℝ) - s) * g ≤ lam s := by
  intro s' hss'
  induction s', hss' using Nat.le_induction with
  | base => intro _; simp
  | succ n hn ih =>
    intro hn1
    have h1 := hgap n (by omega) hn1
    have h2 := ih (by omega)
    have h3 : (((n + 1 : ℕ) : ℝ) - s) * g = ((n : ℝ) - s) * g + g := by push_cast; ring
    rw [h3]
    linarith
end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
