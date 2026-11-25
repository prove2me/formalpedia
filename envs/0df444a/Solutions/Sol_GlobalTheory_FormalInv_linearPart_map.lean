-- Prove2me | solution 1 for GlobalTheory.FormalInv.linearPart_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:45:44.695704+00:00
-- url     : https://prove2.me/submissions/00e1ffd9-1906-455e-9114-5bb2b629de96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries Finsupp
noncomputable section
open GlobalTheory GlobalTheory.FormalInv
variable {σ τ υ ι : Type*} {R : Type*} [CommRing R]
namespace GlobalTheory.FormalInv
theorem _root_.solution {S : Type*} [CommRing S] (φ : R →+* S) (u : ι → MvPowerSeries σ R) :
    linearPart (fun i => MvPowerSeries.map φ (u i)) = (linearPart u).map φ := by
  ext i j; simp
end GlobalTheory.FormalInv
