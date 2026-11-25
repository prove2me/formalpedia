-- Prove2me | solution 1 for GlobalTheory.LB.unit_comp_pullbackHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:56:19.80865+00:00
-- url     : https://prove2.me/submissions/e77b0fae-6857-49cf-9400-3de083bc7f17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_BijectiveToPushforwardComp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.LB
variable {X Y : Scheme.{0}}
variable {L : LB X}
namespace GlobalTheory.LB
theorem _root_.solution (L : LB X) (f : Y ⟶ X) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (toMod L) ≫
      (Scheme.Modules.pushforward f).map (pullbackHom L f) = toPushforward L f :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply _ _)
end GlobalTheory.LB
