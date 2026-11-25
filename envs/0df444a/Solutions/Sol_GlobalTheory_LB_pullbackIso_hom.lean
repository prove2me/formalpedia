-- Prove2me | solution 1 for GlobalTheory.LB.pullbackIso_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:59:17.727796+00:00
-- url     : https://prove2.me/submissions/a6d34f9d-3d34-4734-b00c-d80ce4786aa1

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
theorem _root_.solution (hL : L.IsLB) (f : Y ⟶ X) :
    (pullbackIso hL f).hom = pullbackHom L f := rfl
end GlobalTheory.LB
