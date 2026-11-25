-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateTransport_tateZeroClass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:14:14.008073+00:00
-- url     : https://prove2.me/submissions/8c825ae9-5ada-4855-a25c-6b0aaf6b619d

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateGroupIso
import Definitions.Def_GroundTheory_TateCohomology_TateZeroClass
import Definitions.Def_GroundTheory_TateCohomology_TateTransport
import Theorems.Thm_GroundTheory_GroupCoh_homologyMap_tateZeroClass


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep groupCohomology groupHomology
universe u
variable {k H K : Type u} [CommRing k] [Group H] [Group K]
variable [Fintype H] [Fintype K] (e : H ≃* K)
namespace GroundTheory.GroupCoh
theorem _root_.solution (B : Rep.{u} k K) (x : B.ρ.invariants) :
    ((tateTransport e 0).app B).hom (tateZeroClass B x) =
      tateZeroClass (res (e : H →* K) B) (invariantsTransport e x) :=
  homologyMap_tateZeroClass _ x _ (funext fun _ => rfl)
end GroundTheory.GroupCoh
