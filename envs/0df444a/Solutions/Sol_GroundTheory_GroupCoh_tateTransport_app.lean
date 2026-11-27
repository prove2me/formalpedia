-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateTransport_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:46:46.847054+00:00
-- url     : https://prove2.me/submissions/ffd123a2-5ca9-46f8-9035-daa1ee015045

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateGroupIso
import Definitions.Def_GroundTheory_TateCohomology_TateZeroClass
import Definitions.Def_GroundTheory_TateCohomology_TateTransport

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
theorem _root_.solution (n : ℤ) (B : Rep.{u} k K) :
    (tateTransport e n).app B = HomologicalComplex.homologyMap (tateTransportComplex e B) n := rfl
end GroundTheory.GroupCoh
