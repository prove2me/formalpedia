-- Prove2me | solution 1 for GroundTheory.GroupCoh.coe_invariantsTransport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:55:18.861745+00:00
-- url     : https://prove2.me/submissions/312f73bd-078e-42a5-9939-0f12354e2826

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
omit [Fintype H] [Fintype K]
namespace GroundTheory.GroupCoh
theorem _root_.solution {B : Rep.{u} k K} (x : B.ρ.invariants) :
    (invariantsTransport e x : B) = x := rfl
end GroundTheory.GroupCoh
