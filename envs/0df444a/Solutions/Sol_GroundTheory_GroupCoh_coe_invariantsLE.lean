-- Prove2me | solution 1 for GroundTheory.GroupCoh.coe_invariantsLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:16:39.313971+00:00
-- url     : https://prove2.me/submissions/a25dbf11-b17a-442d-a4ea-5bf4d23d8640

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateUnique
import Definitions.Def_GroundTheory_TateCohomology_TateTransport
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero
import Definitions.Def_GroundTheory_TateCohomology_TateSubgroupMaps

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
open CategoryTheory Limits Rep
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable {U W : Subgroup G} (h : W ≤ U)
variable [Fintype U] [Fintype W]
omit [Fintype U] [Fintype W]
namespace GroundTheory.GroupCoh
theorem _root_.solution {A : Rep.{u} k G} (y : (res U.subtype A).ρ.invariants) :
    (invariantsLE h y : A) = y := rfl
end GroundTheory.GroupCoh
