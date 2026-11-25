-- Prove2me | solution 1 for GroundTheory.GroupCoh.coe_transferInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:55:37.820932+00:00
-- url     : https://prove2.me/submissions/ab7c83a9-15f6-498b-9e3e-aa8706a59896

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CoresRes
import Definitions.Def_GroundTheory_TateCohomology_TateZeroClass
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero

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
open CategoryTheory Limits Rep groupCohomology
universe u
variable {k G H : Type u} [CommRing k] [Group G] [Group H]
variable (S : Subgroup G) {A : Rep.{u} k G}
variable [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (y : (res S.subtype A).ρ.invariants) :
    (transferInv S y : A) = transferSum S y := rfl
end GroundTheory.GroupCoh
