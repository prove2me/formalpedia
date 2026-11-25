-- Prove2me | solution 1 for GroundTheory.GroupCoh.coindConst_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:55:39.792778+00:00
-- url     : https://prove2.me/submissions/a23d8d3c-3b09-4a85-89ba-5629cf1f3208

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
variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)
namespace GroundTheory.GroupCoh
theorem _root_.solution (B : Rep.{u} k S) (y : B.ρ.invariants) (g : G) :
    ((coindConst S B y : coind S.subtype B) : G → B) g = y := rfl
end GroundTheory.GroupCoh
