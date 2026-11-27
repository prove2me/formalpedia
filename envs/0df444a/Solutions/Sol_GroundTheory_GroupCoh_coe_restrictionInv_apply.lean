-- Prove2me | solution 1 for GroundTheory.GroupCoh.coe_restrictionInv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:48:39.868015+00:00
-- url     : https://prove2.me/submissions/2b8d960a-7464-4608-99f6-6fd8b3eec0f8

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ConjAction

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
open CategoryTheory groupCohomology Rep
universe u
variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]
namespace GroundTheory.GroupCoh
theorem _root_.solution (x : groupCohomology A 1) :
    (restrictionInv A S x : groupCohomology (res S.subtype A) 1) =
      (map S.subtype (𝟙 (res S.subtype A)) 1).hom x := rfl
end GroundTheory.GroupCoh
