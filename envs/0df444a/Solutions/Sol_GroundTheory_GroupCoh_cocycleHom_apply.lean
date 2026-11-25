-- Prove2me | solution 1 for GroundTheory.GroupCoh.cocycleHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:49:31.798868+00:00
-- url     : https://prove2.me/submissions/42601b3b-f5ab-4976-9f8f-544f88b5768f

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Definitions.Def_GroundTheory_TateCohomology_AugTrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory groupCohomology Rep
open GroundTheory GroundTheory.GroupCoh
universe u
variable (k G : Type u) [CommRing k] [Group G]
variable {k G}
variable {A : Rep.{u} k G}
namespace GroundTheory.GroupCoh
theorem _root_.solution (f : cocycles₁ A) (x : augIdeal k G) :
    (cocycleHom f).hom x = cocycleLinear f x.1 := rfl
end GroundTheory.GroupCoh
