-- Prove2me | solution 1 for GroundTheory.GroupCoh.cocycleHom_augIdealSubOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:25:13.09346+00:00
-- url     : https://prove2.me/submissions/f940bb16-cbb7-4692-aa38-4315fb4c0631

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Definitions.Def_GroundTheory_TateCohomology_AugTrivial
import Theorems.Thm_GroundTheory_GroupCoh_cocycleHom_apply

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
theorem _root_.solution (f : cocycles₁ A) (g : G) :
    (cocycleHom f).hom (augIdealSubOne g) = f g := by
  rw [cocycleHom_apply, augIdealSubOne_val, map_sub, cocycleLinear_single, cocycleLinear_single,
    cocycles₁_map_one, smul_zero, sub_zero, one_smul]
end GroundTheory.GroupCoh
