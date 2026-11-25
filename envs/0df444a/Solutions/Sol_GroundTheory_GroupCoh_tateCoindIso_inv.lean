-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateCoindIso_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:56:11.32295+00:00
-- url     : https://prove2.me/submissions/97e17dec-d986-4e34-886d-dc0fd9198e18

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CoresRes
import Definitions.Def_GroundTheory_TateCohomology_TateZeroClass
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero
import Theorems.Thm_GroundTheory_GroupCoh_homologyMap_tateShapiroMap_comp_tateCoindIso_hom


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
variable [Fintype G] [Fintype S]
namespace GroundTheory.GroupCoh
theorem _root_.solution (B : Rep.{u} k S) (n : ℤ) :
    (tateCoindIso S B n).inv = HomologicalComplex.homologyMap (tateShapiroMap S B) n := by
  refine (cancel_mono (tateCoindIso S B n).hom).1 ?_
  exact (Iso.inv_hom_id _).trans (homologyMap_tateShapiroMap_comp_tateCoindIso_hom S B n).symm
end GroundTheory.GroupCoh
