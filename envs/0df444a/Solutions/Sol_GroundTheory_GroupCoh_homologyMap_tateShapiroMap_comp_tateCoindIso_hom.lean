-- Prove2me | solution 1 for GroundTheory.GroupCoh.homologyMap_tateShapiroMap_comp_tateCoindIso_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:51:50.877575+00:00
-- url     : https://prove2.me/submissions/0c2219f3-d250-415e-8649-c0670002fc34

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DiagonalSuccIsoFreeInvSingle
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateShapiro

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
open CategoryTheory Limits groupCohomology groupHomology Rep HomologicalComplex
universe u
variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) [Fintype G] [Fintype S]
namespace GroundTheory.GroupCoh
theorem _root_.solution (B : Rep.{u} k S) (n : ℤ) :
    HomologicalComplex.homologyMap (tateShapiroMap S B) n ≫ (tateCoindIso S B n).hom = 𝟙 _ :=
  (asIso (HomologicalComplex.homologyMap (tateShapiroMap S B) n)).hom_inv_id
end GroundTheory.GroupCoh
