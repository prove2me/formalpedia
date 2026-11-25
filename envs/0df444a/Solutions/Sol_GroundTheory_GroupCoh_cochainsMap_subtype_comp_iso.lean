-- Prove2me | solution 1 for GroundTheory.GroupCoh.cochainsMap_subtype_comp_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:06.967702+00:00
-- url     : https://prove2.me/submissions/8f7fa571-8686-4389-a123-a30b5b33b163

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_ResCoresPos
import Theorems.Thm_GroundTheory_GroupCoh_freeLift_cochainsMap_subtype

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
set_option backward.isDefEq.respectTransparency false
namespace GroundTheory.GroupCoh
theorem _root_.solution (A : Rep.{u} k G) :
    cochainsMap S.subtype (𝟙 (res S.subtype A)) ≫ (inhomogeneousCochainsIso (res S.subtype A)).hom =
      (inhomogeneousCochainsIso A).hom ≫ resHomComplex S A ≫
        linearYonedaObjMap (barIncl (k := k) S) (res S.subtype A) := by
  ext n y : 3
  exact freeLift_cochainsMap_subtype S A n y
end GroundTheory.GroupCoh
