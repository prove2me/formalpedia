-- Prove2me | solution 1 for GroundTheory.GroupCoh.iso_resHomComplex_adj_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:09:42.053799+00:00
-- url     : https://prove2.me/submissions/e1468c1d-8b55-4c33-93f1-d05e6f98682d

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_ResCoresPos
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.indSES_obj_g
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)
set_option backward.isDefEq.respectTransparency false
namespace GroundTheory.GroupCoh
theorem _root_.solution (A : Rep.{u} k G) :
    (inhomogeneousCochainsIso A).hom ≫ resHomComplex S A ≫
      (linearYonedaObjResProjectiveResolutionIso (barResolution k G) (res S.subtype A)).hom ≫
        (inhomogeneousCochainsIso (coind S.subtype (res S.subtype A))).inv =
      cochainsMap (MonoidHom.id G) ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app A) := by
  ext n y : 3
  funext v
  refine Subtype.ext (funext fun g => ?_)
  change ((resCoindToHom S.subtype ((barResolution k G).complex.X n) (res S.subtype A)
      ((resFunctor S.subtype).map (freeLift k G A y))).hom
        (Finsupp.single v (MonoidAlgebra.single 1 1))).1 g =
    ((resCoindToHom S.subtype A (res S.subtype A) (𝟙 _)).hom (y v)).1 g
  rw [resCoindToHom_hom_apply_coe, resCoindToHom_hom_apply_coe]
  change (A.ρ.freeLift y) ((Representation.free k G (Fin n → G)) g
    (Finsupp.single v (MonoidAlgebra.single 1 1))) = _
  simp
end GroundTheory.GroupCoh
