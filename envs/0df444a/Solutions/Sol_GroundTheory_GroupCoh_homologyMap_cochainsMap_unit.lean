-- Prove2me | solution 1 for GroundTheory.GroupCoh.homologyMap_cochainsMap_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:04:11.258697+00:00
-- url     : https://prove2.me/submissions/a36199d2-11d7-4270-9812-5e5a09cfa2eb

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_ResCoresPos
import Theorems.Thm_GroundTheory_GroupCoh_cochainsMap_subtype_comp_iso
import Theorems.Thm_GroundTheory_GroupCoh_iso_resHomComplex_adj_iso
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
namespace GroundTheory.GroupCoh
theorem _root_.solution (A : Rep.{u} k G) (n : ℕ) :
    HomologicalComplex.homologyMap (cochainsMap (MonoidHom.id G)
        ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app A)) n =
      groupCohomology.map S.subtype (𝟙 (res S.subtype A)) n ≫
        HomologicalComplex.homologyMap (shapiroCochainsHomotopyEquiv S (res S.subtype A)).hom n := by
  have H := ((linearYonedaObjHomotopy (R := k) (barInclHomotopy (k := k) S)
    (res S.subtype A)).compRight
      ((linearYonedaObjResProjectiveResolutionIso (barResolution k G) (res S.subtype A)).hom ≫
        (inhomogeneousCochainsIso (coind S.subtype (res S.subtype A))).inv)).compLeft
    ((inhomogeneousCochainsIso A).hom ≫ resHomComplex S A)
  have e1 : ((inhomogeneousCochainsIso A).hom ≫ resHomComplex S A) ≫
      linearYonedaObjMap ((barHomotopyEquiv (k := k) S).inv ≫ barIncl S) (res S.subtype A) ≫
        (linearYonedaObjResProjectiveResolutionIso (barResolution k G) (res S.subtype A)).hom ≫
          (inhomogeneousCochainsIso (coind S.subtype (res S.subtype A))).inv =
      cochainsMap S.subtype (𝟙 (res S.subtype A)) ≫
        (shapiroCochainsHomotopyEquiv S (res S.subtype A)).hom := by
    calc _ = ((inhomogeneousCochainsIso A).hom ≫ resHomComplex S A ≫
            linearYonedaObjMap (barIncl (k := k) S) (res S.subtype A)) ≫
          linearYonedaObjMap (barHomotopyEquiv (k := k) S).inv (res S.subtype A) ≫
            (linearYonedaObjResProjectiveResolutionIso (barResolution k G) (res S.subtype A)).hom ≫
              (inhomogeneousCochainsIso (coind S.subtype (res S.subtype A))).inv := by
          rw [linearYonedaObjMap_comp]; simp only [Category.assoc]
      _ = (cochainsMap S.subtype (𝟙 (res S.subtype A)) ≫
            (inhomogeneousCochainsIso (res S.subtype A)).hom) ≫
          linearYonedaObjMap (barHomotopyEquiv (k := k) S).inv (res S.subtype A) ≫
            (linearYonedaObjResProjectiveResolutionIso (barResolution k G) (res S.subtype A)).hom ≫
              (inhomogeneousCochainsIso (coind S.subtype (res S.subtype A))).inv :=
          congrArg (· ≫ _) (cochainsMap_subtype_comp_iso S A).symm
      _ = _ := by simp only [Category.assoc]; rfl
  have e2 : ((inhomogeneousCochainsIso A).hom ≫ resHomComplex S A) ≫
      linearYonedaObjMap (𝟙 _) (res S.subtype A) ≫
        (linearYonedaObjResProjectiveResolutionIso (barResolution k G) (res S.subtype A)).hom ≫
          (inhomogeneousCochainsIso (coind S.subtype (res S.subtype A))).inv =
      cochainsMap (MonoidHom.id G) ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app A) := by
    rw [linearYonedaObjMap_id, Category.id_comp, Category.assoc]
    exact iso_resHomComplex_adj_iso S A
  rw [← e2, ← H.homologyMap_eq, e1, HomologicalComplex.homologyMap_comp]
  rfl
end GroundTheory.GroupCoh
