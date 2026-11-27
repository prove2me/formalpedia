-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateRes_comp_isoGroupCohomology
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:47:23.110596+00:00
-- url     : https://prove2.me/submissions/9cd2b251-d904-4d2a-b6cb-f01cb6cb0491

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_ResCoresPos
import Theorems.Thm_GroundTheory_GroupCoh_homologyMap_cochainsMap_unit
import Theorems.Thm_GroundTheory_GroupCoh_comp_cancel_of_isos
import Theorems.Thm_GroundTheory_GroupCoh_homologyMap_tateShapiroMap_comp_tateCoindIso_hom
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
import Theorems.Thm_GroundTheory_GroupCoh_tateRes_app
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
variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (S : Subgroup G) [Fintype S]
namespace GroundTheory.GroupCoh
theorem _root_.solution (n : ℕ) [NeZero n] (A : Rep.{u} k G) :
    (tateRes S n).app A ≫ (TateCohomology.isoGroupCohomology n).hom.app (res S.subtype A) =
      (TateCohomology.isoGroupCohomology n).hom.app A ≫
        groupCohomology.map S.subtype (𝟙 (res S.subtype A)) n := by
  have h1 : HomologicalComplex.homologyMap
      (tateComplex.map ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app A)) n =
      ((tateComplexConnectData A).homologyIsoPos n n rfl).hom ≫
        HomologicalComplex.homologyMap (cochainsMap (MonoidHom.id G)
          ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app A)) n ≫
        ((tateComplexConnectData (coind S.subtype (res S.subtype A) : Rep.{u} k G)).homologyIsoPos
          n n rfl).inv :=
    CochainComplex.ConnectData.homologyMap_map_of_eq_succ _ _ _ _ _ n n rfl
  have h2 : HomologicalComplex.homologyMap (tateShapiroMap S (res S.subtype A)) n = _ :=
    CochainComplex.ConnectData.homologyMap_map_of_eq_succ
    (tateComplexConnectData (res S.subtype A))
    (tateComplexConnectData (coind S.subtype (res S.subtype A) : Rep.{u} k G))
    (groupHomology.chainsMap S.subtype (toResCoind S (res S.subtype A)))
    (shapiroCochainsHomotopyEquiv S (res S.subtype A)).hom (shapiro_comm_zero S (res S.subtype A))
    n n rfl
  have hb := homologyMap_tateShapiroMap_comp_tateCoindIso_hom S (res S.subtype A) n
  have h2' : HomologicalComplex.homologyMap (shapiroCochainsHomotopyEquiv S (res S.subtype A)).hom n =
      ((tateComplexConnectData (res S.subtype A)).homologyIsoPos n n rfl).inv ≫
        HomologicalComplex.homologyMap (tateShapiroMap S (res S.subtype A)) n ≫
          ((tateComplexConnectData (coind S.subtype (res S.subtype A) : Rep.{u} k G)).homologyIsoPos n n rfl).hom := by
    rw [h2]; simp
  rw [tateRes_app, Category.assoc]
  show HomologicalComplex.homologyMap
      (tateComplex.map ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app A)) n ≫
        (tateCoindIso S (res S.subtype A) n).hom ≫
          ((tateComplexConnectData (res S.subtype A)).homologyIsoPos n n rfl).hom =
      ((tateComplexConnectData A).homologyIsoPos n n rfl).hom ≫
        groupCohomology.map S.subtype (𝟙 (res S.subtype A)) n
  exact comp_cancel_of_isos _ _ _ _ _ _ _ _ _ h1 (homologyMap_cochainsMap_unit S A n) h2' hb
end GroundTheory.GroupCoh
