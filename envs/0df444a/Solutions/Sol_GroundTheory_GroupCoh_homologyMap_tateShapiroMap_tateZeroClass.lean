-- Prove2me | solution 1 for GroundTheory.GroupCoh.homologyMap_tateShapiroMap_tateZeroClass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:57:24.249314+00:00
-- url     : https://prove2.me/submissions/1f867b80-5823-4e93-b9bd-05bcad94baa4

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CoresRes
import Definitions.Def_GroundTheory_TateCohomology_TateZeroClass
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero
import Theorems.Thm_GroundTheory_GroupCoh_coe_transferInv
import Theorems.Thm_GroundTheory_GroupCoh_coindConst_apply
import Theorems.Thm_GroundTheory_GroupCoh_homologyMap_tateZeroClass
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


attribute [local simp] GroundTheory.GroupCoh.coe_transferInv
attribute [local simp] GroundTheory.GroupCoh.coindConst_apply

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)
variable [Fintype G] [Fintype S]
namespace GroundTheory.GroupCoh
theorem _root_.solution (B : Rep.{u} k S) (y : B.ρ.invariants) :
    (HomologicalComplex.homologyMap (tateShapiroMap S B) 0).hom (tateZeroClass B y) =
      tateZeroClass (coind S.subtype B) (coindConst S B y) :=
  homologyMap_tateZeroClass _ y _ (funext fun v => Subtype.ext (funext fun g =>
    shapiroCochains_hom_f_zero_const S B y y.2 v g))
end GroundTheory.GroupCoh
