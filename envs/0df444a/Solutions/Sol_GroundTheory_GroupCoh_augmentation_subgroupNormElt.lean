-- Prove2me | solution 1 for GroundTheory.GroupCoh.augmentation_subgroupNormElt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:56:48.560832+00:00
-- url     : https://prove2.me/submissions/520253a4-a07e-4eb2-b1d2-041e9c6d95d3

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_SplittingModule
import Definitions.Def_GroundTheory_TateCohomology_CohTrivial
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_SplittingCohTrivial
import Theorems.Thm_GroundTheory_GroupCoh_augCocycle_apply
import Theorems.Thm_GroundTheory_GroupCoh_cupCochainsTensor_tmul
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
import Theorems.Thm_P2M_GroundTheory_GroupCoh_augSES_obj_X__c9c9f6b83d2f
import Theorems.Thm_P2M_GroundTheory_GroupCoh_augSES_obj_X__d7360f095d2c
import Theorems.Thm_P2M_GroundTheory_GroupCoh_augSES_obj_X__f61122e4f661
import Theorems.Thm_P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881
import Theorems.Thm_P2M_GroundTheory_GroupCoh_pullbackSESHom____2eb40945c3eb
import Theorems.Thm_P2M_GroundTheory_GroupCoh_pullbackSESHom____538251148457
import Theorems.Thm_P2M_GroundTheory_GroupCoh_pullbackSESHom____b79bf12ff0ad
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.augCocycle_apply
attribute [local simp] GroundTheory.GroupCoh.cupCochainsTensor_tmul
attribute [local simp] GroundTheory.GroupCoh.indSES_obj_g
attribute [local simp] P2M_GroundTheory_GroupCoh_augSES_obj_X__c9c9f6b83d2f
attribute [local simp] P2M_GroundTheory_GroupCoh_augSES_obj_X__d7360f095d2c
attribute [local simp] P2M_GroundTheory_GroupCoh_augSES_obj_X__f61122e4f661
attribute [local simp] P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881
attribute [local simp] P2M_GroundTheory_GroupCoh_pullbackSESHom____2eb40945c3eb
attribute [local simp] P2M_GroundTheory_GroupCoh_pullbackSESHom____538251148457
attribute [local simp] P2M_GroundTheory_GroupCoh_pullbackSESHom____b79bf12ff0ad



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory Limits groupCohomology Rep
open GroundTheory GroundTheory.GroupCoh
universe u
variable {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) (u : groupCohomology M 2)
variable (S : Subgroup G) [Fintype S]
omit [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution :
    augmentation ℤ G (subgroupNormElt S) = (Fintype.card S : ℤ) := by
  rw [subgroupNormElt, map_sum,
    Finset.sum_congr rfl (fun (x : S) _ => augmentation_single (k := ℤ) (x : G) (1 : ℤ))]
  simp
end GroundTheory.GroupCoh
