-- Prove2me | solution 1 for GroundTheory.GroupCoh.cohTrivial_leftRegular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:03:39.515368+00:00
-- url     : https://prove2.me/submissions/ac98176f-152e-4873-bcf0-83e5cf940afd

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Definitions.Def_GroundTheory_TateCohomology_AugTrivial
import Theorems.Thm_GroundTheory_GroupCoh_coeffOneProj_apply
import Theorems.Thm_GroundTheory_GroupCoh_cohTrivial_of_sum_eq
import Theorems.Thm_GroundTheory_GroupCoh_cupCochainsTensor_tmul
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
import Theorems.Thm_P2M_GroundTheory_GroupCoh_augSES_obj_X__c9c9f6b83d2f
import Theorems.Thm_P2M_GroundTheory_GroupCoh_augSES_obj_X__d7360f095d2c
import Theorems.Thm_P2M_GroundTheory_GroupCoh_augSES_obj_X__f61122e4f661
import Theorems.Thm_P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
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
attribute [local simp] GroundTheory.GroupCoh.cupCochainsTensor_tmul
attribute [local simp] GroundTheory.GroupCoh.indSES_obj_g
attribute [local simp] P2M_GroundTheory_GroupCoh_augSES_obj_X__c9c9f6b83d2f
attribute [local simp] P2M_GroundTheory_GroupCoh_augSES_obj_X__d7360f095d2c
attribute [local simp] P2M_GroundTheory_GroupCoh_augSES_obj_X__f61122e4f661
attribute [local simp] P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory groupCohomology Rep
open GroundTheory GroundTheory.GroupCoh
universe u
variable (k G : Type u) [CommRing k] [Group G]
namespace GroundTheory.GroupCoh
theorem _root_.solution [Fintype G] : CohTrivial (Rep.leftRegular k G) := by
  refine cohTrivial_of_sum_eq _ coeffOneProj fun m => ?_
  induction m using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finset.sum_add_distrib, hx, hy]
  | single h c =>
    rw [Fintype.sum_eq_single h]
    · simp [coeffOneProj_apply]
    · intro g hg
      have : g⁻¹ * h ≠ 1 := fun e => hg (inv_mul_eq_one.mp e)
      simp [coeffOneProj_apply, this]
end GroundTheory.GroupCoh
