-- Prove2me | solution 1 for GroundTheory.GroupCoh.augSES_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:46.231161+00:00
-- url     : https://prove2.me/submissions/6df2d9da-e588-4d78-a7f8-40b84630171f

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Theorems.Thm_P2M_GroundTheory_GroupCoh___augIdealRetract_82d7b9ae2009
import Theorems.Thm_GroundTheory_GroupCoh_whiskerRight_hom_tmul
import Theorems.Thm_P2M_GroundTheory_GroupCoh_augSES_obj_X__c9c9f6b83d2f
import Theorems.Thm_P2M_GroundTheory_GroupCoh_augSES_obj_X__d7360f095d2c
import Theorems.Thm_P2M_GroundTheory_GroupCoh_augSES_obj_X__f61122e4f661
import Theorems.Thm_GroundTheory_GroupCoh_cupCochainsTensor_tmul
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
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
attribute [local simp] P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881


attribute [local simp] GroundTheory.GroupCoh.augSES_obj_X₁
attribute [local simp] GroundTheory.GroupCoh.augSES_obj_X₂
attribute [local simp] GroundTheory.GroupCoh.augSES_obj_X₃

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (k G)
variable {k G}
variable (k G)
variable {k G}
namespace GroundTheory.GroupCoh
theorem _root_.solution (X : Rep.{u} k G) (t : (Rep.leftRegular k G ⊗ X : Rep k G)) :
    (augIdealι k G ▷ X).hom (LinearMap.rTensor X.V (augIdealRetract k G) t) +
      (MonoidAlgebra.single 1 1 ⊗ₜ[k] (augX X).hom t : (Rep.leftRegular k G ⊗ X : Rep k G)) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
    rw [LinearMap.rTensor_tmul, whiskerRight_hom_tmul, ι_augIdealRetract, augX_tmul,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', MonoidAlgebra.smul_single, smul_eq_mul,
      mul_one, ← TensorProduct.add_tmul, sub_add_cancel]
  | add s t hs ht =>
    rw [map_add, map_add, map_add, TensorProduct.tmul_add]
    conv_rhs => rw [← hs, ← ht]
    abel
end GroundTheory.GroupCoh
