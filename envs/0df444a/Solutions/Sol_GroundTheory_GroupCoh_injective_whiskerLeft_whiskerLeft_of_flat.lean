-- Prove2me | solution 1 for GroundTheory.GroupCoh.injective_whiskerLeft_whiskerLeft_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:22:12.256308+00:00
-- url     : https://prove2.me/submissions/ca4bf67f-2e5f-435b-aae7-26c64dddcc77

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Theorems.Thm_GroundTheory_GroupCoh_injective_of_lTensor_conj
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
variable {A B : Rep.{u} k G}
variable (V : Rep.{u} k G) [Module.Flat k V.V] {X₁ X₂ : Rep.{u} k G} (f : X₁ ⟶ X₂)
namespace GroundTheory.GroupCoh
theorem _root_.solution (Y : Rep.{u} k G)
    (hf : Function.Injective (Y ◁ f).hom) : Function.Injective (Y ◁ (V ◁ f)).hom := by
  refine injective_of_lTensor_conj (W := V.V) (Y ◁ (V ◁ f)).hom.toLinearMap (Y ◁ f).hom.toLinearMap
    hf (TensorProduct.leftComm k Y.V V.V X₁.V) (TensorProduct.leftComm k Y.V V.V X₂.V) fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul y t =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [TensorProduct.tmul_add, map_add, hs, ht]
    | tmul v a => rfl
end GroundTheory.GroupCoh
