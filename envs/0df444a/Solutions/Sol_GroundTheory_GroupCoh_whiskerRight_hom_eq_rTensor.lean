-- Prove2me | solution 1 for GroundTheory.GroupCoh.whiskerRight_hom_eq_rTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:48:24.236427+00:00
-- url     : https://prove2.me/submissions/2670eea3-7fbd-47ce-a822-611e753191b1

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
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
namespace GroundTheory.GroupCoh
theorem _root_.solution (f : A ⟶ B) (Y : Rep.{u} k G) (t : (A ⊗ Y : Rep k G)) :
    (f ▷ Y).hom t = LinearMap.rTensor Y.V f.hom.toLinearMap t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rfl
  | add s t hs ht => rw [map_add, map_add, hs, ht]
end GroundTheory.GroupCoh
