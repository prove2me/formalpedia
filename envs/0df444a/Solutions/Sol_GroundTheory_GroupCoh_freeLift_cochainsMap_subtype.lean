-- Prove2me | solution 1 for GroundTheory.GroupCoh.freeLift_cochainsMap_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:09:27.888995+00:00
-- url     : https://prove2.me/submissions/2bc918b1-4243-45a0-a5d2-bf40e88019fb

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
theorem _root_.solution (A : Rep.{u} k G) (n : ℕ) (y : (Fin n → G) → A) :
    freeLift k S (res S.subtype A) (((cochainsMap S.subtype (𝟙 (res S.subtype A))).f n).hom y) =
      barInclF S n ≫ (resFunctor S.subtype).map (freeLift k G A y) := by
  refine free_ext _ _ _ _ _ fun w => ?_
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  rw [barInclF_single]
  simp [cochainsMap_f_hom]
  exact (show (freeLift k G A y).hom (Finsupp.single (Subtype.val ∘ w) (MonoidAlgebra.single 1 1)) =
    y (Subtype.val ∘ w) by simp).symm
end GroundTheory.GroupCoh
