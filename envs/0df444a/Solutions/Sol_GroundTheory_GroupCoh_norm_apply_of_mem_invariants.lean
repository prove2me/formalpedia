-- Prove2me | solution 1 for GroundTheory.GroupCoh.norm_apply_of_mem_invariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:49:23.756108+00:00
-- url     : https://prove2.me/submissions/83c64da3-5507-47dc-b65f-2e3ac774e29a

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_Annihilation
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
open CategoryTheory Limits Rep
universe u
variable {R G : Type u} [CommRing R] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (A : Rep.{u} R G) {a : A} (ha : a ∈ A.ρ.invariants) :
    A.ρ.norm a = Fintype.card G • a := by
  rw [Representation.mem_invariants] at ha
  simp [Representation.norm, LinearMap.sum_apply, ha]
end GroundTheory.GroupCoh
