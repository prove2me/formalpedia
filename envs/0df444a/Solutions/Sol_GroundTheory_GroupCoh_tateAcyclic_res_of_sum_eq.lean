-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateAcyclic_res_of_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:49:10.849747+00:00
-- url     : https://prove2.me/submissions/e0070739-4323-4f4b-89dc-14f5b05ee1c4

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_TateGroupIso
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
import Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_of_sum_eq
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
variable {k H K : Type u} [CommRing k] [Group H] [Group K] [Fintype H] [Fintype K]
  (f : H →* K) (hf : Function.Bijective f)
include hf
namespace GroundTheory.GroupCoh
theorem _root_.solution (B : Rep.{u} k K) (φ : B.V →ₗ[k] B.V)
    (hφ : ∀ m : B, ∑ g : K, B.ρ g (φ (B.ρ g⁻¹ m)) = m) : TateAcyclic (res f B) :=
  tateAcyclic_of_sum_eq (res f B) φ fun m => by
    conv_rhs => rw [← hφ m]
    exact Fintype.sum_bijective f hf _ _ fun h => by
      simp only [MonoidHom.comp_apply, map_inv]
end GroundTheory.GroupCoh
