-- Prove2me | solution 1 for GroundTheory.GroupCoh.exists_sum_eq_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:25:14.566067+00:00
-- url     : https://prove2.me/submissions/ed7c0352-a708-4a5a-9fbc-1edc17bf9940

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Definitions.Def_GroundTheory_TateCohomology_UniquelyDivisible
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Theorems.Thm_GroundTheory_GroupCoh_sum_eq_sum_quotient_sum
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
open scoped MonoidAlgebra
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable {V : Type*} [AddCommGroup V] [Module k V]
namespace GroundTheory.GroupCoh
theorem _root_.solution [Fintype G] (ρ : Representation k G V) (φ : V →ₗ[k] V)
    (hφ : ∀ v, ∑ g : G, ρ g (φ (ρ g⁻¹ v)) = v) (S : Subgroup G) [Fintype S] :
    ∃ ψ : V →ₗ[k] V, ∀ v, ∑ s : S, ρ s (ψ (ρ (s⁻¹ : S) v)) = v := by
  classical
  refine ⟨∑ c : G ⧸ S, ρ c.out⁻¹ ∘ₗ φ ∘ₗ ρ c.out, fun v => ?_⟩
  conv_rhs => rw [← hφ v]
  rw [← Fintype.sum_equiv (Equiv.inv G) (fun h => ρ h⁻¹ (φ (ρ h v))) _ (fun h => by simp),
    sum_eq_sum_quotient_sum S, Finset.sum_comm]
  refine Fintype.sum_equiv (Equiv.inv S) _ _ fun s => ?_
  simp [map_sum, LinearMap.sum_apply, map_mul, mul_inv_rev, Module.End.mul_apply]
end GroundTheory.GroupCoh
