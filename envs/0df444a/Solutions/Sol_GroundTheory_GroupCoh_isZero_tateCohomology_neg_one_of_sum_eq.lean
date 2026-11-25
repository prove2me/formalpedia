-- Prove2me | solution 1 for GroundTheory.GroupCoh.isZero_tateCohomology_neg_one_of_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:18:19.434495+00:00
-- url     : https://prove2.me/submissions/424a76cc-9339-4319-b68d-f8f18a554e4f

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Theorems.Thm_GroundTheory_GroupCoh_isZero_tateCohomology_neg_one_of_forall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits groupCohomology groupHomology Rep
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (M : Rep.{u} k G) (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) :
    IsZero (tateCohomology M (-1)) := by
  refine isZero_tateCohomology_neg_one_of_forall M fun m hm =>
    ⟨∑ g : G, Finsupp.single g⁻¹ (φ (M.ρ g⁻¹ m)), ?_⟩
  have hsum : ∑ g : G, M.ρ g⁻¹ m = M.ρ.norm m := by
    rw [Representation.norm, LinearMap.sum_apply]
    exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun _ => rfl)
  show (Finsupp.lsum k fun g : G => M.ρ g⁻¹ - LinearMap.id)
    (∑ g : G, Finsupp.single g⁻¹ (φ (M.ρ g⁻¹ m))) = m
  simp only [map_sum, Finsupp.lsum_single, LinearMap.sub_apply, LinearMap.id_apply, inv_inv]
  rw [Finset.sum_sub_distrib, ← map_sum, hsum, hm, map_zero, sub_zero, hφ]
end GroundTheory.GroupCoh
