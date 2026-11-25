-- Prove2me | solution 1 for GroundTheory.GroupCoh.isZero_tateCohomology_zero_of_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:17:23.606282+00:00
-- url     : https://prove2.me/submissions/8f88ac00-0a06-4428-ba20-e4a92c8713ec

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Theorems.Thm_GroundTheory_GroupCoh_isZero_tateCohomology_zero_of_forall

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
    IsZero (tateCohomology M 0) := by
  refine isZero_tateCohomology_zero_of_forall M fun m hm => ⟨φ m, ?_⟩
  rw [Representation.norm, LinearMap.sum_apply]
  conv_rhs => rw [← hφ m]
  simp only [hm]
end GroundTheory.GroupCoh
