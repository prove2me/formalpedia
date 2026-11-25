-- Prove2me | solution 1 for GroundTheory.GroupCoh.toCoindRes_fromCoindRes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:10:43.814619+00:00
-- url     : https://prove2.me/submissions/0dd799fb-2a18-4160-ab4c-3c3261cf0378

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm

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
open CategoryTheory Limits Rep MonoidalCategory
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
variable (M : Rep.{u} k G)
namespace GroundTheory.GroupCoh
theorem _root_.solution (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) :
    toCoindRes M ≫ fromCoindRes M φ = 𝟙 M := by
  ext m
  change (fromCoindRes M φ).hom.toLinearMap ((toCoindRes M).hom.toLinearMap m) = m
  refine (LinearMap.sum_apply _ _ _).trans ?_
  change ∑ x : G, M.ρ x⁻¹ (φ (M.ρ x m)) = m
  conv_rhs => rw [← hφ m]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun x => by simp
end GroundTheory.GroupCoh
