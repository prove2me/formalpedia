-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateAcyclic_of_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:45:17.089156+00:00
-- url     : https://prove2.me/submissions/1709b150-53a9-4853-bb38-669a9b10c553

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Theorems.Thm_GroundTheory_GroupCoh_toCoindRes_fromCoindRes
import Theorems.Thm_GroundTheory_GroupCoh_TateAcyclic_of_retract
import Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_coind_bot


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
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) : TateAcyclic M :=
  (tateAcyclic_coind_bot _).of_retract _ _ (toCoindRes_fromCoindRes M φ hφ)
end GroundTheory.GroupCoh
