-- Prove2me | solution 1 for GroundTheory.GroupCoh.isZero_tateCohomology_zero_iff_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:18:07.913303+00:00
-- url     : https://prove2.me/submissions/fcc0575d-ffd0-46a2-8550-c2f27907d5e3

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ModuleHomologyData
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Theorems.Thm_GroundTheory_GroupCoh_range_norm_le_invariants
import Theorems.Thm_GroundTheory_GroupCoh_isZero_tateCohomology_zero_iff

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
open CategoryTheory Limits Representation groupCohomology groupHomology
universe u
variable {R G : Type u} [CommRing R] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (M : Rep.{u} R G) :
    IsZero (tateCohomology M 0) ↔ ∀ x ∈ M.ρ.invariants, ∃ m, M.ρ.norm m = x := by
  rw [isZero_tateCohomology_zero_iff]
  constructor
  · intro h x hx
    rw [← h] at hx
    exact hx
  · intro h
    exact le_antisymm (range_norm_le_invariants M) (fun x hx => h x hx)
end GroundTheory.GroupCoh
