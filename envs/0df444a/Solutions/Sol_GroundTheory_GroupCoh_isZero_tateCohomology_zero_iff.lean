-- Prove2me | solution 1 for GroundTheory.GroupCoh.isZero_tateCohomology_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:10:48.301089+00:00
-- url     : https://prove2.me/submissions/8133dd68-7457-445c-85ae-d1e445a145aa

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ModuleHomologyData
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Theorems.Thm_GroundTheory_GroupCoh_range_norm_le_invariants

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
    IsZero (tateCohomology M 0) ↔ LinearMap.range M.ρ.norm = M.ρ.invariants := by
  rw [((tateCohomologyZeroIso R G).app M).isZero_iff, ModuleCat.isZero_iff_subsingleton]
  change Subsingleton (M.ρ.invariants ⧸ normRangeInvariants M) ↔ _
  rw [Submodule.Quotient.subsingleton_iff]
  constructor
  · intro h
    refine le_antisymm (range_norm_le_invariants M) (fun x hx => ?_)
    have : (⟨x, hx⟩ : M.ρ.invariants) ∈ normRangeInvariants M := h ▸ Submodule.mem_top
    exact this
  · intro h
    refine eq_top_iff.2 (fun x _ => ?_)
    show x.1 ∈ LinearMap.range M.ρ.norm
    rw [h]
    exact x.2
end GroundTheory.GroupCoh
