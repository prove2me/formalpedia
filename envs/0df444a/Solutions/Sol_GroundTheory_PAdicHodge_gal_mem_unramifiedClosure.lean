-- Prove2me | solution 1 for GroundTheory.PAdicHodge.gal_mem_unramifiedClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:48:30.923601+00:00
-- url     : https://prove2.me/submissions/2be34dca-425f-4bff-a115-e7169cdb1225

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnramifiedClosureCountableNeighbourhoods
import Definitions.Def_GroundTheory_PAdicHodge_UnramifiedClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Filter Topology
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {x : PadicAlgCl p}
    (hx : x ∈ unramifiedClosure p) : τ x ∈ unramifiedClosure p := by
  have h : (unramifiedClosure p).map (τ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p) ≤
      unramifiedClosure p := by
    rw [unramifiedClosure, IntermediateField.adjoin_map]
    apply IntermediateField.adjoin_le_iff.2
    rintro _ ⟨y, ⟨m, hm, hc, hy⟩, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨m, hm, hc, by rw [← map_pow, hy, map_one]⟩
  exact h ((IntermediateField.mem_map _).2 ⟨x, hx, rfl⟩)
end GroundTheory.PAdicHodge
