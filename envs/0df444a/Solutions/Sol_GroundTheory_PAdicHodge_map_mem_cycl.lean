-- Prove2me | solution 1 for GroundTheory.PAdicHodge.map_mem_cycl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:30.894837+00:00
-- url     : https://prove2.me/submissions/fed06e42-006f-4022-bc0a-dce09c91d0db

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Theorems.Thm_GroundTheory_PAdicHodge_cycl_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial
noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {p}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {n : ℕ} {x : PadicAlgCl p}
    (hx : x ∈ cycl p n) : σ x ∈ cycl p n := by
  rw [← cycl_map σ n]
  exact ⟨x, hx, rfl⟩
end GroundTheory.PAdicHodge
