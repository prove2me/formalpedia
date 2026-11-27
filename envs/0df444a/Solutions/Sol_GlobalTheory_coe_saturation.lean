-- Prove2me | solution 1 for GlobalTheory.coe_saturation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:36:36.288813+00:00
-- url     : https://prove2.me/submissions/6d147cc7-caab-4cdd-baa0-d63afa2d3d93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']
namespace GlobalTheory
theorem _root_.solution [IsDomain R] (N : Submodule R M) :
    (saturation N : Set M) = {x | ∃ a : R, a ≠ 0 ∧ a • x ∈ N} := by
  ext x
  exact mem_saturation_iff
end GlobalTheory
