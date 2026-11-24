-- Prove2me | solution 1 for GlobalTheory.IsSaturatedSubmodule.smul_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:11.471611+00:00
-- url     : https://prove2.me/submissions/7625a517-39a0-44fb-a777-e557917887c0

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
namespace IsSaturatedSubmodule
theorem _root_.solution [IsDomain R] {N : Submodule R M}
    (h : IsSaturatedSubmodule N) {a : R} (ha : a ≠ 0) {x : M} : a • x ∈ N ↔ x ∈ N := ⟨h.mem_of_smul_mem ha, fun hx => N.smul_mem a hx⟩
end IsSaturatedSubmodule
end GlobalTheory
