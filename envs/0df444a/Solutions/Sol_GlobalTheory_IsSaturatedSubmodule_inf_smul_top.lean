-- Prove2me | solution 1 for GlobalTheory.IsSaturatedSubmodule.inf_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:03:31.149803+00:00
-- url     : https://prove2.me/submissions/0fe75392-a4fe-482a-b672-d40d5034ea0f

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
    (h : IsSaturatedSubmodule N) {a : R} (ha : a ≠ 0) :
    N ⊓ a • (⊤ : Submodule R M) = a • N := by
  ext x
  rw [Submodule.mem_inf, Submodule.mem_smul_pointwise_iff_exists,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨hx, y, -, rfl⟩
    exact ⟨y, h.mem_of_smul_mem ha hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨N.smul_mem a hy, y, Submodule.mem_top, rfl⟩
end IsSaturatedSubmodule
end GlobalTheory
