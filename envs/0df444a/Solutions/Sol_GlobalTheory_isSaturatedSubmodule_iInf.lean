-- Prove2me | solution 1 for GlobalTheory.isSaturatedSubmodule_iInf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:39:25.398879+00:00
-- url     : https://prove2.me/submissions/8f012d43-02e2-4f8b-9a27-ece9e6d1bbd9

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
theorem _root_.solution {ι : Sort*} {N : ι → Submodule R M}
    (h : ∀ i, IsSaturatedSubmodule (N i)) : IsSaturatedSubmodule (⨅ i, N i) := by
  rw [isSaturatedSubmodule_iff_le]
  intro x hx
  rw [Submodule.mem_iInf]
  intro i
  exact (h i).saturation_eq.le (saturation_mono (iInf_le N i) hx)
end GlobalTheory
