-- Prove2me | solution 1 for GlobalTheory.IsSaturatedSubmodule.inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:32.332273+00:00
-- url     : https://prove2.me/submissions/7bac7e07-7107-4492-8ba2-75d6a72f1ea0

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
theorem _root_.solution {N P : Submodule R M} (hN : IsSaturatedSubmodule N)
    (hP : IsSaturatedSubmodule P) : IsSaturatedSubmodule (N ⊓ P) := by
  unfold IsSaturatedSubmodule
  rw [saturation_inf, hN.saturation_eq, hP.saturation_eq]
end IsSaturatedSubmodule
end GlobalTheory
