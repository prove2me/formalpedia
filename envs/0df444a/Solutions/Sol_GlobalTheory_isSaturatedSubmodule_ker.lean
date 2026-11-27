-- Prove2me | solution 1 for GlobalTheory.isSaturatedSubmodule_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:39:40.496795+00:00
-- url     : https://prove2.me/submissions/524d3ead-99fe-4400-9d21-455c1b5f1b7d

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
theorem _root_.solution [IsDomain R] [Module.IsTorsionFree R M'] (f : M →ₗ[R] M') :
    IsSaturatedSubmodule (LinearMap.ker f) := by
  rw [isSaturatedSubmodule_iff]
  intro a ha x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [map_smul] at hx
  exact (smul_eq_zero_iff_right ha).1 hx
end GlobalTheory
