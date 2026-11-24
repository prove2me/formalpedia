-- Prove2me | solution 1 for GlobalTheory.isSaturatedSubmodule_of_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:10:23.320333+00:00
-- url     : https://prove2.me/submissions/0f145b7d-85eb-490e-a731-964555e5aff3

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
theorem _root_.solution {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (W : Submodule K V) : IsSaturatedSubmodule W := by
  rw [isSaturatedSubmodule_iff]
  intro a ha x hx
  have hx' := W.smul_mem a⁻¹ hx
  rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at hx'
end GlobalTheory
