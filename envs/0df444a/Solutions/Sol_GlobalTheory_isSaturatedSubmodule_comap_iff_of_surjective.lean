-- Prove2me | solution 1 for GlobalTheory.isSaturatedSubmodule_comap_iff_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:39:19.175942+00:00
-- url     : https://prove2.me/submissions/efc779cd-f362-40bb-ae60-1e1710013e1c

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
theorem _root_.solution {f : M →ₗ[R] M'}
    (hf : Function.Surjective f) {N : Submodule R M'} :
    IsSaturatedSubmodule (N.comap f) ↔ IsSaturatedSubmodule N := by
  unfold IsSaturatedSubmodule
  rw [saturation_comap]
  exact (Submodule.comap_injective_of_surjective hf).eq_iff
end GlobalTheory
