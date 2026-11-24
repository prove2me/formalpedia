-- Prove2me | solution 1 for GlobalTheory.map_saturation_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:33:51.268909+00:00
-- url     : https://prove2.me/submissions/158a9872-8dd4-476e-b412-6a31428599a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_map_saturation_of_injective

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
theorem _root_.solution (e : M ≃ₗ[R] M') (N : Submodule R M) :
    (saturation N).map (e : M →ₗ[R] M') = saturation (N.map (e : M →ₗ[R] M')) := by
  rw [map_saturation_of_injective e.injective, LinearEquiv.range, top_inf_eq]
end GlobalTheory
