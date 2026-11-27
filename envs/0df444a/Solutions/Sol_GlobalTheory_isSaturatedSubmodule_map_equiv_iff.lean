-- Prove2me | solution 1 for GlobalTheory.isSaturatedSubmodule_map_equiv_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:39:44.678156+00:00
-- url     : https://prove2.me/submissions/ed25e429-96a8-4090-a5ad-b30d30df486d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_map_saturation_equiv

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
theorem _root_.solution (e : M ≃ₗ[R] M') {N : Submodule R M} :
    IsSaturatedSubmodule (N.map (e : M →ₗ[R] M')) ↔ IsSaturatedSubmodule N := by
  unfold IsSaturatedSubmodule
  rw [← map_saturation_equiv]
  exact (Submodule.map_injective_of_injective e.injective).eq_iff
end GlobalTheory
