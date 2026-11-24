-- Prove2me | solution 1 for GlobalTheory.smul_inf_restrictScalars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:33:50.237231+00:00
-- url     : https://prove2.me/submissions/97b8d71f-d28f-45aa-a7ae-c0ffb5123686

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
variable {R : Type*} [CommRing R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
variable {K}
omit [IsFractionRing R K]
namespace GlobalTheory
theorem _root_.solution (M : Submodule R V) (W : Submodule K V) {c : K} (hc : c ≠ 0) :
    c • M ⊓ W.restrictScalars R = c • (M ⊓ W.restrictScalars R) := by
  ext x
  simp only [Submodule.mem_inf, Submodule.mem_smul_pointwise_iff_exists,
    Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hw⟩
    refine ⟨y, ⟨hy, ?_⟩, rfl⟩
    have hw' := W.smul_mem c⁻¹ hw
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at hw'
  · rintro ⟨y, ⟨hy, hw⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, W.smul_mem c hw⟩
end GlobalTheory
