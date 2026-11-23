-- Prove2me | solution 1 for GlobalTheory.IsQuasiRegularSeq.of_linearEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:37.772527+00:00
-- url     : https://prove2.me/submissions/c0074c78-905d-4e8b-bd96-71694d75ddb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
variable (M : Type*) [AddCommGroup M] [Module R M]
variable {M}
open GlobalTheory.IsQuasiRegularSeq
namespace GlobalTheory.IsQuasiRegularSeq
theorem _root_.solution {N : Type*} [AddCommGroup N] [Module R N] {f : ι → R}
    (h : IsQuasiRegularSeq M f) (e : M ≃ₗ[R] N) : IsQuasiRegularSeq N f := by
  intro a c hc α
  have := h a (fun β => e.symm (c β)) (by
    have := Submodule.smul_top_le_comap_smul_top _ e.symm.toLinearMap hc
    simpa using this) α
  simpa using Submodule.smul_top_le_comap_smul_top _ e.toLinearMap this
end GlobalTheory.IsQuasiRegularSeq
