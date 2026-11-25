-- Prove2me | solution 1 for GlobalTheory.isSaturatedIn_iff_exists_subspace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:06:18.163214+00:00
-- url     : https://prove2.me/submissions/3505f9fb-4eb7-4fac-959b-ab3291a5ddb5

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
namespace GlobalTheory
theorem _root_.solution {M N : Submodule R V} :
    IsSaturatedIn M N ↔ ∃ W : Submodule K V, M ⊓ W.restrictScalars R = N := by
  constructor
  · intro h
    exact ⟨Submodule.span K (N : Set V), (isSaturatedIn_iff_inf_span_eq K).1 h⟩
  · rintro ⟨W, rfl⟩
    exact isSaturatedIn_inf_restrictScalars M W
end GlobalTheory
