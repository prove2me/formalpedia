-- Prove2me | solution 2 for GlobalTheory.mem_saturatedOrderIsoSubspaceSpan_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:41:04.301344+00:00
-- url     : https://prove2.me/submissions/4d60f77b-486f-4d61-bddc-4eaba48c225f

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
theorem _root_.solution (M : Submodule R V)
    (W : Submodule K (Submodule.span K (M : Set V))) (x : M) :
    x ∈ ((saturatedOrderIsoSubspaceSpan K M).symm W).1 ↔ M.inclusionSpan K x ∈ W := Iff.rfl
end GlobalTheory
