-- Prove2me | solution 1 for GlobalTheory.span_saturationIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:41:08.719995+00:00
-- url     : https://prove2.me/submissions/adf89907-36c3-4f0f-b9a5-e2b94234a778

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
theorem _root_.solution {M N : Submodule R V} (h : N ≤ M) :
    Submodule.span K (saturationIn M N : Set V) = Submodule.span K (N : Set V) := by
  rw [saturationIn_eq_inf_span K, span_inf_restrictScalars, inf_of_le_right (Submodule.span_mono h)]
end GlobalTheory
