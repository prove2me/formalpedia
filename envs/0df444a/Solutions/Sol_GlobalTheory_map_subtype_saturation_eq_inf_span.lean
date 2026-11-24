-- Prove2me | solution 1 for GlobalTheory.map_subtype_saturation_eq_inf_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:39:45.221412+00:00
-- url     : https://prove2.me/submissions/65d85525-2e9e-42d4-bad9-7570db749f50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_map_subtype_saturation

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
theorem _root_.solution (M : Submodule R V) (N : Submodule R M) :
    (saturation N).map M.subtype =
      M ⊓ (Submodule.span K (N.map M.subtype : Set V)).restrictScalars R := by
  rw [map_subtype_saturation, saturationIn_eq_inf_span K]
end GlobalTheory
