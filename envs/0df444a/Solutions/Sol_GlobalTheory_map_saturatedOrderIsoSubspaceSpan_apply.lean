-- Prove2me | solution 1 for GlobalTheory.map_saturatedOrderIsoSubspaceSpan_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:40:03.562309+00:00
-- url     : https://prove2.me/submissions/de2f1031-78a9-4e08-9606-376ac4d02f1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_saturatedOrderIsoSubspace_apply

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
    (N : {N : Submodule R M // IsSaturatedSubmodule N}) :
    (saturatedOrderIsoSubspaceSpan K M N).map (Submodule.span K (M : Set V)).subtype =
      Submodule.span K (N.1.map M.subtype : Set V) := by
  have := isLocalizedModule_inclusionSpan K R⁰ M
  have e : saturatedOrderIsoSubspaceSpan K M N = Submodule.span K (M.inclusionSpan K '' N.1) :=
    saturatedOrderIsoSubspace_apply K (M.inclusionSpan K) N
  rw [e, Submodule.map_span, ← Set.image_comp]
  rfl
end GlobalTheory
