-- Prove2me | solution 1 for GlobalTheory.rank_eq_rank_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:30:37.361262+00:00
-- url     : https://prove2.me/submissions/93575839-a6e5-4803-872a-aa7d5eb0e10a

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
theorem _root_.solution (N : Submodule R V) :
    Module.rank R N = Module.rank K (Submodule.span K (N : Set V)) := by
  have := isLocalizedModule_inclusionSpan K R⁰ N
  rw [IsLocalization.rank_eq K R⁰ le_rfl, IsLocalizedModule.rank_eq R⁰ le_rfl (N.inclusionSpan K)]
end GlobalTheory
