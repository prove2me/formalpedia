-- Prove2me | solution 1 for GlobalTheory.saturatedOrderIsoSubspace_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:32:41.353792+00:00
-- url     : https://prove2.me/submissions/17d97f4a-2041-4448-81ad-83b5268d3b61

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
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  (f : M →ₗ[R] V) [IsLocalizedModule R⁰ f]
namespace GlobalTheory
theorem _root_.solution (N : {N : Submodule R M // IsSaturatedSubmodule N}) :
    saturatedOrderIsoSubspace K f N = Submodule.span K (f '' N.1) := by
  show N.1.localized' K R⁰ f = _
  exact Submodule.localized'_eq_span K R⁰ f N.1
end GlobalTheory
