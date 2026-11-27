-- Prove2me | solution 2 for GlobalTheory.isSaturatedSubmodule_comap_restrictScalars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:39:20.721208+00:00
-- url     : https://prove2.me/submissions/6fa68b30-992b-42ca-bfc6-0610dc9ec47a

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
namespace GlobalTheory
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module R M]
    (f : M →ₗ[R] V) (W : Submodule K V) :
    IsSaturatedSubmodule ((W.restrictScalars R).comap f) := (isSaturatedSubmodule_restrictScalars W).comap f
end GlobalTheory
