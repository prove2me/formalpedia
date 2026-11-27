-- Prove2me | solution 1 for GlobalTheory.finrank_inf_restrictScalars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:41:23.063623+00:00
-- url     : https://prove2.me/submissions/0002e091-80a6-4f3d-bfa5-cfa0966ea453

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_rank_inf_restrictScalars

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
theorem _root_.solution {M : Submodule R V} {W : Submodule K V}
    [FiniteDimensional K W] (h : W ≤ Submodule.span K (M : Set V)) :
    Module.finrank R (M ⊓ W.restrictScalars R : Submodule R V) = Module.finrank K W := congrArg Cardinal.toNat (rank_inf_restrictScalars h)
end GlobalTheory
