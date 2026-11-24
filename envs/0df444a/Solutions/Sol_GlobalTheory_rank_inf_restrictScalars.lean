-- Prove2me | solution 1 for GlobalTheory.rank_inf_restrictScalars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:37:47.014134+00:00
-- url     : https://prove2.me/submissions/e58e4df5-5d10-4bbd-886c-90240264d146

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_rank_eq_rank_span

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
    (h : W ≤ Submodule.span K (M : Set V)) :
    Module.rank R (M ⊓ W.restrictScalars R : Submodule R V) = Module.rank K W := by
  rw [rank_eq_rank_span K, span_inf_restrictScalars_of_le h]
end GlobalTheory
