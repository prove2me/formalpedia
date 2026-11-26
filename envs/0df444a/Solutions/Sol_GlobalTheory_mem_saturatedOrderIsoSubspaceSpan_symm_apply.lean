-- Prove2me | solution 1 for GlobalTheory.mem_saturatedOrderIsoSubspaceSpan_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:23:54.679516+00:00
-- url     : https://prove2.me/submissions/497f8bb6-4cf8-473a-9e2c-a3fca7f11b20

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Mathlib


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
theorem _root_.solution (M : Submodule R V)
    (W : Submodule K (Submodule.span K (M : Set V))) (x : M) :
    x ∈ ((saturatedOrderIsoSubspaceSpan K M).symm W).1 ↔ M.inclusionSpan K x ∈ W := by
  first
    | (intros; rfl)
    | exact Iff.rfl
    | decide
    | (intros; omega)
    | (intros; simp)
    | (intros; simp_all)
    | (intros; norm_num)
    | (intros; positivity)
    | (intros; aesop)
    | (intros; nlinarith)
    | (intros; field_simp; ring)
    | (intros; ext; simp)
    | (intros; constructor <;> intro h <;> simpa using h)
    | (intros; exact?)
  trace "HIT_30_28"

