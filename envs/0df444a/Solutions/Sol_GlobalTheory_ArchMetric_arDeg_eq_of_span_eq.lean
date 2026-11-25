-- Prove2me | solution 1 for GlobalTheory.ArchMetric.arDeg_eq_of_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:28:33.30236+00:00
-- url     : https://prove2.me/submissions/6065c153-b141-4d1a-9903-ac29915cc9b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Theorems.Thm_GlobalTheory_ArchMetric_arDeg_sub_arDeg_of_span_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped ComplexOrder ComplexConjugate
open GlobalTheory
open GlobalTheory.ArchMetric
variable {K : Type*} [Field K] [NumberField K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : ArchMetric K V)
variable {A : Submodule (𝓞 K) V} {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.ArchMetric
theorem _root_.solution (hA : A.FG) {e : ι → V} (he : LinearIndependent K e)
    (hs : Submodule.span K (Set.range e) = Submodule.span K (A : Set V)) :
    h.arDeg A =
      Real.log ((Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex A.toAddSubgroup) -
        Real.log (A.toAddSubgroup.relIndex (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup) -
        ∑ σ : K →+* ℂ, 1 / 2 * Real.log (h.gramDet σ e) := by
  have := h.arDeg_sub_arDeg_of_span_eq hA (Submodule.fg_span (Set.finite_range e))
    (by rw [Submodule.span_span_of_tower, hs])
  rw [h.arDeg_span he] at this
  linarith
end GlobalTheory.ArchMetric
