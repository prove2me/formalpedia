-- Prove2me | solution 1 for GlobalTheory.ArchMetric.restrict_gramDet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:25:09.924553+00:00
-- url     : https://prove2.me/submissions/699b68b5-35e9-4ce2-a86d-5da61616466a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice

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
variable {K : Type*} [Field K] {V V' V'' : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V'] [AddCommGroup V''] [Module K V'']
variable (h : ArchMetric K V)
namespace GlobalTheory.ArchMetric
theorem _root_.solution (W : Submodule K V) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (e : ι → W) :
    (h.restrict W).gramDet σ e = h.gramDet σ fun i => (e i : V) := rfl
end GlobalTheory.ArchMetric
