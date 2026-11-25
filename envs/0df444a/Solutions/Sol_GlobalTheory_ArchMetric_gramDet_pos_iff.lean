-- Prove2me | solution 1 for GlobalTheory.ArchMetric.gramDet_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:25:42.052173+00:00
-- url     : https://prove2.me/submissions/bfa71c1c-459c-4808-99d3-2fef5d971feb

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
variable (σ : K →+* ℂ) {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace GlobalTheory.ArchMetric
theorem _root_.solution {e : ι → V} : 0 < h.gramDet σ e ↔ LinearIndependent K e := by
  refine ⟨fun hp => ?_, h.gramDet_pos σ⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hd : (h.gram σ e).det ≠ 0 := by
    rw [← ofReal_gramDet]
    exact_mod_cast hp.ne'
  have hz : (fun j => σ (c j)) ᵥ* h.gram σ e = 0 := by
    ext j
    have := congrArg (fun x => h.form σ x (e j)) hc
    simpa [Matrix.vecMul, dotProduct, map_sum, LinearMap.map_smulₛₗ] using this
  have := congrFun (Matrix.eq_zero_of_vecMul_eq_zero hd hz) i
  simpa using this
end GlobalTheory.ArchMetric
