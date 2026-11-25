-- Prove2me | solution 1 for GlobalTheory.ArchMetric.comap_gramDet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:25:09.244487+00:00
-- url     : https://prove2.me/submissions/10c7bfd4-4a29-48a7-bbeb-60c609fd34ee

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
variable (f : V' →ₗ[K] V) (hf : Function.Injective f) (σ : K →+* ℂ)
namespace GlobalTheory.ArchMetric
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → V') :
    (h.comap f hf).gramDet σ e = h.gramDet σ (f ∘ e) := rfl
end GlobalTheory.ArchMetric
