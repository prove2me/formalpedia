-- Prove2me | solution 1 for GlobalTheory.ArchMetric.ConjInvariant.gramDet_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:28:28.631039+00:00
-- url     : https://prove2.me/submissions/8dce2357-9dae-40ff-ba98-98ec605305d7

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
variable {h}
namespace GlobalTheory.ArchMetric
namespace ConjInvariant
theorem _root_.solution (hc : h.ConjInvariant) (e : ι → V) :
    h.gramDet (ComplexEmbedding.conjugate σ) e = h.gramDet σ e := by
  have : h.gram (ComplexEmbedding.conjugate σ) e = (h.gram σ e)ᵀ := by
    ext i j
    simp [hc σ]
  rw [gramDet, this, Matrix.det_transpose, gramDet]
end ConjInvariant
end GlobalTheory.ArchMetric
