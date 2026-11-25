-- Prove2me | solution 1 for GlobalTheory.ArchMetric.conjInvariant_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:27:04.882437+00:00
-- url     : https://prove2.me/submissions/b0eb8ed7-6838-4e0a-b68b-2160ed9e702b

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
theorem _root_.solution {ι : Type*} [Fintype ι] {d : (K →+* ℂ) → ι → ℝ}
    (hd : ∀ σ i, 0 < d σ i) (hc : ∀ σ, d (ComplexEmbedding.conjugate σ) = d σ) :
    (diag d hd).ConjInvariant := fun σ x y => by
  simp [diag_form, hc]
end GlobalTheory.ArchMetric
