-- Prove2me | solution 1 for GlobalTheory.ArchMetric.ConjInvariant.norm_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:28:30.662856+00:00
-- url     : https://prove2.me/submissions/52b455ab-12c7-4453-8ff6-2678f605be53

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
variable {h}
namespace GlobalTheory.ArchMetric
namespace ConjInvariant
theorem _root_.solution (hc : h.ConjInvariant) (σ : K →+* ℂ) (x : V) :
    h.norm (ComplexEmbedding.conjugate σ) x = h.norm σ x := by
  rw [norm, hc σ, Complex.conj_re, norm]
end ConjInvariant
end GlobalTheory.ArchMetric
