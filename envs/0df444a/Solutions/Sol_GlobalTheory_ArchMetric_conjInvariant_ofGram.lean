-- Prove2me | solution 1 for GlobalTheory.ArchMetric.conjInvariant_ofGram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:25:17.362739+00:00
-- url     : https://prove2.me/submissions/18fda909-0baf-4820-8fd0-30d0b76626bc

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
theorem _root_.solution {ι : Type*} [Fintype ι] (b : Basis ι K V)
    {G : (K →+* ℂ) → Matrix ι ι ℂ} (hG : ∀ σ, (G σ).PosDef)
    (hc : ∀ σ i j, G (ComplexEmbedding.conjugate σ) i j = conj (G σ i j)) :
    (ofGram b G hG).ConjInvariant := fun σ x y => by
  simp [ofGram_form, hc]
end GlobalTheory.ArchMetric
