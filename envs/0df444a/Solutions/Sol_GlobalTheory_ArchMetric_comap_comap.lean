-- Prove2me | solution 1 for GlobalTheory.ArchMetric.comap_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:29:01.312848+00:00
-- url     : https://prove2.me/submissions/599f03a4-7993-4dc7-89cf-0e79cdcbea99

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
theorem _root_.solution (g : V'' →ₗ[K] V') (hg : Function.Injective g) :
    (h.comap f hf).comap g hg = h.comap (f ∘ₗ g) (hf.comp hg) := rfl
end GlobalTheory.ArchMetric
