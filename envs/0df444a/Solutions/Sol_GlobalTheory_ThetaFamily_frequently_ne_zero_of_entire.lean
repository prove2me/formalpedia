-- Prove2me | solution 1 for GlobalTheory.ThetaFamily.frequently_ne_zero_of_entire
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:29:56.649809+00:00
-- url     : https://prove2.me/submissions/2e309fb9-271a-48cb-a80d-b470fab8f8de

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DifferentiableOnQuotientOfDifferentiableOnSlice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfFiniteOfClosedFibres
import Theorems.Thm_GlobalTheory_SCV_analyticOnNhd_of_differentiable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Metric Set
open scoped Topology
open GlobalTheory GlobalTheory.ThetaFamily
namespace GlobalTheory.ThetaFamily
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {θ : E → ℂ} (hd : Differentiable ℂ θ) (h0 : θ ≠ 0) (z : E) : ∃ᶠ w in 𝓝 z, θ w ≠ 0 := by
  intro h
  refine h0 (funext fun w => ?_)
  exact (SCV.analyticOnNhd_of_differentiable hd univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (mem_univ z) (h.mono fun _ hu => not_not.1 hu) (mem_univ w)
end GlobalTheory.ThetaFamily
