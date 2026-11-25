-- Prove2me | solution 1 for GlobalTheory.ThetaGauss.not_eventually_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:46:33.137607+00:00
-- url     : https://prove2.me/submissions/47ede898-18c4-4646-8abb-49de614f1168

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Metric
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaGauss
variable {g : ℕ}
namespace GlobalTheory.ThetaGauss
theorem _root_.solution {h : ℂ → ℂ} (hh : Differentiable ℂ h) (h0 : ∃ s, h s ≠ 0) (s₀ : ℂ) :
    ¬ ∀ᶠ s in 𝓝 s₀, h s = 0 := fun hz => by
  obtain ⟨s, hs⟩ := h0
  exact hs ((hh.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ s₀) hz (Set.mem_univ s))
end GlobalTheory.ThetaGauss
