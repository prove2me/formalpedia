-- Prove2me | solution 1 for GlobalTheory.ThetaFamily.exists_entire_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:34.876799+00:00
-- url     : https://prove2.me/submissions/86cd877b-084e-4855-9ece-4b606af78d57

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DifferentiableOnQuotientOfDifferentiableOnSlice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfFiniteOfClosedFibres

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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {θ θ' : E → ℂ}
    (hfr : ∀ z, ∃ᶠ w in 𝓝 z, θ' w ≠ 0)
    (h : ∀ z, ∃ ρ : E → ℂ, ρ z ≠ 0 ∧ ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ρ w ∧ ρ w * θ' w = θ w) :
    ∃ ρ : E → ℂ, Differentiable ℂ ρ ∧ (∀ z, ρ z ≠ 0) ∧ ∀ z, ρ z * θ' z = θ z := by
  choose ρ h0 h using h
  refine ⟨fun z => ρ z z, fun z => ?_, h0, fun z => (h z).self_of_nhds.2⟩
  refine (h z).self_of_nhds.1.congr_of_eventuallyEq ?_
  filter_upwards [(h z).eventually_nhds] with w hw
  refine tendsto_nhds_unique_of_frequently_eq (h w).self_of_nhds.1.continuousAt hw.self_of_nhds.1.continuousAt ?_
  exact (((hfr w).and_eventually (h w)).and_eventually hw).mono fun u hu =>
    mul_right_cancel₀ hu.1.1 (hu.1.2.2.trans hu.2.2.symm)
end GlobalTheory.ThetaFamily
