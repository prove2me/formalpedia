-- Prove2me | solution 1 for GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:07:31.209798+00:00
-- url     : https://prove2.me/submissions/3c686171-1b41-422e-a4fe-051e733d449c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Theorems.Thm_GlobalTheory_hasFDerivAt_integral_of_holomorphic_of_dominated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Metric Set
open scoped Topology Interval
open GlobalTheory
variable {T : Type*} [MeasurableSpace T] {μ : Measure T}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable [FiniteDimensional ℂ E]
set_option linter.unusedSectionVars false
variable [CompleteSpace V]
namespace GlobalTheory
theorem _root_.solution {F : T → E → V}
    {U : Set E} (hU : IsOpen U)
    (hmeas : ∀ y ∈ U, AEStronglyMeasurable (fun t => F t y) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableOn ℂ (F t) U)
    (hdom : ∀ x ∈ U, ∃ s ∈ 𝓝 x, ∃ bound : T → ℝ, Integrable bound μ ∧
      ∀ᵐ t ∂μ, ∀ y ∈ s, ‖F t y‖ ≤ bound t) :
    DifferentiableOn ℂ (fun y => ∫ t, F t y ∂μ) U ∧
      ∀ x ∈ U, Integrable (fun t => F t x) μ ∧ Integrable (fun t => fderiv ℂ (F t) x) μ ∧
        HasFDerivAt (fun y => ∫ t, F t y ∂μ) (∫ t, fderiv ℂ (F t) x ∂μ) x := by
  have key : ∀ x ∈ U, Integrable (fun t => F t x) μ ∧ Integrable (fun t => fderiv ℂ (F t) x) μ ∧
      HasFDerivAt (fun y => ∫ t, F t y ∂μ) (∫ t, fderiv ℂ (F t) x ∂μ) x := by
    intro x hx
    obtain ⟨s, hs, bound, hint, hb⟩ := hdom x hx
    exact hasFDerivAt_integral_of_holomorphic_of_dominated (s := s ∩ U)
      (inter_mem hs (hU.mem_nhds hx)) (fun y hy => hmeas y hy.2)
      (hdiff.mono fun t ht => ht.mono inter_subset_right)
      (hb.mono fun t ht y hy => ht y hy.1) hint
  exact ⟨fun x hx => (key x hx).2.2.differentiableAt.differentiableWithinAt, key⟩
end GlobalTheory
