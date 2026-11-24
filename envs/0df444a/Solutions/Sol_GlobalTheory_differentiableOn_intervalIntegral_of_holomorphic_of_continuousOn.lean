-- Prove2me | solution 1 for GlobalTheory.differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:25:07.240628+00:00
-- url     : https://prove2.me/submissions/3a868b59-b298-405a-9622-1b40f4dab7b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Theorems.Thm_GlobalTheory_differentiableOn_setIntegral_of_holomorphic_of_continuousOn

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
theorem _root_.solution {F : ℝ → E → V}
    {U : Set E} (hU : IsOpen U) {a b : ℝ}
    (hcont : ContinuousOn (Function.uncurry F) ([[a, b]] ×ˢ U))
    (hdiff : ∀ t ∈ [[a, b]], DifferentiableOn ℂ (F t) U) :
    DifferentiableOn ℂ (fun y => ∫ t in a..b, F t y) U ∧
      ∀ x ∈ U, IntervalIntegrable (fun t => F t x) volume a b ∧
        IntervalIntegrable (fun t => fderiv ℂ (F t) x) volume a b ∧
        HasFDerivAt (fun y => ∫ t in a..b, F t y) (∫ t in a..b, fderiv ℂ (F t) x) x := by
  have h := differentiableOn_setIntegral_of_holomorphic_of_continuousOn (μ := volume) hU
    (isCompact_uIcc (a := a) (b := b)) uIoc_subset_uIcc measurableSet_uIoc
    (by simp [uIoc]) hcont fun t ht => hdiff t (uIoc_subset_uIcc ht)
  have key : ∀ x ∈ U, IntervalIntegrable (fun t => F t x) volume a b ∧
      IntervalIntegrable (fun t => fderiv ℂ (F t) x) volume a b ∧
      HasFDerivAt (fun y => ∫ t in a..b, F t y) (∫ t in a..b, fderiv ℂ (F t) x) x := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := h.2 x hx
    refine ⟨intervalIntegrable_iff.2 h1, intervalIntegrable_iff.2 h2, ?_⟩
    simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    split_ifs
    · simpa using h3
    · simpa using h3.fun_neg
  exact ⟨fun x hx => (key x hx).2.2.differentiableAt.differentiableWithinAt, key⟩
end GlobalTheory
