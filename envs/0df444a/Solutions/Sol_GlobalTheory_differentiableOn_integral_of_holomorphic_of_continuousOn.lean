-- Prove2me | solution 1 for GlobalTheory.differentiableOn_integral_of_holomorphic_of_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:24:48.870417+00:00
-- url     : https://prove2.me/submissions/45e438c8-3bdc-49fa-9b7b-8578d4f10fee

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
theorem _root_.solution [TopologicalSpace T]
    [OpensMeasurableSpace T] [CompactSpace T] [IsFiniteMeasure μ] {F : T → E → V} {U : Set E}
    (hU : IsOpen U) (hcont : ContinuousOn (Function.uncurry F) (univ ×ˢ U))
    (hdiff : ∀ t, DifferentiableOn ℂ (F t) U) :
    DifferentiableOn ℂ (fun y => ∫ t, F t y ∂μ) U ∧
      ∀ x ∈ U, Integrable (fun t => F t x) μ ∧ Integrable (fun t => fderiv ℂ (F t) x) μ ∧
        HasFDerivAt (fun y => ∫ t, F t y ∂μ) (∫ t, fderiv ℂ (F t) x ∂μ) x := by
  simpa only [Measure.restrict_univ, integrableOn_univ] using
    differentiableOn_setIntegral_of_holomorphic_of_continuousOn (μ := μ) hU isCompact_univ
      subset_rfl MeasurableSet.univ (measure_ne_top μ _) hcont fun t _ => hdiff t
end GlobalTheory
