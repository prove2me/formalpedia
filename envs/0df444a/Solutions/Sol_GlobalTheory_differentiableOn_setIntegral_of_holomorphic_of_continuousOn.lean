-- Prove2me | solution 1 for GlobalTheory.differentiableOn_setIntegral_of_holomorphic_of_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:17:11.429326+00:00
-- url     : https://prove2.me/submissions/4b96f3bb-cf79-4c34-a4b5-18273507250f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Theorems.Thm_GlobalTheory_differentiableOn_integral_of_holomorphic_of_locally_dominated

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
    [OpensMeasurableSpace T] {F : T → E → V} {U : Set E} (hU : IsOpen U) {S K : Set T}
    (hK : IsCompact K) (hSK : S ⊆ K) (hS : MeasurableSet S) (hfin : μ S ≠ ⊤)
    (hcont : ContinuousOn (Function.uncurry F) (K ×ˢ U))
    (hdiff : ∀ t ∈ S, DifferentiableOn ℂ (F t) U) :
    DifferentiableOn ℂ (fun y => ∫ t in S, F t y ∂μ) U ∧
      ∀ x ∈ U, IntegrableOn (fun t => F t x) S μ ∧
        IntegrableOn (fun t => fderiv ℂ (F t) x) S μ ∧
        HasFDerivAt (fun y => ∫ t in S, F t y ∂μ) (∫ t in S, fderiv ℂ (F t) x ∂μ) x := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have : IsFiniteMeasure (μ.restrict S) := ⟨by simpa using hfin.lt_top⟩
  refine differentiableOn_integral_of_holomorphic_of_locally_dominated (μ := μ.restrict S) hU
    (fun y hy => ?_) (ae_restrict_of_forall_mem hS hdiff) (fun x hx => ?_)
  · have : ContinuousOn (fun t => F t y) K :=
      hcont.comp (f := fun t => (t, y)) (by fun_prop) fun t ht => ⟨ht, hy⟩
    exact this.aestronglyMeasurable_of_subset_isCompact hK hS hSK
  · obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
    obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall x r)).exists_bound_of_continuousOn
      (hcont.mono (prod_mono subset_rfl hrU))
    refine ⟨closedBall x r, closedBall_mem_nhds x hr, fun _ => C, integrable_const C, ?_⟩
    exact ae_restrict_of_forall_mem hS fun t ht y hy => hC (t, y) ⟨hSK ht, hy⟩
end GlobalTheory
