-- Prove2me | solution 1 for GlobalTheory.aestronglyMeasurable_fderiv_of_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:33:59.635675+00:00
-- url     : https://prove2.me/submissions/98b3c024-9696-4e50-a7c7-24ed53bf9af3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Theorems.Thm_GlobalTheory_aestronglyMeasurable_fderiv_apply_of_param

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
namespace GlobalTheory
theorem _root_.solution {F : T → E → V} {x₀ : E}
    (hmeas : ∀ᶠ y in 𝓝 x₀, AEStronglyMeasurable (fun t => F t y) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableAt ℂ (F t) x₀) :
    AEStronglyMeasurable (fun t => fderiv ℂ (F t) x₀) μ := by
  let b := Module.finBasis ℂ E
  have key : (fun t => fderiv ℂ (F t) x₀) = fun t =>
      ∑ i, ContinuousLinearMap.smulRightL ℂ E V
        (LinearMap.toContinuousLinearMap (b.coord i)) (fderiv ℂ (F t) x₀ (b i)) := by
    funext t
    ext v
    have h : fderiv ℂ (F t) x₀ v = ∑ i, (b.repr v) i • fderiv ℂ (F t) x₀ (b i) := by
      conv_lhs => rw [← b.sum_repr v]
      simp only [map_sum, map_smul]
    simpa using h
  rw [key]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  exact (ContinuousLinearMap.smulRightL ℂ E V
    (LinearMap.toContinuousLinearMap (b.coord i))).continuous.comp_aestronglyMeasurable
      (aestronglyMeasurable_fderiv_apply_of_param hmeas hdiff (b i))
end GlobalTheory
