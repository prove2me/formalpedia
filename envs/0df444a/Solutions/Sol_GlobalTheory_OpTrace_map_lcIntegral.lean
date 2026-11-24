-- Prove2me | solution 1 for GlobalTheory.OpTrace.map_lcIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:13.31533+00:00
-- url     : https://prove2.me/submissions/5184b12f-a302-44a6-bdbc-3edfb34f7fe8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_finite_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace Pointwise
noncomputable section
open GlobalTheory GlobalTheory.OpTrace
variable {X V : Type*} [TopologicalSpace X] [AddCommGroup V] [Module ℂ V]
variable [MeasurableSpace X]
variable [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
namespace GlobalTheory.OpTrace
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {F : X → V} (hF : IsLocallyConstant F) (hc : HasCompactSupport F) (l : V →ₗ[ℂ] E) :
    l (lcIntegral μ F) = ∫ x, l (F x) ∂μ := by
  classical
  have hfin := finite_range hF hc
  have h1 : lcIntegral μ F = ∑ w ∈ hfin.toFinset, (μ.real (F ⁻¹' {w}) : ℂ) • w := by
    refine finsum_eq_sum_of_support_subset _ fun w hw => ?_
    by_contra hn
    have : F ⁻¹' {w} = ∅ := Set.preimage_singleton_eq_empty.2 (by simpa using hn)
    simp [this] at hw
  have h2 : ∀ x, l (F x) = ∑ w ∈ hfin.toFinset, (F ⁻¹' {w}).indicator (fun _ => l w) x := by
    intro x
    simp [Set.indicator_apply]
  simp only [h1, h2, map_sum, map_smul]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [integral_indicator_const _ (hF _).measurableSet, Complex.coe_smul]
  · intro w _
    by_cases hw : w = 0
    · simp [hw]
    · rw [integrable_indicator_iff (hF _).measurableSet]
      refine integrableOn_const (ne_top_of_le_ne_top hc.isCompact.measure_ne_top
        (measure_mono fun x hx => subset_tsupport F ?_))
      rw [Function.mem_support, show F x = w from hx]
      exact hw
end GlobalTheory.OpTrace
