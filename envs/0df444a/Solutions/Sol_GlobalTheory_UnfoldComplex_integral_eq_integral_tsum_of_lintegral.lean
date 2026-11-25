-- Prove2me | solution 1 for GlobalTheory.UnfoldComplex.integral_eq_integral_tsum_of_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:22:38.43267+00:00
-- url     : https://prove2.me/submissions/719bb9e6-72d0-4025-ae39-86b541edfbc4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IntegralEqIntegralTsumOfLintegral
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.UnfoldComplex
namespace GlobalTheory.UnfoldComplex
theorem _root_.solution {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ ν : Measure α) (f : α → ℂ) (g : ι → α → ℂ) (hf : Measurable f) (hg : ∀ i, Measurable (g i))
    (H : ∀ φ : ℂ → ℝ≥0∞, Measurable φ → ∫⁻ z, φ (f z) ∂μ = ∫⁻ z, ∑' i, φ (g i z) ∂ν)
    (hi : Integrable f μ) : ∫ z, f z ∂μ = ∫ z, ∑' i, g i z ∂ν := by
  have hmap : μ.map f = Measure.sum fun i => ν.map (g i) := by
    ext s hs
    have hφ : Measurable (s.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hs
    have h1 := H _ hφ
    rw [lintegral_tsum (f := fun i z => s.indicator (1 : ℂ → ℝ≥0∞) (g i z))
      fun i => (hφ.comp (hg i)).aemeasurable] at h1
    rw [Measure.sum_apply _ hs, ← lintegral_indicator_one hs, lintegral_map hφ hf, h1]
    refine tsum_congr fun i => ?_
    rw [← lintegral_indicator_one hs, lintegral_map hφ (hg i)]
  have hfin : ∑' i, ∫⁻ z, ‖g i z‖ₑ ∂ν ≠ ⊤ := by
    have h1 := H (fun w => ‖w‖ₑ) measurable_enorm
    rw [lintegral_tsum fun i => (hg i).enorm.aemeasurable] at h1
    rw [← h1]
    exact hi.2.ne
  have hid : Integrable (fun w : ℂ => w) (μ.map f) :=
    (integrable_map_measure aestronglyMeasurable_id hf.aemeasurable).mpr hi
  rw [integral_tsum (fun i => (hg i).aestronglyMeasurable) hfin]
  calc ∫ z, f z ∂μ = ∫ w, w ∂(μ.map f) := (integral_map hf.aemeasurable aestronglyMeasurable_id).symm
    _ = ∑' i, ∫ w, w ∂(ν.map (g i)) := by
        rw [hmap] at hid ⊢
        exact integral_sum_measure hid
    _ = ∑' i, ∫ z, g i z ∂ν :=
        tsum_congr fun i => integral_map (hg i).aemeasurable aestronglyMeasurable_id
end GlobalTheory.UnfoldComplex
