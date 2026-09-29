-- Prove2me | solution 1 for MeasureTheory.tendsto_integral_mul_nhdsGT_of_tendstoUniformlyOn_tsupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/6e2866b0-f16f-57b4-9938-69a6ba63b485

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_tendsto_integral_mul_nhdsGT_of_tendstoUniformlyOn_tsupport

set_option autoImplicit false

open MeasureTheory Filter

theorem solution
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (w : X → ℝ) (hwm : Measurable w) (hwc : HasCompactSupport w) (hwb : ∃ B : ℝ, ∀ x, |w x| ≤ B)
    (Φ : ℝ → X → ℂ) (Φ₀ : X → ℂ)
    (hΦm : ∀ θ : ℝ, AEStronglyMeasurable (Φ θ) μ) (hΦ₀m : AEStronglyMeasurable Φ₀ μ)
    (hΦ₀b : ∃ B₀ : ℝ, ∀ x ∈ tsupport w, ‖Φ₀ x‖ ≤ B₀)
    (hunif : TendstoUniformlyOn Φ Φ₀ (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (tsupport w)) :
    Tendsto (fun θ : ℝ => ∫ x, Φ θ x * (w x : ℂ) ∂μ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ x, Φ₀ x * (w x : ℂ) ∂μ)) := by
  obtain ⟨B, hB⟩ := hwb
  obtain ⟨B₀, hB₀⟩ := hΦ₀b
  have hwz : ∀ x, x ∉ tsupport w → w x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun x => (B₀ + 1) * |w x|) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun θ =>
      (hΦm θ).mul (Complex.continuous_ofReal.measurable.comp hwm).aestronglyMeasurable
  · have h1 := (Metric.tendstoUniformlyOn_iff.1 hunif) 1 one_pos
    filter_upwards [h1] with θ hθ
    refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ tsupport w
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have hd := hθ x hx
      rw [Complex.dist_eq] at hd
      calc ‖Φ θ x‖ ≤ ‖Φ₀ x‖ + ‖Φ θ x - Φ₀ x‖ := norm_le_norm_add_norm_sub' _ _
        _ ≤ B₀ + 1 := by
            have : ‖Φ θ x - Φ₀ x‖ = ‖Φ₀ x - Φ θ x‖ := norm_sub_rev _ _
            linarith [hB₀ x hx]
    · rw [hwz x hx]; simp
  ·
    have hK : IsCompact (tsupport w) := hwc
    have hint : IntegrableOn (fun x => (B₀ + 1) * |w x|) (tsupport w) μ := by
      refine Measure.integrableOn_of_bounded (M := (|B₀| + 1) * B) hK.measure_lt_top.ne ?_ ?_
      · exact ((measurable_const.mul (hwm.abs))).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun x => ?_
        rw [Real.norm_eq_abs, abs_mul, abs_abs]
        exact mul_le_mul ((abs_add_le B₀ 1).trans_eq (by rw [abs_one])) (hB x) (abs_nonneg _) (by positivity)
    refine hint.integrable_of_ae_notMem_eq_zero (Filter.Eventually.of_forall fun x hx => ?_)
    rw [hwz x hx]; simp
  · refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ tsupport w
    · exact (hunif.tendsto_at hx).mul tendsto_const_nhds
    · rw [hwz x hx]; simp

end S_MeasureTheory_tendsto_integral_mul_nhdsGT_of_tendstoUniformlyOn_tsupport
end P2MW
export P2MW.S_MeasureTheory_tendsto_integral_mul_nhdsGT_of_tendstoUniformlyOn_tsupport (solution)
