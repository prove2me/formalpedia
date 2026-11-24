-- Prove2me | solution 1 for GlobalTheory.SetIntegralSmoothness.hasFDerivAt_setIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:45:33.330223+00:00
-- url     : https://prove2.me/submissions/c8d2b1e2-9391-4d16-ae35-b1b695c79d25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HasFDerivAtSetIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set
open scoped ContDiff
open GlobalTheory GlobalTheory.SetIntegralSmoothness
namespace GlobalTheory.SetIntegralSmoothness
theorem _root_.solution {X P E : Type} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K)
    {a : X → E} (ha : Continuous a) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : P × E → F) (hΨ : ContDiff ℝ ∞ Ψ) (p₀ : P) :
    HasFDerivAt (fun p : P => ∫ x in K, Ψ (p, a x) ∂μ)
      (∫ x in K, (fderiv ℝ Ψ (p₀, a x)).comp (ContinuousLinearMap.inl ℝ P E) ∂μ) p₀ := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hΨ1 : ContDiff ℝ 1 Ψ := hΨ.of_le (by exact_mod_cast le_top)
  have hdΨ : Continuous (fderiv ℝ Ψ) := hΨ1.continuous_fderiv one_ne_zero
  have hS : IsCompact (closedBall p₀ 1 ×ˢ (a '' K)) := (isCompact_closedBall p₀ 1).prod (hK.image ha)
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hdΨ.continuousOn
  have hcont : ∀ p : P, Continuous fun x : X => Ψ (p, a x) :=
    fun p => hΨ.continuous.comp (continuous_const.prodMk ha)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ.restrict K) (x₀ := p₀)
    (F := fun p x => Ψ (p, a x)) (F' := fun p x => (fderiv ℝ Ψ (p, a x)).comp (ContinuousLinearMap.inl ℝ P E))
    (bound := fun _ => C * ‖ContinuousLinearMap.inl ℝ P E‖)
    (closedBall_mem_nhds p₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun p =>
      (hcont p).continuousOn.aestronglyMeasurable_of_isCompact hK hKm
  · exact (hcont p₀).continuousOn.integrableOn_compact hK
  · exact ((hdΨ.comp (continuous_const.prodMk ha)).clm_comp continuous_const).continuousOn.aestronglyMeasurable_of_isCompact hK hKm
  · refine (ae_restrict_iff' hKm).mpr (Filter.Eventually.of_forall fun x hx p hp => ?_)
    calc ‖(fderiv ℝ Ψ (p, a x)).comp (ContinuousLinearMap.inl ℝ P E)‖
        ≤ ‖fderiv ℝ Ψ (p, a x)‖ * ‖ContinuousLinearMap.inl ℝ P E‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * ‖ContinuousLinearMap.inl ℝ P E‖ :=
        mul_le_mul_of_nonneg_right (hC _ ⟨hp, mem_image_of_mem a hx⟩) (norm_nonneg _)
  · exact integrableOn_const hK.measure_ne_top
  · exact Filter.Eventually.of_forall fun x p _ =>
      ((hΨ1.differentiable one_ne_zero) (p, a x)).hasFDerivAt.comp p (hasFDerivAt_prodMk_left p (a x))
end GlobalTheory.SetIntegralSmoothness
