-- Prove2me | solution 1 for GlobalTheory.integrableOn_log_norm_ball_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:25:41.87581+00:00
-- url     : https://prove2.me/submissions/b45ea3b4-9c63-4bce-bd06-886b7e646047

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableOnOfNormLeSumAbsLogAddLogLog
import Theorems.Thm_GlobalTheory_log_norm_le_circleAverage_log_norm
import Theorems.Thm_GlobalTheory_measurePreserving_smul_of_norm_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal Real
namespace GlobalTheory
section Holomorphic
private theorem measurable_logGap (M : ℝ) : Measurable (logGap M) :=
  Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)
private theorem lintegral_logGap_circle_le {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (closedBall 0 1))
    (h0 : g 0 ≠ 0) {M : ℝ} (hM : ∀ z ∈ closedBall (0 : ℂ) 1, ‖g z‖ ≤ M) :
    ∫⁻ t in Ioc 0 (2 * π), logGap M (g (circleMap 0 1 t)) ≤
      ENNReal.ofReal (2 * π * (Real.log M - Real.log ‖g 0‖)) := by
  have h2 : (0 : ℝ) < 2 * π := by positivity
  have hne : ∀ᵐ t ∂(volume.restrict (Ioc 0 (2 * π))), g (circleMap 0 1 t) ≠ 0 := by
    have h1 := hg.preimage_zero_mem_codiscreteWithin h0 (mem_closedBall_self zero_le_one)
      (isConnected_closedBall zero_le_one)
    have h3 : g ⁻¹' {0}ᶜ ∈ codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|) :=
      codiscreteWithin_mono (by simpa using sphere_subset_closedBall) h1
    exact ae_restrict_le_codiscreteWithin measurableSet_Ioc
      (codiscreteWithin_mono (subset_univ _) (circleMap_preimage_codiscrete one_ne_zero h3))
  have hint : IntegrableOn (fun t => Real.log ‖g (circleMap 0 1 t)‖) (Ioc 0 (2 * π)) := by
    have h1 : CircleIntegrable (fun z => Real.log ‖g z‖) 0 1 :=
      MeromorphicOn.circleIntegrable_log_norm
        (hg.mono (by simpa using sphere_subset_closedBall)).meromorphicOn
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h2.le).1 h1
  have hc : IntegrableOn (fun _ : ℝ => Real.log M) (Ioc 0 (2 * π)) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hJ := log_norm_le_circleAverage_log_norm hg h0
  rw [Real.circleAverage, intervalIntegral.integral_of_le h2.le, smul_eq_mul,
    le_inv_mul_iff₀ h2] at hJ
  calc ∫⁻ t in Ioc 0 (2 * π), logGap M (g (circleMap 0 1 t))
      = ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (Real.log M - Real.log ‖g (circleMap 0 1 t)‖) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hne] with t ht
        simp [logGap, ht]
    _ = ENNReal.ofReal (∫ t in Ioc 0 (2 * π), (Real.log M - Real.log ‖g (circleMap 0 1 t)‖)) := by
        refine (ofReal_integral_eq_lintegral_ofReal (hc.sub hint) ?_).symm
        filter_upwards [hne] with t ht
        exact sub_nonneg.2 (Real.log_le_log (norm_pos_iff.2 ht)
          (hM _ (sphere_subset_closedBall (circleMap_mem_sphere 0 zero_le_one t))))
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_sub hc hint]
        simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter,
          Real.volume_real_Ioc, sub_zero, max_eq_left h2.le, smul_eq_mul]
        linarith
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]
end Holomorphic
section Coordinates
open Bornology
variable {ι : Type*} [Fintype ι]
variable {F : Type*} [NormedAddCommGroup F]
end Coordinates
end GlobalTheory
end

set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal Real
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GlobalTheory
theorem _root_.solution (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℂ}
    {r M : ℝ} (hf : DifferentiableOn ℂ f (ball 0 r)) (hM : ∀ z ∈ ball (0 : E) r, ‖f z‖ ≤ M)
    (h0 : f 0 ≠ 0) :
    (∀ᵐ z ∂(μ.restrict (ball 0 r)), f z ≠ 0) ∧
      IntegrableOn (fun z => Real.log ‖f z‖) (ball 0 r) μ := by
  classical
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have h2 : (0 : ℝ) < 2 * π := by positivity
  have hn : ∀ t, ‖circleMap 0 1 t‖ = 1 := fun t => by simp
  set F : E → ℂ := (ball (0 : E) r).piecewise f 0 with hF
  have hFm : Measurable F :=
    hf.continuousOn.measurable_piecewise continuousOn_const measurableSet_ball
  set G : E → ℝ≥0∞ := (ball (0 : E) r).indicator fun z => logGap M (F z) with hG
  have hGm : Measurable G := ((measurable_logGap M).comp hFm).indicator measurableSet_ball
  have hj : Measurable fun p : ℝ × E => G (circleMap 0 1 p.1 • p.2) := by
    refine hGm.comp (Continuous.measurable ?_)
    exact ((continuous_circleMap 0 1).comp continuous_fst).smul continuous_snd
  have hA : ∫⁻ t in Ioc 0 (2 * π), ∫⁻ z, G (circleMap 0 1 t • z) ∂μ =
      (∫⁻ z in ball 0 r, logGap M (F z) ∂μ) * ENNReal.ofReal (2 * π) := by
    have h4 : ∀ t, ∫⁻ z, G (circleMap 0 1 t • z) ∂μ = ∫⁻ z in ball 0 r, logGap M (F z) ∂μ :=
      fun t => by
        rw [(measurePreserving_smul_of_norm_eq_one μ (hn t)).lintegral_comp hGm, hG,
          lintegral_indicator measurableSet_ball]
    simp [h4]
  have hsm : ∀ z ∈ ball (0 : E) r, ∀ c ∈ closedBall (0 : ℂ) 1, c • z ∈ ball (0 : E) r := by
    intro z hz c hc
    rw [mem_ball_zero_iff] at hz ⊢
    rw [mem_closedBall_zero_iff] at hc
    calc ‖c • z‖ ≤ 1 * ‖z‖ := by rw [norm_smul]; gcongr
      _ < r := by simpa using hz
  have hB : ∫⁻ t in Ioc 0 (2 * π), ∫⁻ z, G (circleMap 0 1 t • z) ∂μ < ∞ := by
    rw [lintegral_lintegral_swap hj.aemeasurable]
    calc ∫⁻ z, ∫⁻ t in Ioc 0 (2 * π), G (circleMap 0 1 t • z) ∂volume ∂μ
        ≤ ∫⁻ z, (ball (0 : E) r).indicator
          (fun _ => ENNReal.ofReal (2 * π * (Real.log M - Real.log ‖f 0‖))) z ∂μ := by
          refine lintegral_mono fun z => ?_
          by_cases hz : z ∈ ball (0 : E) r
          · have h5 : ∀ t, G (circleMap 0 1 t • z) = logGap M (f (circleMap 0 1 t • z)) :=
              fun t => by
                have := hsm z hz _ (mem_closedBall_zero_iff.2 (hn t).le)
                rw [hG, indicator_of_mem this, hF, piecewise_eq_of_mem _ _ _ this]
            have h6 : AnalyticOnNhd ℂ (fun c : ℂ => f (c • z)) (closedBall 0 1) := by
              have ho : IsOpen ((fun c : ℂ => c • z) ⁻¹' ball 0 r) :=
                isOpen_ball.preimage (by fun_prop)
              have hd : DifferentiableOn ℂ (fun c : ℂ => f (c • z))
                  ((fun c : ℂ => c • z) ⁻¹' ball 0 r) :=
                hf.comp (by fun_prop) (mapsTo_preimage _ _)
              exact (hd.analyticOnNhd ho).mono fun c hc => hsm z hz c hc
            simp only [indicator_of_mem hz, h5]
            simpa using lintegral_logGap_circle_le h6 (by simpa using h0)
              (fun c hc => hM _ (hsm z hz c hc))
          · have h5 : ∀ t, G (circleMap 0 1 t • z) = 0 := fun t => by
              rw [hG, indicator_of_notMem]
              simpa [norm_smul, hn] using hz
            simp [h5]
      _ < ∞ := by
          rw [lintegral_indicator_const measurableSet_ball]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top
  rw [hA] at hB
  have hC : ∫⁻ z in ball 0 r, logGap M (F z) ∂μ < ∞ :=
    (ENNReal.lt_top_of_mul_ne_top_left hB.ne (ENNReal.ofReal_pos.2 h2).ne')
  have hFf : F =ᵐ[μ.restrict (ball 0 r)] f := piecewise_ae_eq_restrict measurableSet_ball
  have hne : ∀ᵐ z ∂(μ.restrict (ball 0 r)), f z ≠ 0 := by
    filter_upwards [ae_lt_top ((measurable_logGap M).comp hFm) hC.ne, hFf] with z hz hz' h
    simp [hz', logGap, h] at hz
  refine ⟨hne, ?_⟩
  have hmeas : AEStronglyMeasurable (fun z => Real.log ‖f z‖) (μ.restrict (ball 0 r)) := by
    have : AEMeasurable f (μ.restrict (ball 0 r)) := ⟨F, hFm, hFf.symm⟩
    exact (Real.measurable_log.comp_aemeasurable this.norm).aestronglyMeasurable
  have hc : IntegrableOn (fun _ : E => Real.log M) (ball 0 r) μ :=
    integrableOn_const measure_ball_lt_top.ne
  have hsub : IntegrableOn (fun z => Real.log M - Real.log ‖f z‖) (ball 0 r) μ := by
    refine ⟨aestronglyMeasurable_const.sub hmeas, ?_⟩
    refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hC
    filter_upwards [hne, hFf, ae_restrict_mem measurableSet_ball] with z hz hz' hzb
    rw [hz', logGap, if_neg hz, Real.enorm_eq_ofReal]
    exact sub_nonneg.2 (Real.log_le_log (norm_pos_iff.2 hz) (hM z hzb))
  exact (hc.sub hsub).congr (Eventually.of_forall fun z => by simp)
end GlobalTheory
