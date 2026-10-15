-- Prove2me | solution 1 for HunterPDE.Sobolev.centered_ball_oscillation_le_potential
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-15T07:21:04.572135+00:00
-- url     : https://prove2.me/submissions/df157fe8-0cc3-4ef1-93af-d2003336799d

import Theorems.Thm_MeasureTheory_ofReal_abs_sub_le_segment_lintegral_gradient
import Theorems.Thm_MeasureTheory_lintegral_segment_ball_le_rieszPotential

open MeasureTheory
set_option autoImplicit false

theorem solution {n : ℕ} (hn : 0 < n) :
    ∃ C : NNReal, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 f → ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      (∫⁻ z in Metric.ball x r, ENNReal.ofReal |f x - f z|) ≤
        volume (Metric.ball x r) * (C : ENNReal) *
          (∫⁻ z in Metric.ball x r, ENNReal.ofReal ‖gradient f z‖ *
            ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ)))) := by
  obtain ⟨C, hC⟩ := MeasureTheory.lintegral_segment_ball_le_rieszPotential hn
  refine ⟨C, fun f hf x r hr => ?_⟩
  have hg : Measurable (fun z => ENNReal.ofReal ‖gradient f z‖) := by
    have hc := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp
      (hf.continuous_fderiv (by norm_num))
    exact ENNReal.measurable_ofReal.comp hc.norm.measurable
  calc
    (∫⁻ z in Metric.ball x r, ENNReal.ofReal |f x - f z|) ≤
        ∫⁻ z in Metric.ball x r, ENNReal.ofReal ‖z - x‖ *
          (∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ‖gradient f (x + t • (z - x))‖) :=
      lintegral_mono fun z => MeasureTheory.ofReal_abs_sub_le_segment_lintegral_gradient f hf x z
    _ ≤ _ := hC (fun z => ENNReal.ofReal ‖gradient f z‖) hg x r hr
