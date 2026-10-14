-- Prove2me | solution 1 for NewtonGravitation.integrable_newtonKernel_inside_hollow
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T18:29:27.706129+00:00
-- url     : https://prove2.me/submissions/a288dcf6-8a58-461e-8075-47642b2e3452

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory NewtonGravitation

theorem solution (μ : Measure Space) [IsFiniteMeasure μ] (ρ : ℝ)
    (hρ : μ (Metric.ball (0 : Space) ρ) = 0)
    (x : Space) (hx : ‖x‖ < ρ) :
    Integrable (fun y => -(G / ‖x - y‖ ^ 3) • (x - y)) μ := by
  classical
  let δ : ℝ := ρ - ‖x‖
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  let f : Space → Space := fun y => -(G / ‖x - y‖ ^ 3) • (x - y)
  have hmeas : Measurable f := by
    have hs : Measurable (fun y : Space => x - y) :=
      measurable_const.sub measurable_id
    have hn : Measurable (fun y : Space => ‖x - y‖) := hs.norm
    exact (measurable_const.div (hn.pow_const 3)).neg.smul hs
  have hAE : ∀ᵐ y ∂μ, y ∉ Metric.ball (0 : Space) ρ := by
    apply ae_iff.mpr
    have hs : {y : Space | ¬ y ∉ Metric.ball (0 : Space) ρ} =
        Metric.ball (0 : Space) ρ := by
      ext y
      simp
    rwa [hs]
  have hbounded : ∀ᵐ y ∂μ, ‖f y‖ ≤ |G| / δ ^ 2 := by
    filter_upwards [hAE] with y hy
    have hyρ : ρ ≤ ‖y‖ := by
      have h : ¬ ‖y‖ < ρ := by
        simpa only [Metric.mem_ball, dist_zero_right] using hy
      exact le_of_not_gt h
    have htri : ‖y‖ ≤ ‖x - y‖ + ‖x‖ := by
      calc
        ‖y‖ = ‖(y - x) + x‖ := by simp
        _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
        _ = ‖x - y‖ + ‖x‖ := by rw [norm_sub_rev]
    have hdist : δ ≤ ‖x - y‖ := by
      dsimp [δ]
      linarith
    have hpos : 0 < ‖x - y‖ := hδ.trans_le hdist
    have hnz : ‖x - y‖ ≠ 0 := ne_of_gt hpos
    have hn : ‖f y‖ = |G| / ‖x - y‖ ^ 2 := by
      dsimp [f]
      rw [norm_smul, Real.norm_eq_abs]
      simp only [abs_neg, abs_div, abs_pow,
        abs_of_nonneg (norm_nonneg (x - y))]
      field_simp
    rw [hn]
    exact div_le_div_of_nonneg_left (abs_nonneg G) (pow_pos hδ 2)
      (pow_le_pow_left₀ hδ.le hdist 2)
  change Integrable f μ
  exact Integrable.of_bound hmeas.aestronglyMeasurable
    (|G| / δ ^ 2) hbounded
