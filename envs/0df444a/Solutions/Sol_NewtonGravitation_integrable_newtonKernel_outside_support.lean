-- Prove2me | solution 1 for NewtonGravitation.integrable_newtonKernel_outside_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T18:13:27.021924+00:00
-- url     : https://prove2.me/submissions/c4c9d3da-8c9f-47cd-a11b-0f19cfb72fa9

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory NewtonGravitation

theorem solution (μ : Measure Space) [IsFiniteMeasure μ] (R : ℝ)
    (hR : μ (Metric.closedBall (0 : Space) R)ᶜ = 0)
    (x : Space) (hx : R < ‖x‖) :
    Integrable (fun y => -(G / ‖x - y‖ ^ 3) • (x - y)) μ := by
  classical
  let K : Set Space := Metric.closedBall 0 R
  let f : Space → Space := fun y => -(G / ‖x - y‖ ^ 3) • (x - y)
  have hcompact : IsCompact K := isCompact_closedBall (0 : Space) R
  have hcont : ContinuousOn f K := by
    intro y hy
    have hyR : ‖y‖ ≤ R := by
      simpa [K, Metric.mem_closedBall, dist_zero_right] using hy
    have hne : x - y ≠ 0 := by
      intro h
      have heq : x = y := sub_eq_zero.mp h
      rw [heq] at hx
      exact (not_lt_of_ge hyR) hx
    have hden : ‖x - y‖ ^ 3 ≠ 0 :=
      pow_ne_zero 3 (norm_ne_zero_iff.mpr hne)
    have hsub : Continuous (fun z : Space => x - z) :=
      continuous_const.sub continuous_id
    have hnorm : Continuous (fun z : Space => ‖x - z‖ ^ 3) :=
      (continuous_norm.comp hsub).pow 3
    have hscalar : ContinuousAt (fun z : Space => -(G / ‖x - z‖ ^ 3)) y :=
      (continuousAt_const.div hnorm.continuousAt hden).neg
    exact (hscalar.smul hsub.continuousAt).continuousWithinAt
  have hIntegrableOn : IntegrableOn f K μ :=
    hcont.integrableOn_compact hcompact
  have hAE : ∀ᵐ y ∂μ, y ∈ K := by
    apply ae_iff.mpr
    change μ Kᶜ = 0 at hR
    exact hR
  have hRestrict : μ.restrict K = μ :=
    Measure.restrict_eq_self_of_ae_mem hAE
  change Integrable f μ
  rw [← hRestrict]
  exact hIntegrableOn
