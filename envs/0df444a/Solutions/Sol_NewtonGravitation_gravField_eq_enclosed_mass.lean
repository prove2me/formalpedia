-- Prove2me | solution 1 for NewtonGravitation.gravField_eq_enclosed_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T18:13:21.95708+00:00
-- url     : https://prove2.me/submissions/22e76d16-fa17-47c4-a5da-21839a37fce1

import Definitions.Def_NewtonGravitation_Defs
import Theorems.Thm_NewtonGravitation_radial_shell_averaging_kernel
import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory NewtonGravitation

theorem solution (μ : Measure Space) [IsFiniteMeasure μ]
    (hμ : IsSphericallySymmetric μ) (x : Space)
    (hint : Integrable (fun y => -(G / ‖x - y‖ ^ 3) • (x - y)) μ) :
    gravField μ x = pointField (μ.real (Metric.ball 0 ‖x‖)) 0 x := by
  classical
  let ν : Measure ℝ := μ.map (fun y : Space => ‖y‖)
  let v : Space := (-(G / ‖x‖ ^ 3)) • x
  have haverage : gravField μ x =
      ∫ r : ℝ, (if r < ‖x‖ then v else 0) ∂ν :=
    NewtonGravitation.radial_shell_averaging_kernel μ hμ x hint
  have hindicator : (fun r : ℝ => if r < ‖x‖ then v else 0) =
      (Set.Iio ‖x‖).indicator (fun _ : ℝ => v) := by
    funext r
    by_cases hr : r < ‖x‖ <;> simp [Set.indicator, hr]
  have hintegral : (∫ r : ℝ, (if r < ‖x‖ then v else 0) ∂ν) =
      ν.real (Set.Iio ‖x‖) • v := by
    rw [hindicator]
    exact integral_indicator_const v measurableSet_Iio
  have hball : (fun y : Space => ‖y‖) ⁻¹' (Set.Iio ‖x‖) =
      Metric.ball (0 : Space) ‖x‖ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iio, Metric.mem_ball,
      dist_zero_right]
  have hmeasure : ν.real (Set.Iio ‖x‖) =
      μ.real (Metric.ball (0 : Space) ‖x‖) := by
    change (μ.map (fun y : Space => ‖y‖)).real (Set.Iio ‖x‖) =
      μ.real (Metric.ball (0 : Space) ‖x‖)
    have hmap : (μ.map (fun y : Space => ‖y‖)) (Set.Iio ‖x‖) =
        μ (Metric.ball (0 : Space) ‖x‖) := by
      rw [Measure.map_apply (measurable_norm) measurableSet_Iio]
      exact congrArg μ hball
    simpa [Measure.real] using congrArg ENNReal.toReal hmap
  calc
    gravField μ x = ∫ r : ℝ, (if r < ‖x‖ then v else 0) ∂ν := haverage
    _ = ν.real (Set.Iio ‖x‖) • v := hintegral
    _ = pointField (μ.real (Metric.ball 0 ‖x‖)) 0 x := by
      rw [hmeasure]
      simp only [v, pointField, sub_zero, smul_smul]
      congr 1
      ring
