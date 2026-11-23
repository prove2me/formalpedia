-- Prove2me | solution 1 for NoHair.inverse_radius_limit_of_decaying_poisson_field
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:20:03.558566+00:00
-- url     : https://prove2.me/submissions/fb29e10e-10de-4969-9cd5-bcd5e6f2c658

import Theorems.Thm_NoHair_rescaled_ball_mass_recovers_total_source
import Theorems.Thm_NoHair_spherical_mean_lapse_source_identity
open NoHair MeasureTheory Metric Set Filter Laplacian
open scoped ContDiff Topology

theorem solution (u : ADMPoint → ℝ) (hu : ContDiff ℝ 2 u)
    (h0 : Tendsto u (cocompact ADMPoint) (𝓝 0))
    (hi : Integrable (fun z => -(Δ u) z))
    (hd : ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ z : ADMPoint, R < ‖z‖ → |(Δ u) z| ≤ C/‖z‖^4) :
    Tendsto (fun x : ADMPoint => ‖x‖*u x) (cocompact ADMPoint)
      (𝓝 ((∫ z, -(Δ u) z)/(3*volume.real (ball (0:ADMPoint) 1)))) := by
  have hn : ∃ R C : ℝ, 0<R ∧ 0<C ∧ ∀ z : ADMPoint, R<‖z‖ → |-(Δ u) z| ≤ C/‖z‖^4 := by
    simpa only [abs_neg] using hd
  have hb := rescaled_ball_mass_recovers_total_source (fun z => -(Δ u) z) hi hn
  have hm := spherical_mean_lapse_source_identity u hu h0 hi hd
  have hv : 0 < volume.real (ball (0:ADMPoint) 1) :=
    ENNReal.toReal_pos (measure_ball_pos _ _ zero_lt_one).ne' (measure_ball_lt_top ..).ne
  apply (hb.div_const (3*volume.real (ball (0:ADMPoint) 1))).congr'
  filter_upwards [hm] with x he
  apply (div_eq_iff (by positivity : (3*volume.real (ball (0:ADMPoint) 1))≠0)).2
  rw [← he]
  ring
