-- Prove2me | solution 1 for NoHair.regular_static_lapse_positive_monopole
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:20:07.111025+00:00
-- url     : https://prove2.me/submissions/e950a2b3-59f2-44aa-bbd9-eda8a55a5827

import Theorems.Thm_NoHair_regular_static_lapse_euclidean_poisson_source
import Theorems.Thm_NoHair_inverse_radius_limit_of_decaying_poisson_field
open NoHair MeasureTheory Metric Set Filter Laplacian
open scoped ContDiff Topology

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∃ μ : ℝ, 0 < μ ∧ HasStaticLapseMonopole N μ := by
  obtain ⟨u,hu,he,h0,hi,hd,hpos⟩ := regular_static_lapse_euclidean_poisson_source Ω W N h c
  have hv : 0 < volume.real (ball (0:ADMPoint) 1) :=
    ENNReal.toReal_pos (measure_ball_pos _ _ zero_lt_one).ne' (measure_ball_lt_top ..).ne
  refine ⟨_,div_pos hpos (by positivity : 0<3*volume.real (ball (0:ADMPoint) 1)),?_⟩
  exact (inverse_radius_limit_of_decaying_poisson_field u hu h0 hi hd).congr'
    (he.mono (fun x hx => congrArg (‖x‖ * ·) hx))
