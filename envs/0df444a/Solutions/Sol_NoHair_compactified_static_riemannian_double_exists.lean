-- Prove2me | solution 1 for NoHair.compactified_static_riemannian_double_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:52:05.760674+00:00
-- url     : https://prove2.me/submissions/0f679bdd-cee9-4313-a966-5b18bf2e956e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_finite_static_horizon_reflection
import Theorems.Thm_NoHair_negative_static_end_smooth_point_chart
import Theorems.Thm_NoHair_complete_static_double_from_reflection_and_point_chart
import Theorems.Thm_NoHair_reflected_static_double_compact_truncations
import Theorems.Thm_NoHair_negative_static_end_inversion_bound
import Theorems.Thm_NoHair_static_conformal_halves_signed_lapse_equation
import Theorems.Thm_NoHair_static_conformal_halves_nondegenerate
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) (hpositiveEnd : ∃ R : ℝ, 0 < R ∧
      (∀ x : ADMPoint, R < ‖x‖ → ∀ v : ADMPoint, ‖v‖^2 / 4 ≤
        ∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h x i j * v i * v j) ∧
      ∀ (γ : ℝ → ADMPoint) (a b : ℝ), a ≤ b → ContDiff ℝ 1 γ →
        (∀ t ∈ Set.Icc a b, R < ‖γ t‖) →
        ‖γ b - γ a‖ ≤ 2 * ∫ t in a..b, Real.sqrt
          (∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h (γ t) i j * deriv γ t i * deriv γ t j))
    (hmass : Tendsto (staticADMFlux (staticPositiveMetric N h)) atTop (𝓝 0))
    (hflat : ∀ x ∈ closure Ω, spatialScalarCurvature h x = 0 ∧
      ∀ s : ℝ, 1 + s * N x ≠ 0 →
        spatialScalarCurvature (staticPositiveMetric (fun y => s*N y) h) x = 0)
    (hforms : ∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ frontier Ω, ∀ s : ℝ, s = 1 ∨ s = -1 →
      let k : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ := staticPositiveMetric (fun y => s*N y) h
      (∀ i j : Fin 3, k x i j = h x i j / 16) ∧
      staticLapseGradientSq N k x = (4*κ)^2 ∧
      ∀ v w : ADMPoint, fderiv ℝ N x v = 0 → fderiv ℝ N x w = 0 →
        (∑ i : Fin 3, ∑ j : Fin 3, staticSpatialHessian N k i j x * v i * w j) / (4*κ) =
          s*8*κ*(∑ i : Fin 3, ∑ j : Fin 3, k x i j * v i * w j)) :
    Nonempty (StaticConformalCompletion Ω N h) := by
  obtain ⟨d⟩ := finite_static_horizon_reflection Ω W N h c hflat hforms
    (static_conformal_halves_nondegenerate Ω W N h c) (static_conformal_halves_signed_lapse_equation Ω W N h c)
  obtain ⟨a⟩ := negative_static_end_smooth_point_chart Ω W N h c (negative_static_end_inversion_bound Ω W N h c)
  exact complete_static_double_from_reflection_and_point_chart Ω W N h c d a
    (reflected_static_double_compact_truncations Ω N h d) hpositiveEnd hmass
