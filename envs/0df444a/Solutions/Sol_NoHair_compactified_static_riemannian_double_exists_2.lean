-- Prove2me | solution 2 for NoHair.compactified_static_riemannian_double_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:54:48.820895+00:00
-- url     : https://prove2.me/submissions/d1740348-3e73-4a01-a1fe-fd5d473503b6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_regular_static_lapse_positive_monopole
import Theorems.Thm_NoHair_static_negative_sheet_pole_from_lapse_monopole
import Theorems.Thm_NoHair_static_riemannian_gluing_with_continuous_pole

open NoHair Set Filter
open scoped ContDiff Topology

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
  obtain ⟨μ,hμ,hasμ⟩ := regular_static_lapse_positive_monopole Ω W N h c
  have hpole := static_negative_sheet_pole_from_lapse_monopole Ω W N h c μ hasμ
  exact static_riemannian_gluing_with_continuous_pole Ω W N h c hpositiveEnd hmass hflat hforms μ hμ hpole
