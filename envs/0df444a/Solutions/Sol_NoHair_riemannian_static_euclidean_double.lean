-- Prove2me | solution 1 for NoHair.riemannian_static_euclidean_double
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:09:22.598444+00:00
-- url     : https://prove2.me/submissions/affc5220-5870-45f8-8038-7639e1175f56
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_compactified_static_riemannian_double_exists
import Theorems.Thm_NoHair_euclidean_chart_from_static_completion
import Theorems.Thm_NoHair_static_conformal_halves_scalar_flat
import Theorems.Thm_NoHair_static_conformal_horizon_matching_forms
import Definitions.Def_NoHair_staticConformalCompletion

open NoHair Set Filter
open scoped ContDiff Manifold Topology

noncomputable section

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) (hrigidity : ThreeDimensionalZeroMassRigidity)
    (hpositiveEnd : ∃ R : ℝ, 0 < R ∧
      (∀ x : ADMPoint, R < ‖x‖ → ∀ v : ADMPoint, ‖v‖^2 / 4 ≤
        ∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h x i j * v i * v j) ∧
      ∀ (γ : ℝ → ADMPoint) (a b : ℝ), a ≤ b → ContDiff ℝ 1 γ →
        (∀ t ∈ Set.Icc a b, R < ‖γ t‖) →
        ‖γ b - γ a‖ ≤ 2 * ∫ t in a..b, Real.sqrt
          (∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h (γ t) i j * deriv γ t i * deriv γ t j))
    (hmass : Tendsto (staticADMFlux (staticPositiveMetric N h)) atTop (𝓝 0)) :
    ∃ (V : ADMPoint → ℝ) (p : ADMPoint), HasStaticSpatialDoubleChart Ω N h V ∧
      ContDiffOn ℝ 2 V ({0}ᶜ) ∧ (∀ x, x ≠ 0 → -1 < V x) ∧
      (∀ ε : ℝ, 0 < ε → ∃ L : ℝ, ∀ x, L < ‖x‖ → |V x - 1| ≤ ε) ∧
      p ≠ 0 ∧ V p = 0 ∧ (∀ x : ADMPoint, x ≠ 0 → V x ≠ 0 →
        ∑ i : Fin 3, fderiv ℝ
          (fun y => (2 / (1 + V y))^2 * fderiv ℝ V y (EuclideanSpace.single i (1:ℝ)))
          x (EuclideanSpace.single i (1:ℝ)) = 0) := by
  obtain ⟨d⟩ := compactified_static_riemannian_double_exists Ω W N h c hpositiveEnd hmass
    (static_conformal_halves_scalar_flat Ω W N h c)
    (static_conformal_horizon_matching_forms Ω W N h c)
  exact euclidean_chart_from_static_completion Ω N h d hrigidity
