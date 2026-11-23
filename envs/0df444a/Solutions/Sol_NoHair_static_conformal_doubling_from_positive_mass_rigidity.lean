-- Prove2me | solution 1 for NoHair.static_conformal_doubling_from_positive_mass_rigidity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T09:18:31.747828+00:00
-- url     : https://prove2.me/submissions/f673b32c-1f81-4764-ad29-7b407111e004
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_regular_static_slice_field_equations
import Theorems.Thm_NoHair_regular_static_horizon_surface_gravity
import Theorems.Thm_NoHair_riemannian_static_euclidean_double
import Theorems.Thm_NoHair_spacetime_chart_of_static_spatial_isometry
import Definitions.Def_NoHair_staticHorizonGeometry

open NoHair Set Filter
open scoped ContDiff Manifold Topology

noncomputable section

theorem solution {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M)
    (c : RegularStaticSliceCoordinates g φ D)
    (hrigidity : ThreeDimensionalZeroMassRigidity)
    (hpositiveEnd : ∃ R : ℝ, 0 < R ∧
      (∀ x : ADMPoint, R < ‖x‖ → ∀ v : ADMPoint, ‖v‖^2 / 4 ≤
        ∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric c.N c.h x i j * v i * v j) ∧
      ∀ (γ : ℝ → ADMPoint) (a b : ℝ), a ≤ b → ContDiff ℝ 1 γ →
        (∀ t ∈ Set.Icc a b, R < ‖γ t‖) →
        ‖γ b - γ a‖ ≤ 2 * ∫ t in a..b, Real.sqrt
          (∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric c.N c.h (γ t) i j * deriv γ t i * deriv γ t j))
    (hmass : Tendsto (staticADMFlux (staticPositiveMetric c.N c.h)) atTop (𝓝 0)) :
    let X := EuclideanSpace ℝ (Fin 3)
    ∃ (V : X → ℝ) (p : X),
      HasConformalVacuumExterior g D (fun x => 2 / (1 + V x)) ∧
      ContDiffOn ℝ 2 V ({0}ᶜ) ∧ (∀ x, x ≠ 0 → -1 < V x) ∧
      (∀ ε : ℝ, 0 < ε → ∃ L : ℝ, ∀ x, L < ‖x‖ → |V x - 1| ≤ ε) ∧
      p ≠ 0 ∧ V p = 0 ∧ (∀ x : X, x ≠ 0 → V x ≠ 0 →
        ∑ i : Fin 3, fderiv ℝ
          (fun y => (2 / (1 + V y))^2 * fderiv ℝ V y (EuclideanSpace.single i (1:ℝ)))
          x (EuclideanSpace.single i (1:ℝ)) = 0) := by
  have he := regular_static_slice_field_equations g φ D c
  have hz := regular_static_horizon_surface_gravity g φ D c he
  have s : RegularRiemannianStaticEnd c.Ω c.W c.N c.h :=
    ⟨c.openSlice,c.connectedSlice,c.compactComplement,c.hasBoundary,c.connectedBoundary,
      c.openExtension,c.extendsAcross,c.positiveSide,c.horizon,c.smoothLapse,c.smoothMetric,
      c.positiveMetric,c.falloff,he,hz⟩
  obtain ⟨V,p,chart,cs,hlow,hinf,hp,hn,hdiv⟩ :=
    riemannian_static_euclidean_double c.Ω c.W c.N c.h s hrigidity hpositiveEnd hmass
  exact ⟨V,p,spacetime_chart_of_static_spatial_isometry g φ D c V hlow chart,
    cs,hlow,hinf,hp,hn,hdiv⟩
