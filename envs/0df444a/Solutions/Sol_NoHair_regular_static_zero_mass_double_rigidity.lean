-- Prove2me | solution 1 for NoHair.regular_static_zero_mass_double_rigidity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T08:07:30.365073+00:00
-- url     : https://prove2.me/submissions/ccb248ff-b1c5-439b-b0fe-6385a00ec6a0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_positive_static_end_length_lower_bound
import Theorems.Thm_NoHair_scalar_flat_zero_mass_rigidity_three
import Theorems.Thm_NoHair_static_conformal_doubling_from_positive_mass_rigidity

open NoHair Set Filter InnerProductSpace
open scoped Manifold ContDiff Topology

theorem solution {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M)
    (c : RegularStaticSliceCoordinates g φ D)
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
  exact static_conformal_doubling_from_positive_mass_rigidity g φ D c
    scalar_flat_zero_mass_rigidity_three (positive_static_end_length_lower_bound g φ D c) hmass
