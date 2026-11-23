-- Prove2me | solution 1 for NoHair.analytic_static_timelike_end_harmonic_double
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:34:01.893888+00:00
-- url     : https://prove2.me/submissions/38a3fe3e-5637-4949-835c-906dfc2b0fc3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_analytic_static_timelike_end_regular_slice
import Theorems.Thm_NoHair_regular_static_vacuum_euclidean_double

open NoHair Set InnerProductSpace
open scoped ContDiff Manifold

theorem solution {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] [IsManifold 𝓘(ℝ, E4) ω M]
    (g F : BilinField M) (T : VecField M)
    (φ : ℝ → M → M) (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (htime : ∀ x ∈ E.region, g x (flowGenerator φ x) (flowGenerator φ x) < 0)
    (hvac : ∀ x, F x = 0) (hanalytic : IsAnalyticBilinField g)
    (hnondeg : IsNondegenerateHorizon g F (futureEventHorizon g T E.region)
      (domainOfOuterCommunications g T E.region))
    (hstatic : IsStaticOn g φ (domainOfOuterCommunications g T E.region)) :
    ∃ (U : EuclideanSpace ℝ (Fin 3) → ℝ) (p : EuclideanSpace ℝ (Fin 3)),
      HasConformalVacuumExterior g (domainOfOuterCommunications g T E.region) U ∧
      HarmonicOnNhd U ({0}ᶜ) ∧ (∀ x, x ≠ 0 → 0 ≤ U x) ∧
      (∀ ε : ℝ, 0 < ε → ∃ L : ℝ, ∀ x, L < ‖x‖ → |U x - 1| ≤ ε) ∧ p ≠ 0 ∧ U p = 2 := by
  apply regular_static_vacuum_euclidean_double g φ _
  exact analytic_static_timelike_end_regular_slice g F T φ E h htime hvac hanalytic hnondeg hstatic
