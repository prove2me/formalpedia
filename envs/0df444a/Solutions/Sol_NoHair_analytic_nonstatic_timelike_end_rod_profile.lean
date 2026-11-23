-- Prove2me | solution 1 for NoHair.analytic_nonstatic_timelike_end_rod_profile
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:34:15.467893+00:00
-- url     : https://prove2.me/submissions/ee3193c1-3371-4ac0-b216-38c4bb30cbf3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_analytic_nonstatic_timelike_end_regular_rod_data
import Theorems.Thm_NoHair_Weyl_profile_of_regular_rod_boundary_data

open NoHair Set
open scoped ContDiff Manifold

theorem solution {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] [IsManifold 𝓘(ℝ, E4) ω M]
    (g F : BilinField M) (T : VecField M)
    (φ : ℝ → M → M) (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (htime : ∀ x ∈ E.region, g x (flowGenerator φ x) (flowGenerator φ x) < 0)
    (hvac : ∀ x, F x = 0) (hanalytic : IsAnalyticBilinField g)
    (hnondeg : IsNondegenerateHorizon g F (futureEventHorizon g T E.region)
      (domainOfOuterCommunications g T E.region))
    (hns : ¬ IsStaticOn g φ (domainOfOuterCommunications g T E.region)) :
    ∃ ℓ J : ℝ, 0 ≤ ℓ ∧ (0 < ℓ ∨ J ≠ 0) ∧
      ∀ m a : ℝ, 0 < m → m^2-a^2 = ℓ^2 → m*a = J →
        ∃ (Ψ : E4 → M) (u : Weyl.ErnstPotentials),
          IsDiffeoOnto Ψ (kerrNewmanDOC m a 0) (domainOfOuterCommunications g T E.region) ∧
          u.IsSolution ∧ Weyl.IsWeylRepresentation m a (pullbackCoeffs g Ψ) u ∧
          Weyl.HasProfileEstimates u (Weyl.rodBoundaryProfile m ℓ J) := by
  obtain ⟨ℓ,J,hℓ,hJ,hdata⟩ :=
    analytic_nonstatic_timelike_end_regular_rod_data g F T φ E h htime hvac hanalytic hnondeg hns
  refine ⟨ℓ,J,hℓ,hJ,?_⟩
  intro m a hm hma hspin
  obtain ⟨Ψ,u,hΨ,hu,hrep,⟨bd⟩⟩ := hdata m a hm hma hspin
  exact ⟨Ψ,u,hΨ,hu,hrep,Weyl.profile_of_regular_rod_boundary_data u m ℓ J hm hℓ bd⟩
