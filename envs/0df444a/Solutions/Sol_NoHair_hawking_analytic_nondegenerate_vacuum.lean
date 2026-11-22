-- Prove2me | solution 1 for NoHair.hawking_analytic_nondegenerate_vacuum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T21:00:16.891318+00:00
-- url     : https://prove2.me/submissions/8f6cec3c-e9e5-499c-943b-5b80e539c557
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_israel_static_vacuum
import Theorems.Thm_NoHair_analytic_nonstatic_exterior_weyl_comparison
import Theorems.Thm_NoHair_Weyl_vacuum_ernst_boundary_uniqueness

open scoped ContDiff Manifold
open NoHair Set

private theorem metric_eq_on_exterior {D : Set E4}
    {G K : E4 → Matrix (Fin 4) (Fin 4) ℝ} {u v : Weyl.ErnstPotentials}
    (hc : Weyl.HaveCommonCharts D G K u v) (huv : u = v) : EqOn G K D := by
  subst v
  obtain ⟨_, _, hG, hK, S, hSD, hdense, hcharts⟩ := hc
  refine Set.EqOn.of_subset_closure ?_ hG hK hSD hdense
  intro y hy
  obtain ⟨V, c, _, hyV, _, _, _, hcoeff⟩ := hcharts y hy
  obtain ⟨_, hGchart, hKchart⟩ := hcoeff y hyV
  exact hGchart.trans hKchart.symm

theorem solution {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] [IsManifold 𝓘(ℝ, E4) ω M]
    (g F : BilinField M) (T : VecField M) (φ : ℝ → M → M)
    (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (hvac : ∀ x, F x = 0) (hanalytic : IsAnalyticBilinField g)
    (hnondeg : IsNondegenerateHorizon g F (futureEventHorizon g T E.region)
      (domainOfOuterCommunications g T E.region)) :
    ∃ m a : ℝ, IsKerrNewmanBlackHoleParams m a 0 ∧
      IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m a 0 := by
  by_cases hs : IsStaticOn g φ (domainOfOuterCommunications g T E.region)
  · obtain ⟨m, hm, hSchwarzschild⟩ := israel_static_vacuum g F T φ E h hvac hs
    exact ⟨m, 0, ⟨hm, by simpa using sq_nonneg m⟩, hSchwarzschild⟩
  · obtain ⟨m, a, hparams, Ψ, u, v, hΨ, hu, hv, hbounds, hcharts⟩ :=
      analytic_nonstatic_exterior_weyl_comparison g F T φ E h hvac hanalytic hnondeg hs
    have huv := Weyl.vacuum_ernst_boundary_uniqueness u v hu hv hbounds
    have hmetric := metric_eq_on_exterior hcharts huv
    refine ⟨m, a, hparams, 0, Ψ, hΨ, ?_⟩
    intro y hy
    refine ⟨hmetric hy, ?_⟩
    ext μ ν
    simp [pullbackCoeffs, hvac, kerrNewmanField, coordPartial, kerrNewmanPotential]
