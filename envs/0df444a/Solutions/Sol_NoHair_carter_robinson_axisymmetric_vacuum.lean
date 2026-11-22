-- Prove2me | solution 1 for NoHair.carter_robinson_axisymmetric_vacuum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T20:53:49.732863+00:00
-- url     : https://prove2.me/submissions/bbece1de-9e60-4d8b-8245-089019295121
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_israel_static_vacuum
import Theorems.Thm_NoHair_nonstatic_vacuum_weyl_comparison
import Theorems.Thm_NoHair_Weyl_vacuum_ernst_boundary_uniqueness

open scoped ContDiff Manifold
open NoHair Set

private theorem metric_eq_of_common_potentials {D : Set E4}
    {G₁ G₂ : E4 → Matrix (Fin 4) (Fin 4) ℝ} {u : Weyl.ErnstPotentials}
    (hc : Weyl.HaveCommonCharts D G₁ G₂ u u) : EqOn G₁ G₂ D := by
  obtain ⟨_, _, h₁, h₂, S, hSD, hDS, hcharts⟩ := hc
  refine Set.EqOn.of_subset_closure ?_ h₁ h₂ hSD hDS
  intro y hy
  obtain ⟨V, c, _, hyV, _, _, _, hcoeff⟩ := hcharts y hy
  obtain ⟨_, hleft, hright⟩ := hcoeff y hyV
  exact hleft.trans hright.symm

theorem solution {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (T : VecField M)
    (φ : ℝ → M → M) (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (hvac : ∀ x, F x = 0) (ρ : ℝ → M → M) (hρ : IsAxialSymmetry g F φ ρ) :
    ∃ m a : ℝ, IsKerrNewmanBlackHoleParams m a 0 ∧
      IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m a 0 := by
  by_cases hs : IsStaticOn g φ (domainOfOuterCommunications g T E.region)
  · obtain ⟨m, hm, hSchwarzschild⟩ := israel_static_vacuum g F T φ E h hvac hs
    exact ⟨m, 0, ⟨hm, by simpa using sq_nonneg m⟩, hSchwarzschild⟩
  · obtain ⟨m, a, hma, Ψ, u, v, hΨ, hu, hv, hb, hc⟩ :=
      nonstatic_vacuum_weyl_comparison g F T φ E h hvac ρ hρ hs
    have huv := Weyl.vacuum_ernst_boundary_uniqueness u v hu hv hb
    subst v
    refine ⟨m, a, hma, 0, Ψ, hΨ, ?_⟩
    intro y hy
    refine ⟨metric_eq_of_common_potentials hc hy, ?_⟩
    ext μ ν
    simp [pullbackCoeffs, hvac, kerrNewmanField, coordPartial, kerrNewmanPotential]
