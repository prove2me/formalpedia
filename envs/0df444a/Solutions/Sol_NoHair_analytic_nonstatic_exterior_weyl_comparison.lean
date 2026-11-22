-- Prove2me | solution 1 for NoHair.analytic_nonstatic_exterior_weyl_comparison
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T21:35:48.643223+00:00
-- url     : https://prove2.me/submissions/9b88886a-f3d2-4122-8b28-c84f914864ec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_analytic_nonstatic_exterior_axis_data
import Theorems.Thm_NoHair_Weyl_kerr_parameters_from_rod_and_spin
import Theorems.Thm_NoHair_Weyl_kerr_ernst_axis_data
import Theorems.Thm_NoHair_Weyl_kerr_weyl_model

open NoHair
open scoped ContDiff Manifold

theorem solution {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] [IsManifold 𝓘(ℝ, E4) ω M]
    (g F : BilinField M) (T : VecField M) (φ : ℝ → M → M)
    (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (hvac : ∀ x, F x = 0) (hanalytic : IsAnalyticBilinField g)
    (hnondeg : IsNondegenerateHorizon g F (futureEventHorizon g T E.region)
      (domainOfOuterCommunications g T E.region))
    (hns : ¬ IsStaticOn g φ (domainOfOuterCommunications g T E.region)) :
    ∃ m a : ℝ, IsKerrNewmanBlackHoleParams m a 0 ∧
      ∃ (Ψ : E4 → M) (u v : Weyl.ErnstPotentials),
        IsDiffeoOnto Ψ (kerrNewmanDOC m a 0) (domainOfOuterCommunications g T E.region) ∧
        u.IsSolution ∧ v.IsSolution ∧ Weyl.HasComparisonBounds u v ∧
        Weyl.HaveCommonCharts (kerrNewmanDOC m a 0) (pullbackCoeffs g Ψ)
          (kerrNewmanMetric m a 0) u v := by
  obtain ⟨ℓ, J, hℓ, hn, hdata⟩ :=
    analytic_nonstatic_exterior_axis_data g F T φ E h hvac hanalytic hnondeg hns
  obtain ⟨⟨m, a⟩, ⟨hm, hrod, hspin⟩, _⟩ :=
    Weyl.kerr_parameters_from_rod_and_spin ℓ J hℓ hn
  change 0 < m at hm
  change m ^ 2 - a ^ 2 = ℓ ^ 2 at hrod
  change m * a = J at hspin
  obtain ⟨Ψ, u, hΨ, hu, _, hbounds, hrepu⟩ := hdata m a hm hrod hspin
  have hparam : IsKerrNewmanBlackHoleParams m a 0 := ⟨hm, by nlinarith [sq_nonneg ℓ]⟩
  obtain ⟨hv, hrepv, hdense, hcharts⟩ := Weyl.kerr_weyl_model m a hparam
  have haxis := Weyl.kerr_ernst_axis_data m a ℓ hm hℓ hrod
  rw [hspin] at haxis
  refine ⟨m, a, hparam, Ψ, u, Weyl.kerrErnst m a, hΨ, hu, hv, hbounds haxis,
    hrepu.quadratures, hrepv.quadratures, hrepu.continuous, hrepv.continuous,
    Weyl.offAxisExterior m a, fun _ hy => hy.1, hdense, ?_⟩
  intro y hy
  obtain ⟨V, c, hyV, hc⟩ := hcharts y hy
  refine ⟨V, c, hc.source_open, hyV, hc.off_axis, hc.image_open, hc.diffeo, ?_⟩
  intro x hx
  exact ⟨hc.pos x hx, hrepu.coefficients V c hc x hx, hrepv.coefficients V c hc x hx⟩
