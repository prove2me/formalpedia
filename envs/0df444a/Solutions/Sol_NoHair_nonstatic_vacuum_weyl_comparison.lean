-- Prove2me | solution 1 for NoHair.nonstatic_vacuum_weyl_comparison
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T21:25:08.417691+00:00
-- url     : https://prove2.me/submissions/fc1ea530-df76-4da6-9b1e-2a3c44153cca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_Weyl_kerr_parameters_from_rod_and_spin
import Theorems.Thm_NoHair_Weyl_kerr_ernst_axis_data
import Theorems.Thm_NoHair_Weyl_kerr_weyl_model
import Theorems.Thm_NoHair_nonstatic_vacuum_weyl_axis_data

open scoped ContDiff Manifold
open NoHair

theorem solution {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (T : VecField M)
    (φ : ℝ → M → M) (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (hvac : ∀ x, F x = 0) (ρ : ℝ → M → M) (hρ : IsAxialSymmetry g F φ ρ)
    (hns : ¬ IsStaticOn g φ (domainOfOuterCommunications g T E.region)) :
    ∃ m a : ℝ, IsKerrNewmanBlackHoleParams m a 0 ∧
      ∃ (Ψ : E4 → M) (u v : Weyl.ErnstPotentials),
        IsDiffeoOnto Ψ (kerrNewmanDOC m a 0) (domainOfOuterCommunications g T E.region) ∧
        u.IsSolution ∧ v.IsSolution ∧ Weyl.HasComparisonBounds u v ∧
        Weyl.HaveCommonCharts (kerrNewmanDOC m a 0) (pullbackCoeffs g Ψ)
          (kerrNewmanMetric m a 0) u v := by
  obtain ⟨ℓ,J,hℓ,hn,space⟩ := nonstatic_vacuum_weyl_axis_data g F T φ E h hvac ρ hρ hns
  obtain ⟨⟨m,a⟩,⟨hm,hlen,hJ⟩,_⟩ := Weyl.kerr_parameters_from_rod_and_spin ℓ J hℓ hn
  change 0 < m at hm
  change m^2-a^2 = ℓ^2 at hlen
  change m*a = J at hJ
  have hma : IsKerrNewmanBlackHoleParams m a 0 := ⟨hm, by nlinarith [sq_nonneg ℓ]⟩
  obtain ⟨Ψ,u,hΨ,hu,_,compare,rep⟩ := space m a hm hlen hJ
  have haxis := Weyl.kerr_ernst_axis_data m a ℓ hm hℓ hlen
  rw [hJ] at haxis
  obtain ⟨hv,kerrRep,dense,cover⟩ := Weyl.kerr_weyl_model m a hma
  refine ⟨m,a,hma,Ψ,u,Weyl.kerrErnst m a,hΨ,hu,hv,compare haxis,
    rep.quadratures,kerrRep.quadratures,rep.continuous,kerrRep.continuous,
    Weyl.offAxisExterior m a,fun _ hy => hy.1,dense,?_⟩
  intro y hy
  obtain ⟨V,c,hyV,hc⟩ := cover y hy
  exact ⟨V,c,hc.source_open,hyV,hc.off_axis,hc.image_open,hc.diffeo,
    fun x hx => ⟨hc.pos x hx,rep.coefficients V c hc x hx,kerrRep.coefficients V c hc x hx⟩⟩
