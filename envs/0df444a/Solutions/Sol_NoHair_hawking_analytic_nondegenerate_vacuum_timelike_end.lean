-- Prove2me | solution 1 for NoHair.hawking_analytic_nondegenerate_vacuum_timelike_end
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:01:16.988214+00:00
-- url     : https://prove2.me/submissions/47d1b0e5-c823-44bc-b097-e3000c6befaf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_analytic_static_timelike_end_harmonic_double
import Theorems.Thm_NoHair_analytic_nonstatic_timelike_end_rod_profile
import Theorems.Thm_NoHair_schwarzschild_of_positive_harmonic_double
import Theorems.Thm_NoHair_Weyl_kerr_parameters_from_rod_and_spin
import Theorems.Thm_NoHair_vacuum_kerr_exterior_iff_weyl_profile

open NoHair Set
open scoped ContDiff Manifold

theorem solution {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] [IsManifold 𝓘(ℝ, E4) ω M]
    (g F : BilinField M) (T : VecField M)
    (φ : ℝ → M → M) (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (htime : ∀ x ∈ E.region, g x (flowGenerator φ x) (flowGenerator φ x) < 0)
    (hvac : ∀ x, F x = 0) (hanalytic : IsAnalyticBilinField g)
    (hnondeg : IsNondegenerateHorizon g F (futureEventHorizon g T E.region)
      (domainOfOuterCommunications g T E.region)) :
    ∃ m a : ℝ, IsKerrNewmanBlackHoleParams m a 0 ∧
      IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m a 0 := by
  let D := domainOfOuterCommunications g T E.region
  have hF : ∀ x ∈ D, F x = 0 := fun x _ => hvac x
  by_cases hs : IsStaticOn g φ D
  · obtain ⟨U,p,hchart,hh,hpos,hfar,hp,hlevel⟩ :=
      analytic_static_timelike_end_harmonic_double g F T φ E h htime hvac hanalytic hnondeg hs
    obtain ⟨hm,hiso⟩ := schwarzschild_of_positive_harmonic_double g F D hF U hchart hh hpos hfar p hp hlevel
    exact ⟨2*‖p‖,0,⟨hm,by simpa using sq_nonneg (2*‖p‖)⟩,hiso⟩
  · obtain ⟨ℓ,J,hℓ,hn,hdata⟩ :=
      analytic_nonstatic_timelike_end_rod_profile g F T φ E h htime hvac hanalytic hnondeg hs
    obtain ⟨⟨m,a⟩,⟨hm,hrod,hspin⟩,_⟩ := Weyl.kerr_parameters_from_rod_and_spin ℓ J hℓ hn
    change 0 < m at hm
    change m^2-a^2 = ℓ^2 at hrod
    change m*a = J at hspin
    have hparams : IsKerrNewmanBlackHoleParams m a 0 := ⟨hm,by nlinarith [sq_nonneg ℓ]⟩
    obtain ⟨Ψ,u,hΨ,hu,hrep,hprofile⟩ := hdata m a hm hrod hspin
    refine ⟨m,a,hparams,(vacuum_kerr_exterior_iff_weyl_profile g F D m a hparams hF).2
      ⟨Ψ,u,hΨ,hu,hrep,?_⟩⟩
    rwa [hrod,Real.sqrt_sq hℓ,hspin]
