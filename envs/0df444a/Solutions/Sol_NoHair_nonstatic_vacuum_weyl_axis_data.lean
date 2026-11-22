-- Prove2me | solution 1 for NoHair.nonstatic_vacuum_weyl_axis_data
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:48:04.451496+00:00
-- url     : https://prove2.me/submissions/50a0f2d0-d2ad-4b5b-91c5-c07518192b12
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_nonstatic_vacuum_weyl_boundary_profile
import Theorems.Thm_NoHair_Weyl_kerr_boundary_profile_estimates
import Theorems.Thm_NoHair_Weyl_comparison_of_common_boundary_profile
import Theorems.Thm_NoHair_Weyl_kerr_ernst_axis_data

open scoped ContDiff Manifold

open NoHair

theorem solution {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (T : VecField M)
    (φ : ℝ → M → M) (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (hvac : ∀ x, F x = 0) (ρ : ℝ → M → M) (hρ : IsAxialSymmetry g F φ ρ)
    (hns : ¬ IsStaticOn g φ (domainOfOuterCommunications g T E.region)) :
    ∃ ℓ J : ℝ, 0 ≤ ℓ ∧ (0 < ℓ ∨ J ≠ 0) ∧
      ∀ m a : ℝ, 0 < m → m^2-a^2 = ℓ^2 → m*a = J →
        ∃ (Ψ : E4 → M) (u : Weyl.ErnstPotentials),
          IsDiffeoOnto Ψ (kerrNewmanDOC m a 0) (domainOfOuterCommunications g T E.region) ∧
          u.IsSolution ∧ Weyl.HasAxisData u ℓ J ∧
          (Weyl.HasAxisData (Weyl.kerrErnst m a) ℓ J →
            Weyl.HasComparisonBounds u (Weyl.kerrErnst m a)) ∧
          Weyl.IsWeylRepresentation m a (pullbackCoeffs g Ψ) u := by
  obtain ⟨ℓ,J,hℓ,hn,space⟩ :=
    nonstatic_vacuum_weyl_boundary_profile g F T φ E h hvac ρ hρ hns
  refine ⟨ℓ,J,hℓ,hn,?_⟩
  intro m a hm hlen hJ
  obtain ⟨Ψ,u,hΨ,hu,hprofile,hlimit,hrep⟩ := space m a hm hlen hJ
  have hma : IsKerrNewmanBlackHoleParams m a 0 := ⟨hm,by nlinarith [sq_nonneg ℓ]⟩
  have hroot : Real.sqrt (m^2-a^2)=ℓ := by rw [hlen,Real.sqrt_sq hℓ]
  have hk:=Weyl.kerr_boundary_profile_estimates m a hma
  dsimp only at hk
  rw [hroot,hJ] at hk
  have comparison := Weyl.comparison_of_common_boundary_profile u (Weyl.kerrErnst m a)
    (Weyl.rodBoundaryProfile m ℓ J) (fun p => (hk.2 p).1) hprofile hk.1
  have haxis := Weyl.kerr_ernst_axis_data m a ℓ hm hℓ hlen
  rw [hJ] at haxis
  exact ⟨Ψ,u,hΨ,hu,comparison.2 ℓ J haxis hlimit,fun _ => comparison.1,hrep⟩
