-- Prove2me | solution 1 for NoHair.vacuum_kerr_exterior_iff_weyl_profile
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:01:16.89507+00:00
-- url     : https://prove2.me/submissions/d426888a-e9d4-4736-9c7c-2cf1b8b9fcfb

import Theorems.Thm_NoHair_Weyl_kerr_weyl_model
import Theorems.Thm_NoHair_Weyl_kerr_boundary_profile_estimates
import Theorems.Thm_NoHair_Weyl_comparison_of_common_boundary_profile
import Theorems.Thm_NoHair_Weyl_vacuum_ernst_boundary_uniqueness

open NoHair Set
open scoped ContDiff Manifold

theorem solution {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ,E4) ∞ M] (g F : BilinField M) (D : Set M) (m a : ℝ)
    (hm : IsKerrNewmanBlackHoleParams m a 0) (hF : ∀ x ∈ D, F x = 0) :
    IsKerrNewmanDOC g F D m a 0 ↔
      ∃ (Ψ : E4 → M) (u : Weyl.ErnstPotentials),
        IsDiffeoOnto Ψ (kerrNewmanDOC m a 0) D ∧ u.IsSolution ∧
        Weyl.IsWeylRepresentation m a (pullbackCoeffs g Ψ) u ∧
        Weyl.HasProfileEstimates u (Weyl.rodBoundaryProfile m (Real.sqrt (m^2-a^2)) (m*a)) := by
  let H := kerrNewmanDOC m a 0
  let K := Weyl.kerrErnst m a
  let b := Weyl.rodBoundaryProfile m (Real.sqrt (m^2-a^2)) (m*a)
  obtain ⟨hsol,hrep,hdense,hcharts⟩ := Weyl.kerr_weyl_model m a hm
  obtain ⟨hK,hmodel⟩ := Weyl.kerr_boundary_profile_estimates m a hm
  have hb (p : Weyl.OrbitPoint) : 0 < b.normSq p := (hmodel p).1
  constructor
  · rintro ⟨_,Ψ,hΨ,hgF⟩
    have eq : EqOn (pullbackCoeffs g Ψ) (kerrNewmanMetric m a 0) H := fun y hy => (hgF y hy).1
    refine ⟨Ψ,K,hΨ,hsol,?_,hK⟩
    refine ⟨hrep.quadratures,hrep.continuous.congr eq,?_⟩
    intro V c hc y hy
    exact (eq (hc.off_axis hy).1).trans (hrep.coefficients V c hc y hy)
  · rintro ⟨Ψ,u,hΨ,hu,hrepu,hprofile⟩
    have hbounds := (Weyl.comparison_of_common_boundary_profile u K b hb hprofile hK).1
    have heq : u = K := Weyl.vacuum_ernst_boundary_uniqueness u K hu hsol hbounds
    subst u
    have GKeq : EqOn (pullbackCoeffs g Ψ) (kerrNewmanMetric m a 0) H := by
      apply Set.EqOn.of_subset_closure _ hrepu.continuous hrep.continuous (fun _ hy => hy.1) hdense
      intro y hy
      obtain ⟨V,c,hyV,hc⟩ := hcharts y hy
      exact (hrepu.coefficients V c hc y hyV).trans (hrep.coefficients V c hc y hyV).symm
    refine ⟨0,Ψ,hΨ,?_⟩
    intro y hy
    obtain ⟨_,him,_,_,_,_,_⟩ := hΨ
    have hz := hF (Ψ y) (him hy)
    refine ⟨GKeq hy,?_⟩
    ext i j
    simp [pullbackCoeffs,hz,kerrNewmanField,coordPartial,kerrNewmanPotential]
