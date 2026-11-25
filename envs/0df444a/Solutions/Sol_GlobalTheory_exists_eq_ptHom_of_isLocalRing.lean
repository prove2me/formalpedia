-- Prove2me | solution 1 for GlobalTheory.exists_eq_ptHom_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:38:46.749254+00:00
-- url     : https://prove2.me/submissions/dccdb9b0-d5a7-40e7-8901-3545d121539e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsEqPtHomOfIsLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) (A : Type) [CommRing A] [IsLocalRing A] (ρ : R →+* A) (x : Sp A ⟶ scheme W), x ≫ toSpec W = spMap ρ → ∃ (P : Fin 3 → A) (h : IsUnimodularSol (W.map ρ) P), x = ptHom W ρ P h := by
  intro R _ W A _ _ ρ x hx
  have key : ∀ i : Fin 3, x (IsLocalRing.closedPoint A) ∈ coordOpen W i →
      ∃ (P : Fin 3 → A) (h : IsUnimodularSol (W.map ρ) P), x = ptHom W ρ P h := by
    intro i hi
    have htop : x ⁻¹ᵁ coordOpen W i = ⊤ :=
      (IsLocalRing.closedPoint_mem_iff (R := A) (x ⁻¹ᵁ coordOpen W i)).mp hi
    have hr : Set.range x ⊆ Set.range (awayChart W i) := by
      rintro _ ⟨y, rfl⟩
      have hy : y ∈ x ⁻¹ᵁ coordOpen W i := htop.ge trivial
      rw [← opensRange_awayChart] at hy
      exact hy
    obtain ⟨g, hg⟩ := Spec.map_surjective (IsOpenImmersion.lift (awayChart W i) x hr)
    have hx' : x = Spec.map (CommRingCat.ofHom g.hom) ≫ awayChart W i := by
      rw [CommRingCat.ofHom_hom, hg, IsOpenImmersion.lift_fac]
    rw [SpecMap_awayChart] at hx'
    have hρ : g.hom.comp (awayConst W i) = ρ := by
      rw [hx', ptHom_toSpec] at hx
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective hx)
    subst hρ
    exact ⟨_, _, hx'⟩
  have h : x (IsLocalRing.closedPoint A) ∈ coordOpen W 1 ⊔ coordOpen W 2 := by
    rw [coordOpen_one_sup_coordOpen_two]
    trivial
  rcases h with h | h
  · exact key 1 h
  · exact key 2 h
end GlobalTheory
