-- Prove2me | solution 1 for GlobalTheory.SS.ArcInf.exists_basicOpen_factor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:52.214644+00:00
-- url     : https://prove2.me/submissions/41a7aa42-e506-4006-b996-48e7d8a19aa6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AlgOverHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasicOpenFactorFieldPointAffineOpen
import Theorems.Thm_GlobalTheory_SS_ArcInf_algOverHom_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.ArcInf
namespace GlobalTheory.SS.ArcInf
theorem _root_.solution : ∀ (k : Type) [CommRing k] (G : Over (Sp k)) (A B F : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [Field F] [Algebra k F] (j : algOver k A ⟶ G) (φ : algOver k B ⟶ G) (δ : B →ₐ[k] F) (χ₀ : A →ₐ[k] F), IsOpenImmersion j.left → algOverHom δ ≫ φ = algOverHom χ₀ ≫ j → ∃ e : B, δ e ≠ 0 ∧ ∀ (B' : Type) [CommRing B'] [Algebra k B'] (ρ : B →ₐ[k] B'), IsUnit (ρ e) → ∃ χ : A →ₐ[k] B', algOverHom χ ≫ j = algOverHom ρ ≫ φ := by
  intro k _ G A B F _ _ _ _ _ _ j φ δ χ₀ hj h
  let U : (Spec (CommRingCat.of B)).Opens := φ.left ⁻¹ᵁ j.left.opensRange
  let p₀ : PrimeSpectrum F := ⟨⊥, Ideal.isPrime_bot⟩
  let p : PrimeSpectrum B := PrimeSpectrum.comap (δ : B →+* F) p₀
  have hl : (algOverHom δ).left ≫ φ.left = (algOverHom χ₀).left ≫ j.left := by
    have := congrArg (fun x => x.left) h
    simpa only [Over.comp_left] using this
  have hp : p ∈ (U : Set (Spec (CommRingCat.of B))) := by
    refine ⟨(algOverHom χ₀).left p₀, ?_⟩
    have := congrArg (fun x => x p₀) hl
    simp only [Scheme.Hom.comp_apply] at this
    exact this.symm
  obtain ⟨_, ⟨e, rfl⟩, he, heU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp U.isOpen
  refine ⟨e, fun h0 => he (show δ e ∈ (⊥ : Ideal F) from h0), ?_⟩
  intro B' _ _ ρ hρ
  have hr : Set.range ((algOverHom ρ).left ≫ φ.left) ⊆ Set.range j.left := by
    rintro _ ⟨q, rfl⟩
    have hq : PrimeSpectrum.comap (ρ : B →+* B') q ∈ PrimeSpectrum.basicOpen e := by
      intro hm
      exact q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ (show ρ e ∈ q.asIdeal from hm) hρ)
    rw [Scheme.Hom.comp_apply]
    exact heU hq
  have hf := IsOpenImmersion.lift_fac j.left ((algOverHom ρ).left ≫ φ.left) hr
  let ψ : algOver k B' ⟶ algOver k A :=
    Over.homMk (IsOpenImmersion.lift j.left ((algOverHom ρ).left ≫ φ.left) hr) (by
      rw [← Over.w j, ← Category.assoc, hf, Category.assoc, Over.w φ, Over.w (algOverHom ρ)])
  obtain ⟨χ, hχ⟩ := algOverHom_surjective ψ
  refine ⟨χ, ?_⟩
  rw [hχ]
  ext1
  exact hf
end GlobalTheory.SS.ArcInf
