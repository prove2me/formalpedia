-- Prove2me | solution 1 for GlobalTheory.SS.exists_fieldOfValues
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:42:48.915509+00:00
-- url     : https://prove2.me/submissions/937780fa-e560-424b-b3dd-1feb1ad453ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFieldOfValues
import Theorems.Thm_GlobalTheory_SS_residue_embedding_unique
import Theorems.Thm_GlobalTheory_SS_essFiniteType_residueField_of_locallyOfFiniteType

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
open GlobalTheory GlobalTheory.SS
namespace GlobalTheory.SS
theorem _root_.solution : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (x : Sp Ω ⟶ X), ∃ E : Subfield Ω, (∀ τ τ' : Ω →+* Ω, spMap τ ≫ x = spMap τ' ≫ x ↔ ∀ c ∈ E, τ c = τ' c) ∧ (∀ (K' : Type) [Field K'] (j : K' →+* Ω), E ≤ j.fieldRange ↔ ∃ y : Sp K' ⟶ X, spMap j ≫ y = x) ∧ ∀ (K : Type) [Field K] [Algebra K Ω] (s : X ⟶ Sp K), LocallyOfFiniteType s → x ≫ s = spMap (algebraMap K Ω) → Algebra.IsAlgebraic K Ω → ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ L.toSubfield = E := by
  intro X Ω _ x
  obtain ⟨⟨p, φ⟩, hx⟩ := (Scheme.SpecToEquivOfField Ω X).symm.surjective x
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hx
  subst hx
  let f : X.residueField p →+* Ω := φ.hom
  refine ⟨f.fieldRange, fun τ τ' => ?_, fun K' _ j => ⟨fun h => ?_, ?_⟩, ?_⟩
  · rw [← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp,
      Spec.map_inj]
    constructor
    · rintro h _ ⟨c, rfl⟩
      exact congrArg (fun g => g.hom c) h
    · intro h
      ext c
      exact h _ ⟨c, rfl⟩
  · let e : K' ≃+* j.fieldRange := j.rangeRestrictFieldEquiv
    let g : X.residueField p →+* K' :=
      e.symm.toRingHom.comp (f.codRestrict j.fieldRange fun c => h ⟨c, rfl⟩)
    refine ⟨Spec.map (CommRingCat.ofHom g) ≫ X.fromSpecResidueField p, ?_⟩
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext c
    exact congrArg Subtype.val (e.apply_symm_apply ⟨f c, h ⟨c, rfl⟩⟩)
  · rintro ⟨y, hy⟩
    obtain ⟨⟨q, ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K' X).symm.surjective y
    simp only [Scheme.SpecToEquivOfField_symm_apply] at hy
    rw [← Category.assoc, ← Spec.map_comp] at hy
    obtain ⟨e, he⟩ := residue_embedding_unique _ _ hy.symm
    rintro _ ⟨c, rfl⟩
    exact ⟨ψ.hom ((X.residueFieldCongr e).hom.hom c), (congrArg (fun g => g.hom c) he).symm⟩
  · intro K _ _ s hs hxs halg
    obtain ⟨ψ, hψ⟩ := Spec.map_surjective (X.fromSpecResidueField p ≫ s)
    have hess := essFiniteType_residueField_of_locallyOfFiniteType s p ψ hψ
    rw [Category.assoc, ← hψ, ← Spec.map_comp, Spec.map_inj] at hxs
    letI : Algebra K (X.residueField p) := ψ.hom.toAlgebra
    let fa : X.residueField p →ₐ[K] Ω :=
      { f with commutes' := fun c => congrArg (fun g => g.hom c) hxs }
    haveI : Algebra.EssFiniteType K (X.residueField p) := hess
    haveI : Algebra.IsAlgebraic K (X.residueField p) :=
      Algebra.IsAlgebraic.of_injective fa f.injective
    haveI : Module.Finite K (X.residueField p) := Algebra.finite_of_essFiniteType_of_isAlgebraic
    refine ⟨fa.fieldRange, ?_, rfl⟩
    exact Module.Finite.equiv (AlgEquiv.ofInjectiveField fa).toLinearEquiv
end GlobalTheory.SS
