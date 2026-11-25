-- Prove2me | solution 1 for GlobalTheory.SmoothDedekind.smoothOfRelativeDimension_of_flat_of_tangent_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:44:58.186389+00:00
-- url     : https://prove2.me/submissions/2d441d1e-7d8f-45ab-8991-429e1a9f9e80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfFlatDedekindTangentLe
import Theorems.Thm_GlobalTheory_SmoothDedekind_exists_isStandardSmoothOfRelativeDimension_of_isMaximal
import Theorems.Thm_GlobalTheory_exists_affine_chart_over


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.SmoothDedekind
open GlobalTheory.SmoothTangent IsLocalRing
namespace GlobalTheory.SmoothDedekind
theorem _root_.solution : ∀ (o : Type) [CommRing o] [IsDedekindDomain o] [CharZero o] (X : Scheme.{0}) (s : X ⟶ Sp o) (d : ℕ), Algebra.FiniteType ℤ o → Flat s → LocallyOfFiniteType s → (∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ X), IsOpenImmersion x → x ≫ s = spMap (algebraMap o R) → ∀ q ∈ minimalPrimes (FractionRing o ⊗[o] R), (d : WithBot ℕ∞) ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (β : o →+* K) (x : Sp (TrivSqZeroExt K (Fin r → K)) ⟶ X), x ≫ s = spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) → (∀ lam : (Fin r → K) →ₗ[K] K, spMap (dirMap lam) ≫ x = constPt (spMap (dirMap lam) ≫ x) → lam = 0) → r ≤ d) → SmoothOfRelativeDimension d s := by
  intro o _ _ _ X s d _ _ _ hd ht
  have key (z : X) : ∃ U : X.Opens, z ∈ U ∧ SmoothOfRelativeDimension d (U.ι ≫ s) := by
    obtain ⟨A, _, _, j, _, p, hp, hj⟩ := exists_affine_chart_over s z
    have : Algebra.FiniteType o A := RingHom.finiteType_algebraMap.mp <|
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
        (φ := CommRingCat.ofHom (algebraMap o A))).mp (hj ▸ inferInstance)
    have : Module.Flat o A := RingHom.flat_algebraMap_iff.mp <|
      (HasRingHomProperty.Spec_iff (P := @Flat)
        (φ := CommRingCat.ofHom (algebraMap o A))).mp (hj ▸ inferInstance)
    obtain ⟨q, hq, hpq⟩ := Ideal.exists_le_maximal _ p.isPrime.ne_top
    obtain ⟨f, hf, hs⟩ := exists_isStandardSmoothOfRelativeDimension_of_isMaximal o
      (hd A j ‹_› hj) (d := d) (fun C _ _ r g h₁ h₂ ↦ by
        refine ht C r ((TrivSqZeroExt.fstHom C C (Fin r → C)).toRingHom.comp
          (g.comp (algebraMap o A))) (spMap g ≫ j) ?_ fun lam h ↦ h₂ lam fun a ↦ ?_
        · rw [Category.assoc, hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 2
          refine RingHom.ext fun c ↦ TrivSqZeroExt.ext ?_ ?_
          · rfl
          · exact h₁ c
        · simp only [constPt, ← Category.assoc, cancel_mono, ← Spec.map_comp,
            ← CommRingCat.ofHom_comp] at h
          have h' := congrArg (fun t ↦ TrivSqZeroExt.snd (t.hom a)) (Spec.map_injective h)
          simpa [dirMap, TrivSqZeroExt.algebraMap_eq_inl] using h') q
    let j' := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) ≫ j
    have hs' : SmoothOfRelativeDimension d (j' ≫ s) := by
      rw [Category.assoc, hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq,
        HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)]
      exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
        ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap d).mpr hs)
    refine ⟨j'.opensRange, ?_, ?_⟩
    · obtain ⟨t, ht⟩ :
          p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away f))) := by
        rw [PrimeSpectrum.localization_away_comap_range _ f]
        exact fun h ↦ hf (hpq h)
      refine ⟨t, ?_⟩
      rw [← hp, ← ht]
      rfl
    · rw [← j'.isoOpensRange_inv_comp, Category.assoc]
      have := smoothOfRelativeDimension_comp 0 d j'.isoOpensRange.inv (j' ≫ s)
      rwa [zero_add] at this
  choose U hU hs using key
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension d)
  exact IsZariskiLocalAtSource.of_iSup_eq_top U
    (top_le_iff.mp fun z _ ↦ le_iSup U z (hU z)) hs
end GlobalTheory.SmoothDedekind
