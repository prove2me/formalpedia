-- Prove2me | solution 1 for GlobalTheory.SpreadScheme.hasModel_of_isAffine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:20:12.473289+00:00
-- url     : https://prove2.me/submissions/59a9be54-e199-45bf-8790-70959269c27d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SchemeDescendsToSubalgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
noncomputable section
open GlobalTheory GlobalTheory.SpreadScheme
open GlobalTheory.Spread GlobalTheory.GlueModels
attribute [instance] PairModel.lfp PairModel.qs PairModel.qc PairModel.opn PairModel.qca
variable {S S₁ S₀ U T : Scheme.{0}} {f : S ⟶ S₀} {p : U ⟶ S} {a : T ⟶ U}
variable {V : Type} [CommRing V]
namespace GlobalTheory.SpreadScheme
theorem _root_.solution {X : Scheme.{0}} (q : X ⟶ Sp V) [IsAffine X] [LocallyOfFinitePresentation q] :
    HasModel q := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (R := CommRingCat.of V) (S := Γ(X, ⊤)) (X.isoSpec.inv ≫ q)
  have h1 : LocallyOfFinitePresentation (Spec.map ψ) := by rw [hψ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)] at h1
  let A : Type := Γ(X, ⊤)
  letI : Algebra V A := ψ.hom.toAlgebra
  haveI : Algebra.FinitePresentation V A := h1
  let P := Algebra.Presentation.ofFinitePresentation V A
  let k : Subalgebra ℤ V := Algebra.adjoin ℤ P.coeffs
  have hk : Algebra.FiniteType ℤ k := Algebra.FiniteType.adjoin_of_finite P.finite_coeffs
  haveI : P.HasCoeffs k := ⟨fun x hx => ⟨⟨x, Algebra.subset_adjoin hx⟩, rfl⟩⟩
  let e := P.tensorModelOfHasCoeffsEquiv k
  have h := (CommRingCat.isPushout_tensorProduct k V (P.ModelOfHasCoeffs k)).flip
  have h' : IsPushout (CommRingCat.ofHom (algebraMap k (P.ModelOfHasCoeffs k)))
      (CommRingCat.ofHom (algebraMap k V))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom) ≫ e.toRingEquiv.toCommRingCatIso.hom)
      (CommRingCat.ofHom (algebraMap V A)) := by
    refine h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · ext x
      exact e.commutes x
  obtain ⟨g, h2⟩ : ∃ g, IsPullback g (Spec.map ψ) (spMap (algebraMap k (P.ModelOfHasCoeffs k)))
      (spMap (algebraMap k V)) := ⟨_, isPullback_SpecMap_of_isPushout _ _ _ _ h'⟩
  refine ⟨k, inferInstance, algebraMap k V, _, spMap (algebraMap k (P.ModelOfHasCoeffs k)), X.isoSpec.hom ≫ g,
    hk, ?_, inferInstance, inferInstance,
    h2.of_iso X.isoSpec.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_⟩
  · exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2
      (RingHom.finitePresentation_algebraMap.2 inferInstance)
  · simp
  · simp [hψ]
  · simp
  · simp
end GlobalTheory.SpreadScheme
