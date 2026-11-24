-- Prove2me | solution 1 for GlobalTheory.RelBasis.indepOn_spanOn_of_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:35:55.079208+00:00
-- url     : https://prove2.me/submissions/94b069c5-7f90-4f81-9627-fc27f4c3fd38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IndepOnEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PullbackSectionsBasisAffineBaseChangeOfAffine
import Theorems.Thm_GlobalTheory_RelBasis_affine_transfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.RelBasis
variable {X Y T Y' T' : Scheme.{0}} {L : LB X} {t : ℤ} {N : ℕ}
namespace GlobalTheory.RelBasis
theorem _root_.solution : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (p : X ⟶ Sp R) (L : LB X) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t)), (∀ (R' : Type) [CommRing R'] (f : R →+* R'), ∃ (Y : Scheme.{0}) (p₁ : Y ⟶ Sp R') (p₂ : Y ⟶ X), IsPullback p₂ p₁ p (spMap f) ∧ GlobalTheory.RelBasis.IndepOn b p₁ p₂ ⊤ ∧ GlobalTheory.RelBasis.SpanOn b p₁ p₂ ⊤) → ∀ (T Y : Scheme.{0}) (q : T ⟶ Sp R) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X), IsPullback p₂ p₁ p q → ∀ W : T.Opens, IsAffineOpen W → GlobalTheory.RelBasis.IndepOn b p₁ p₂ W ∧ GlobalTheory.RelBasis.SpanOn b p₁ p₂ W := by
  intro R _ X p L t N b H T Y q p₁ p₂ sq W hW
  obtain ⟨Y', p₁', p₂', sq', h₁, h₂⟩ := H Γ(T, W) (Spec.preimage (hW.fromSpec ≫ q)).hom
  have hf : spMap (Spec.preimage (hW.fromSpec ≫ q)).hom = hW.fromSpec ≫ q := Spec.map_preimage _
  rw [hf] at sq'
  let j : Y' ⟶ Y := sq.lift p₂' (p₁' ≫ hW.fromSpec) (by rw [sq'.w, Category.assoc])
  have e₂ : j ≫ p₂ = p₂' := sq.lift_fst _ _ _
  have e₁ : j ≫ p₁ = p₁' ≫ hW.fromSpec := sq.lift_snd _ _ _
  rw [← e₂] at sq' h₁ h₂
  have sq'' : IsPullback j p₁' p₁ hW.fromSpec := IsPullback.of_right (by simpa using sq') e₁ sq
  have e : ⊤ ≤ hW.fromSpec ⁻¹ᵁ W := hW.fromSpec_preimage_self.ge
  refine affine_transfer b p₁ p₂ W j p₁' hW.fromSpec sq'' hW.range_fromSpec e ?_ h₁ h₂
  have : hW.fromSpec.appLE W ⊤ e = (Scheme.ΓSpecIso Γ(T, W)).inv := by
    rw [Scheme.Hom.appLE, hW.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ ((congrArg _ (Subsingleton.elim _ _)).trans (CategoryTheory.Functor.map_id _ _))).trans
      (Category.comp_id _)
  rw [this]
  exact ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso Γ(T, W)).inv
end GlobalTheory.RelBasis
