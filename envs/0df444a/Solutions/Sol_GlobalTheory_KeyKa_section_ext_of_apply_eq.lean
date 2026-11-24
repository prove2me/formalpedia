-- Prove2me | solution 1 for GlobalTheory.KeyKa.section_ext_of_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:32:29.240985+00:00
-- url     : https://prove2.me/submissions/1efef1c9-3e6a-4152-b965-875397a4c958

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_TransversalZerosOfJacobianNeZeroDomain

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
open GlobalTheory GlobalTheory.KeyKa
open EtBaseChange
namespace GlobalTheory.KeyKa
theorem _root_.solution {K : Type} [Field K] {X : Scheme.{0}} (t : X ⟶ Sp K) (a b : Sp K ⟶ X)
    (ha : a ≫ t = 𝟙 _) (hb : b ≫ t = 𝟙 _) (p : Sp K) (h : a p = b p) : a = b := by
  obtain ⟨⟨y, α⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective a
  obtain ⟨⟨y', β⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective b
  simp only [Scheme.SpecToEquivOfField_symm_apply] at ha hb h ⊢
  have hy : y = y' := by simpa using h
  subst hy
  obtain ⟨c, hc⟩ := Spec.map_surjective (X.fromSpecResidueField y ≫ t)
  rw [Category.assoc, ← hc, ← Spec.map_comp, ← Spec.map_id] at ha hb
  have h₁ := Spec.map_injective ha
  have h₂ := Spec.map_injective hb
  have e₁ : ∀ k, α.hom (c.hom k) = k := fun k => congrArg (fun q => q.hom k) h₁
  have e₂ : ∀ k, β.hom (c.hom k) = k := fun k => congrArg (fun q => q.hom k) h₂
  have : α = β := by
    ext k
    have e₃ : c.hom (α.hom k) = k := α.hom.injective (e₁ _)
    exact (e₂ (α.hom k)).symm.trans (congrArg β.hom e₃)
  rw [this]
end GlobalTheory.KeyKa
