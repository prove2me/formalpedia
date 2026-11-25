-- Prove2me | solution 1 for GlobalTheory.GrpDescent.grpObj_descends_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:48:32.329509+00:00
-- url     : https://prove2.me/submissions/cdced545-5c21-457e-a5a8-d398a3125783

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_GrpObjDescendsFaithfullyFlat
import Theorems.Thm_GlobalTheory_GrpDescent_grpObj_descends

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
open GlobalTheory GlobalTheory.GrpDescent
variable {S S₀ : Scheme.{0}}
namespace GlobalTheory.GrpDescent
theorem _root_.solution : ∀ (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] [Module.FaithfullyFlat R₀ R] (A : Over (Sp R)) [GrpObj A] (A₀ : Over (Sp R₀)) [Flat A₀.hom] [IsSeparated A₀.hom] [QuasiCompact A₀.hom] (π : A.left ⟶ A₀.left) (e₀ : 𝟙_ (Over (Sp R₀)) ⟶ A₀) (m₀ : A₀ ⊗ A₀ ⟶ A₀) (i₀ : A₀ ⟶ A₀) (π₂ : (A ⊗ A).left ⟶ (A₀ ⊗ A₀).left), IsPullback π A.hom A₀.hom (spMap (algebraMap R₀ R)) → π₂ ≫ (fst A₀ A₀).left = (fst A A).left ≫ π → π₂ ≫ (snd A₀ A₀).left = (snd A A).left ≫ π → η[A].left ≫ π = spMap (algebraMap R₀ R) ≫ e₀.left → μ[A].left ≫ π = π₂ ≫ m₀.left → (GrpObj.inv : A ⟶ A).left ≫ π = π ≫ i₀.left → ∃ _ : GrpObj A₀, IsGrpPullback A A₀ (spMap (algebraMap R₀ R)) π := by
  intro R₀ R _ _ _ _ A _ A₀ _ _ _ π e₀ m₀ i₀ π₂ hπ h1 h2 he hm hi
  have hff : (algebraMap R₀ R).FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.2 ‹_›
  obtain ⟨_, _⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R₀ R))).2 hff
  exact grpObj_descends _ A A₀ π e₀ m₀ i₀ π₂ hπ h1 h2 he hm hi
end GlobalTheory.GrpDescent
