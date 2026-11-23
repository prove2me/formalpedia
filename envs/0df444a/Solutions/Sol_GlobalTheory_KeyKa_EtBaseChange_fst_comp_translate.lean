-- Prove2me | solution 1 for GlobalTheory.KeyKa.EtBaseChange.fst_comp_translate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:36.000175+00:00
-- url     : https://prove2.me/submissions/8c7ae5ee-bb72-493f-a4d3-92f4ff431218

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia

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
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.EtBaseChange
variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]
namespace GlobalTheory.KeyKa.EtBaseChange
theorem _root_.solution (z : 𝟙_ (Over (Sp R)) ⟶ G) (v : epsR R ⟶ G) (hv : IsTangent v) :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ ((toUnit (epsR R) ≫ z) * v).left = z.left := by
  let r : 𝟙_ (Over (Sp R)) ⟶ epsR R := Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) (by
    show spMap _ ≫ spMap _ = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    congr 1)
  have h1 : r ≫ v = 1 := by
    have e₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ G) = η[G] := by rw [Hom.one_def]; simp
    rw [e₁]
    exact Over.OverMorphism.ext hv
  have h2 : r ≫ toUnit (epsR R) ≫ z = z := by
    rw [← Category.assoc, toUnit_unique (r ≫ toUnit (epsR R)) (𝟙 _), Category.id_comp]
  have h3 : r ≫ ((toUnit (epsR R) ≫ z) * v) = z := by
    rw [MonObj.comp_mul, h1, h2, _root_.mul_one]
  exact congrArg CommaMorphism.left h3
end GlobalTheory.KeyKa.EtBaseChange
