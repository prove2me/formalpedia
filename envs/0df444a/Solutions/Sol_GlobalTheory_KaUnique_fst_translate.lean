-- Prove2me | solution 1 for GlobalTheory.KaUnique.fst_translate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:25.549111+00:00
-- url     : https://prove2.me/submissions/645c7fed-3a38-4381-9d01-230d49a4ddf4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SignSwap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_TopLeTranslate

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
open GlobalTheory GlobalTheory.KaUnique
variable {T T' : Type} [CommRing T] [CommRing T'] {X : Scheme.{0}}
variable {R : Type} [CommRing R]
namespace GlobalTheory.KaUnique
theorem _root_.solution (x : KeyIn R) (z : Pt x) (k : Fin x.P.g) :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ ((toUnit (epsR R) ≫ z) * x.v k).left = z.left := by
  let io : 𝟙_ (Over (Sp R)) ⟶ epsR R := Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)
  have h1 : io ≫ x.v k = 1 := by
    rw [Hom.one_def, toUnit_unique (toUnit (𝟙_ (Over (Sp R)))) (𝟙 _), Category.id_comp]
    exact Over.OverMorphism.ext (x.basis.1 k)
  have h2 : io ≫ ((toUnit (epsR R) ≫ z) * x.v k) = z := by
    rw [MonObj.comp_mul, h1, _root_.mul_one, ← Category.assoc, toUnit_unique (io ≫ toUnit _) (𝟙 _), Category.id_comp]
  exact congrArg (·.left) h2
end GlobalTheory.KaUnique
