-- Prove2me | solution 1 for GlobalTheory.FormalChart.spMap_valH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:23.779567+00:00
-- url     : https://prove2.me/submissions/3ba71d36-fe0e-476d-9249-ac979208e787

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LePreimageOfClosedPoint

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
open GlobalTheory GlobalTheory.FormalChart
open GlobalTheory.KeyKa.EtBaseChange
variable {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) {T : Type} [CommRing T]
namespace GlobalTheory.FormalChart
theorem _root_.solution (w : Sp T ⟶ X) (hw : ⊤ ≤ w ⁻¹ᵁ V) :
    spMap (R := Γ(X, V)) (valH w V hw) ≫ hV.fromSpec = w := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec w hV (isAffineOpen_top (Spec (CommRingCat.of T))) hw
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  show Spec.map (w.appLE V ⊤ hw ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).hom) ≫ hV.fromSpec = w
  rw [Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]
end GlobalTheory.FormalChart
