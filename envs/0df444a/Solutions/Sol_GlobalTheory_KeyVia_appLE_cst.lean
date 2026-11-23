-- Prove2me | solution 1 for GlobalTheory.KeyVia.appLE_cst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:01:44.70589+00:00
-- url     : https://prove2.me/submissions/f7959682-74b9-423a-aba0-ab666f07d658

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PwIsoIsGen

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
open GlobalTheory GlobalTheory.KeyVia
variable {X Y : Scheme.{0}} {L : LB X} {L' : LB Y} {φ : Y ⟶ X}
namespace GlobalTheory.KeyVia
theorem _root_.solution {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (p : X ⟶ Sp R) (p' : Y ⟶ Sp R')
    (hφ : φ ≫ p = p' ≫ spMap f) {U : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (r : R) :
    (φ.appLE U V h).hom (cst p U r) = cst p' V (f r) := by
  refine (appLE_res h le_top _).trans ?_
  have e₁ : p.appTop ≫ φ.appTop = (spMap f).appTop ≫ p'.appTop := by
    rw [← Scheme.Hom.comp_appTop, hφ, Scheme.Hom.comp_appTop]
  have e₂ := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)
  have e₃ : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫ φ.appTop =
      CommRingCat.ofHom f ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫ p'.appTop := by
    rw [e₁, ← Category.assoc, ← e₂, Category.assoc]
  exact congrArg (fun q => rs Y (le_top : V ≤ ⊤) (q.hom r)) e₃
end GlobalTheory.KeyVia
