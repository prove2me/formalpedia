-- Prove2me | solution 1 for GlobalTheory.KeyKa.EtBaseChange.valT_appLE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:07:45.326125+00:00
-- url     : https://prove2.me/submissions/6fd1eff8-e470-464b-93d4-1559167c158c

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
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_valT_eq

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
variable {T T' : Type} [CommRing T] [CommRing T'] {X Y : Scheme.{0}}
namespace GlobalTheory.KeyKa.EtBaseChange
theorem _root_.solution (w : Sp T ⟶ Y) (φ : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (hle : V ≤ φ ⁻¹ᵁ U) (h : ⊤ ≤ w ⁻¹ᵁ V)
    (a : Γ(X, U)) : valT w V ((φ.appLE U V hle).hom a) = valT (w ≫ φ) U a := by
  have h' : ⊤ ≤ (w ≫ φ) ⁻¹ᵁ U := fun p hp => hle (h hp)
  rw [valT_eq w V h, valT_eq _ U h']
  have e := congrArg (fun q => q.hom a) (Scheme.Hom.appLE_comp_appLE w φ U V ⊤ hle h)
  exact congrArg (Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom e
end GlobalTheory.KeyKa.EtBaseChange
