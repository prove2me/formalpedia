-- Prove2me | solution 1 for GlobalTheory.TraceDescent.pb_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:24:14.45642+00:00
-- url     : https://prove2.me/submissions/911dd6a8-e755-4f97-9dfa-1f9862b0b689

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExactAtSectionCubeOfMulPullback
import Theorems.Thm_GlobalTheory_TraceDescent_exists_fun
import Theorems.Thm_GlobalTheory_AbLaw_PowVanish_pb_congr
import Theorems.Thm_GlobalTheory_AbLaw_PowVanish_pb_pb


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
open GlobalTheory
noncomputable section
open GlobalTheory GlobalTheory.TraceDescent
open GlobalTheory.AbLaw.PowVanish
variable {X Y : Scheme.{0}} (f : Y ⟶ X) (M : LB X)
variable {G : Type} (τ : G → (Y ⟶ Y)) (hτ : ∀ y, τ y ≫ f = f)
    (hgal : ∀ (U : X.Opens) (s : Γ(Y, f ⁻¹ᵁ U)),
      (∀ y (e : f ⁻¹ᵁ U ≤ τ y ⁻¹ᵁ (f ⁻¹ᵁ U)), pb (τ y) e s = s) → ∃! g : Γ(X, U), (f.app U).hom g = s)
include hτ hgal
namespace GlobalTheory.TraceDescent
theorem _root_.solution (U : X.Opens) (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ U) (e' : f ⁻¹ᵁ U ≤ W) :
    Function.Injective (pb f e) := fun a _ hab =>
  (exists_fun f τ hgal U W e e' (pb f e a) (fun y _ => by rw [pb_pb, pb_congr (hτ y)])).unique rfl hab.symm
end GlobalTheory.TraceDescent
