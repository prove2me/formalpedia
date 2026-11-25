-- Prove2me | solution 1 for GlobalTheory.TraceDescent.pullLE_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:59:23.22197+00:00
-- url     : https://prove2.me/submissions/84d9fc0a-b0ba-466c-9973-925a808ccc46

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
import Theorems.Thm_GlobalTheory_TraceDescent_coord_pullLE
import Theorems.Thm_GlobalTheory_TraceDescent_pb_injective
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_coord_pullLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


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
theorem _root_.solution (V : X.Opens) (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ V) (e' : f ⁻¹ᵁ V ≤ W) :
    Function.Injective (SecOn.pullLE M f V W e) := fun a b hab => GlobalTheory.LB.sec_ext fun i => by
  have h := (coord_pullLE f M e a (fun _ => i)).symm.trans
    ((congrArg (GlobalTheory.LB.coord · (fun _ => i : (M.pull f).ι)) hab).trans (coord_pullLE f M e b (fun _ => i)))
  exact pb_injective f τ hτ hgal (V ⊓ M.U i) (W ⊓ (M.pull f).U (fun _ => i)) _
    (fun y hy => ⟨e' hy.1, mem_pull.2 hy.2⟩) h
end GlobalTheory.TraceDescent
