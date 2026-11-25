-- Prove2me | solution 1 for GlobalTheory.TraceDescent.exists_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:04:25.758469+00:00
-- url     : https://prove2.me/submissions/40e3266c-b075-48e7-a65e-d4763cdcd670

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
import Theorems.Thm_GlobalTheory_AbLaw_PowVanish_app_eq_pb
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom



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
omit hτ
namespace GlobalTheory.TraceDescent
theorem _root_.solution (U : X.Opens) (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ U) (e' : f ⁻¹ᵁ U ≤ W) (s : Γ(Y, W))
    (hs : ∀ y (e : W ≤ τ y ⁻¹ᵁ W), pb (τ y) e s = s) : ∃! g : Γ(X, U), pb f e g = s := by
  obtain rfl := le_antisymm e e'
  simpa only [app_eq_pb] using hgal U s hs
end GlobalTheory.TraceDescent
