-- Prove2me | solution 1 for GlobalTheory.PowUnif.val_g_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:13.169839+00:00
-- url     : https://prove2.me/submissions/e9c697b5-74e7-48c1-9366-914b8fc4928e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Theorems.Thm_GlobalTheory_PowUnif_val_res
import Theorems.Thm_P2M_GlobalTheory_valAt__one_9935cf2928d8


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
noncomputable section
open GlobalTheory GlobalTheory.PowUnif
variable {X Y : Scheme.{0}}
namespace GlobalTheory.PowUnif
theorem _root_.solution {L : LB X} (hL : L.IsLB) (x : Sp ℂ ⟶ X) (i : L.ι) (h : ⊤ ≤ x ⁻¹ᵁ L.U i) :
    valAt' x (L.U i ⊓ L.U i) (L.g i i).val = 1 := by
  rw [← val_res x (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i) _ h, hL.g_self, Units.val_one, valAt'_one x h]
end GlobalTheory.PowUnif
