-- Prove2me | solution 1 for GlobalTheory.PowUnif.val_div_g
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:51.143138+00:00
-- url     : https://prove2.me/submissions/6e9c59f3-4947-469a-8845-6de0f041b377

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
import Theorems.Thm_P2M_GlobalTheory_valAt__mul_dca2439ccec2
import Theorems.Thm_P2M_GlobalTheory_valAt__units_inv_d8876f25a60d


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
theorem _root_.solution (M L : LB X) (x : Sp ℂ ⟶ X) (a a' : M.ι) (b b' : L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ (M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b'))) :
    valAt' x (M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b')) ((LB.div M L).g (a, b) (a', b')).val =
      valAt' x (M.U a ⊓ M.U a') (M.g a a').val * (valAt' x (L.U b ⊓ L.U b') (L.g b b').val)⁻¹ := by
  rw [← val_res x (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)) (M.g a a') h,
    ← val_res x (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) (L.g b b') h,
    ← valAt'_units_inv x h, ← valAt'_mul]
  rfl
end GlobalTheory.PowUnif
