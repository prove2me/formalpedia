-- Prove2me | solution 1 for GlobalTheory.IsoDesc.char_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:05:51.980889+00:00
-- url     : https://prove2.me/submissions/3dd6e043-8536-441d-a220-3747acce0326

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsCPMapDescends
import Theorems.Thm_GlobalTheory_IsoDesc_appTop_eq_iff
import Theorems.Thm_GlobalTheory_IsoDesc_IsQuot_trans
import Theorems.Thm_GlobalTheory_TorusUnit_IsCharNear_unique
import Theorems.Thm_GlobalTheory_UU_CubWeil_unique
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_GlobalTheory_UU_TorusCompat_unique
import Theorems.Thm_GlobalTheory_existsUnique_character_of_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.IsoDesc
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] (Y : Over S) [ConnectedSpace Y.left]
include Y
namespace GlobalTheory.IsoDesc
theorem _root_.solution {χ : X} (h : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (_ : Z ⟶ Y) (z : Z.left),
    gm (𝟙 Z.left) z ⊤ (chV t χ) = 1) : χ = 0 := by
  refine (existsUnique_character_of_mul S X Y 1 fun Z t t' y => by simp).unique ?_ ?_
  · rw [← chV_val]
    exact (appTop_eq_iff _ _).2 fun z => (map_one _).trans (h _ _ (snd _ _) z).symm
  · rw [← chV_val, chV_zero]
end GlobalTheory.IsoDesc
