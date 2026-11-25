-- Prove2me | solution 1 for GlobalTheory.CubTrivTorus.prod_biTriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:21:44.261635+00:00
-- url     : https://prove2.me/submissions/1c6d256c-796c-4498-bf17-b3df9f49491b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConnectedSpaceOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubTrivDeltaAndEvenUnique

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
open GlobalTheory GlobalTheory.CubTrivTorus
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
variable {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] (i : H ⟶ G)
namespace GlobalTheory.CubTrivTorus
theorem _root_.solution {T : Over S} (t : T ⟶ H) (x : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ k : Fin 4, h ((lift t x).left ≫ lamφ i k) ^ Oε k =
      h ((t ≫ i) * x).left * (h (t ≫ i).left)⁻¹ * (h x.left)⁻¹ * h (1 : T ⟶ G).left := by
  have e1 : (lift t x).left ≫ ((fst H G ≫ i) * snd H G).left = ((t ≫ i) * x).left := by
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst_assoc, lift_snd]
  have e2 : (lift t x).left ≫ (fst H G ≫ i).left = (t ≫ i).left := by
    rw [← Over.comp_left, lift_fst_assoc]
  have e3 : (lift t x).left ≫ (snd H G).left = x.left := by
    rw [← Over.comp_left, lift_snd]
  have e4 : (lift t x).left ≫ (1 : H ⊗ G ⟶ G).left = (1 : T ⟶ G).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  rw [Fin.prod_univ_four]
  change h ((lift t x).left ≫ ((fst H G ≫ i) * snd H G).left) ^ (1 : ℤ) *
      h ((lift t x).left ≫ (fst H G ≫ i).left) ^ (-1 : ℤ) * h ((lift t x).left ≫ (snd H G).left) ^ (-1 : ℤ) *
      h ((lift t x).left ≫ (1 : H ⊗ G ⟶ G).left) ^ (1 : ℤ) = _
  rw [e1, e2, e3, e4]
  simp only [zpow_one, zpow_neg]
end GlobalTheory.CubTrivTorus
