-- Prove2me | solution 1 for GlobalTheory.CubicUnit.eq_zero_of_chV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:06:19.044818+00:00
-- url     : https://prove2.me/submissions/d6bbda03-510a-444d-9f95-3735f5271750

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvenCubicUnitEqOne
import Theorems.Thm_GlobalTheory_existsUnique_character_of_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


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
open GlobalTheory GlobalTheory.CubicUnit
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
namespace GlobalTheory.CubicUnit
theorem _root_.solution (Y : Over S) [ConnectedSpace Y.left] (χ : X)
    (h : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X), chV t χ = 1) : χ = 0 := by
  have key : ∀ ψ : X, (∀ (Z : Over S) (t : Z ⟶ splitTorus S X), chV t ψ = 1) →
      ((1 : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ) : Γ((splitTorus S X ⊗ Y).left, ⊤)) =
        (fst (splitTorus S X) Y).left.appTop.hom (charUnit S X ψ).val := by
    intro ψ hψ
    have := congrArg Units.val (hψ _ (fst (splitTorus S X) Y))
    rw [chV_val] at this
    rw [this, Units.val_one]
  have hm : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom ((1 : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ) : Γ((splitTorus S X ⊗ Y).left, ⊤)) =
        (lift t y).left.appTop.hom (1 : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ).val *
          (lift t' y).left.appTop.hom (1 : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ).val := by
    intro Z t t' y
    simp
  obtain ⟨ψ, -, huniq⟩ := GlobalTheory.existsUnique_character_of_mul S X Y 1 hm
  rw [huniq χ (key χ h), huniq 0 (key 0 fun Z t => chV_zero t)]
end GlobalTheory.CubicUnit
