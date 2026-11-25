-- Prove2me | solution 1 for GlobalTheory.CubicUnit.exists_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:34:17.476703+00:00
-- url     : https://prove2.me/submissions/c8fd8b3c-e551-496c-b174-8371cadbd177

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
import Theorems.Thm_GlobalTheory_CubicUnit_ev_val
import Theorems.Thm_GlobalTheory_FunDescent_comp_appTop_apply
import Theorems.Thm_GlobalTheory_existsUnique_character_of_mul


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
theorem _root_.solution (Y : Over S) [ConnectedSpace Y.left] (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ)
    (hρ : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      ev (lift (t * t') y) ρ = ev (lift t y) ρ * ev (lift t' y) ρ) :
    ∃ χ : X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y), ev (lift t y) ρ = chV t χ := by
  have hm : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom ρ.val =
        (lift t y).left.appTop.hom ρ.val * (lift t' y).left.appTop.hom ρ.val := by
    intro Z t t' y
    have := congrArg Units.val (hρ Z t t' y)
    simpa [ev_val] using this
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.existsUnique_character_of_mul S X Y ρ hm
  refine ⟨χ, fun Z t y => ?_⟩
  ext
  rw [ev_val, chV_val, hχ, ← GlobalTheory.FunDescent.comp_appTop_apply, ← Over.comp_left, lift_fst]
end GlobalTheory.CubicUnit
