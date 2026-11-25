-- Prove2me | solution 1 for GlobalTheory.IsoDesc.exists_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:07:23.582024+00:00
-- url     : https://prove2.me/submissions/5239fac3-57ec-441b-886d-01080e89c723

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
import Theorems.Thm_GlobalTheory_existsUnique_character_of_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_over_appTop_comp


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
namespace GlobalTheory.IsoDesc
theorem _root_.solution (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ)
    (h : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y) (z : Z.left),
      gm (lift (t * t') y).left z ⊤ ρ = gm (lift t y).left z ⊤ ρ * gm (lift t' y).left z ⊤ ρ) :
    ∃ χ : X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y) (z : Z.left),
      gm (lift t y).left z ⊤ ρ = gm (𝟙 Z.left) z ⊤ (chV t χ) := by
  obtain ⟨χ, hχ, -⟩ := existsUnique_character_of_mul S X Y ρ fun Z t t' y =>
    (appTop_eq_iff (Units.map (lift (t * t') y).left.appTop.hom.toMonoidHom ρ)
      (Units.map (lift t y).left.appTop.hom.toMonoidHom ρ * Units.map (lift t' y).left.appTop.hom.toMonoidHom ρ)).2
      fun z => by rw [map_mul, ← gm_top, ← gm_top, ← gm_top, h]
  refine ⟨χ, fun Z t y z => ?_⟩
  rw [gm_top]
  refine congrArg _ (Units.ext ?_)
  show (lift t y).left.appTop.hom ρ.val = _
  rw [hχ, chV_val, Rosenlicht.over_appTop_comp, lift_fst]
end GlobalTheory.IsoDesc
