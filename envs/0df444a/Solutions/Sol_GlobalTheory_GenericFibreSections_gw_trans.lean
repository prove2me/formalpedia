-- Prove2me | solution 1 for GlobalTheory.GenericFibreSections.gw_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:56:12.220953+00:00
-- url     : https://prove2.me/submissions/7112a3c3-720f-4403-94fa-66d02eb5dd7e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SameB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_BijectiveOfIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.GenericFibreSections
variable {X₁ X₂ Y Y' : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂}
namespace GlobalTheory.GenericFibreSections
theorem _root_.solution {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} (hw : w.IsGen) (y : Y)
    {i i' : L₁.ι} {j j' : L₂.ι} (hi : f₁ y ∈ L₁.U i) (hi' : f₁ y ∈ L₁.U i') (hj : f₂ y ∈ L₂.U j) (hj' : f₂ y ∈ L₂.U j') :
    gw w (𝟙 Y) y j (fun _ => i) * gm (𝟙 Y ≫ f₁) y _ (L₁.g i i') =
      gm (𝟙 Y ≫ f₂) y _ (L₂.g j j') * gw w (𝟙 Y) y j' (fun _ => i') := by
  have e := (isGen_iff w).1 hw Y (𝟙 Y) y j j' (fun _ => i) (fun _ => i') hj hj' (mem_pull.2 hi) (mem_pull.2 hi')
  rw [gm_pull_g L₁ f₁ (𝟙 Y) y _ _ (mem_pull.2 hi) (mem_pull.2 hi')] at e
  rw [e, _root_.mul_right_comm, inv_mul_cancel_right]
end GlobalTheory.GenericFibreSections
