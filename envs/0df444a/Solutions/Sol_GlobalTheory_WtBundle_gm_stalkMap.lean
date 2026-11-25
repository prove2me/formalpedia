-- Prove2me | solution 1 for GlobalTheory.WtBundle.gm_stalkMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:20:12.370811+00:00
-- url     : https://prove2.me/submissions/a7815901-b7cf-4b17-a611-33c5a7a5f80f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CommGroupCommonFactorQuotientCancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_val


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
open GlobalTheory GlobalTheory.WtBundle
variable {X Y Z W : Scheme.{0}}
namespace GlobalTheory.WtBundle
theorem _root_.solution (κ : W ⟶ Z) (w : W) (r : Z ⟶ Y) (U : Y.Opens) (h : r (κ w) ∈ U) (a : Γ(Y, U)ˣ) :
    Units.map (κ.stalkMap w).hom.toMonoidHom (gm r (κ w) U a) = gm (κ ≫ r) w U a := by
  apply Units.ext
  rw [gm_val (κ ≫ r) w U h]
  show (κ.stalkMap w).hom (gm r (κ w) U a).val = _
  rw [gm_val r (κ w) U h]
  exact Scheme.Hom.germ_stalkMap_apply κ (r ⁻¹ᵁ U) w h _
end GlobalTheory.WtBundle
