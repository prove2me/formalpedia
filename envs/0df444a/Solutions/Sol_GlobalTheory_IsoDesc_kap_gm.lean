-- Prove2me | solution 1 for GlobalTheory.IsoDesc.kap_gm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:15:44.819998+00:00
-- url     : https://prove2.me/submissions/21a77b9d-9be6-43c4-a47c-bbafb83c8e51

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_val


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
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.IsoDesc
theorem _root_.solution (σ : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (a : Γ(X, U)ˣ) :
    kap σ z (gm r (σ z) U a) = gm (σ ≫ r) z U a := by
  by_cases h : r (σ z) ∈ U
  · apply Units.ext
    rw [gm_val (σ ≫ r) z U h]
    show (σ.stalkMap z).hom (gm r (σ z) U a).val = _
    rw [gm_val r (σ z) U h]
    exact Scheme.Hom.germ_stalkMap_apply σ (r ⁻¹ᵁ U) z h _
  · have h' : ¬ (σ ≫ r) z ∈ U := h
    rw [gm, gm, dif_neg h, dif_neg h']
    exact map_one _
end GlobalTheory.IsoDesc
