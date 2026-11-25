-- Prove2me | solution 1 for GlobalTheory.EquivDesc.exists_stalk_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:39:23.109296+00:00
-- url     : https://prove2.me/submissions/274b4493-f529-4aed-aa6c-81aa53484f17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
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
open GlobalTheory.UU TopologicalSpace
noncomputable section
open GlobalTheory GlobalTheory.EquivDesc
variable {S : Scheme.{0}}
namespace GlobalTheory.EquivDesc
theorem _root_.solution {Z Z' : Scheme.{0}} (κ : Z' ⟶ Z) [IsOpenImmersion κ] (z : Z') :
    ∃ Φ : (Z.presheaf.stalk (κ z))ˣ →* (Z'.presheaf.stalk z)ˣ, Function.Injective Φ ∧
      ∀ (Y : Scheme.{0}) (f : Z ⟶ Y) (U : Y.Opens) (a : Γ(Y, U)ˣ), f (κ z) ∈ U →
        Φ (gm f (κ z) U a) = gm (κ ≫ f) z U a := by
  refine ⟨Units.map (κ.stalkMap z).hom.toMonoidHom,
    Units.map_injective (ConcreteCategory.bijective_of_isIso (κ.stalkMap z)).1, fun Y f U a h => Units.ext ?_⟩
  rw [gm_val (κ ≫ f) z U h]
  change (κ.stalkMap z).hom (gm f (κ z) U a).val = _
  rw [gm_val f (κ z) U h]
  exact Scheme.Hom.germ_stalkMap_apply κ (f ⁻¹ᵁ U) z h _
end GlobalTheory.EquivDesc
