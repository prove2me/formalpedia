-- Prove2me | solution 1 for GlobalTheory.WtBundle.exists_unit_desc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:30:27.145896+00:00
-- url     : https://prove2.me/submissions/4cd88cab-acc2-4ccf-820a-3ac9a218f1b6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CommGroupCommonFactorQuotientCancel
import Theorems.Thm_GlobalTheory_WtBundle_gm_appLE
import Theorems.Thm_GlobalTheory_FunDescent_exists_app_eq
import Theorems.Thm_GlobalTheory_FunDescent_isUnit_of_isUnit_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


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
theorem _root_.solution (π : X ⟶ Y) [Flat π] [Surjective π] [QuasiCompact π] (U : Y.Opens)
    (f : Γ(X, π ⁻¹ᵁ U)ˣ)
    (hf : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ X) (z : Z), g₁ ≫ π = g₂ ≫ π → π (g₁ z) ∈ U → π (g₂ z) ∈ U →
      gm g₁ z (π ⁻¹ᵁ U) f = gm g₂ z (π ⁻¹ᵁ U) f) :
    ∃ a : Γ(Y, U)ˣ, ∀ (Z : Scheme.{0}) (g : Z ⟶ X) (z : Z), π (g z) ∈ U →
      gm (g ≫ π) z U a = gm g z (π ⁻¹ᵁ U) f := by
  obtain ⟨a, ha⟩ := FunDescent.exists_app_eq π U f.val fun Z g₁ g₂ h₁ h₂ e => by
    have : Units.map (g₁.appLE _ ⊤ h₁).hom.toMonoidHom f = Units.map (g₂.appLE _ ⊤ h₂).hom.toMonoidHom f :=
      unit_ext fun z _ => by
        rw [gm_appLE, gm_appLE]
        exact hf Z g₁ g₂ z e (h₁ trivial) (h₂ trivial)
    exact congrArg Units.val this
  have hu : IsUnit a := FunDescent.isUnit_of_isUnit_app π U a (ha ▸ f.isUnit)
  refine ⟨hu.unit, fun Z g z hz => ?_⟩
  rw [← gm_pull g π z U hz]
  exact congrArg _ (Units.ext ha)
end GlobalTheory.WtBundle
