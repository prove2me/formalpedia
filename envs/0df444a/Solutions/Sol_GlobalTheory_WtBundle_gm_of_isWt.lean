-- Prove2me | solution 1 for GlobalTheory.WtBundle.gm_of_isWt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:39:37.788844+00:00
-- url     : https://prove2.me/submissions/9e47a2bc-6fbb-485b-b6ee-97a3523fb6c1

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
import Theorems.Thm_GlobalTheory_WtBundle_gm_stalkMap
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
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
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.WtBundle
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X]
namespace GlobalTheory.WtBundle
theorem _root_.solution {i : splitTorus S X ⟶ G} {V : G.left.Opens} {u : Γ(G.left, V)ˣ} {χ : X} (hu : IsWt i V u.val χ)
    {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (h₁ : ((t ≫ i) * g).left z ∈ V)
    (h₂ : g.left z ∈ V) :
    gm ((t ≫ i) * g).left z V u = gm (𝟙 Z.left) z ⊤ (chV t χ) * gm g.left z V u := by
  let W : Z.left.Opens := ((t ≫ i) * g).left ⁻¹ᵁ V ⊓ g.left ⁻¹ᵁ V
  let Z' : Over S := Over.mk (W.ι ≫ Z.hom)
  let κ : Z' ⟶ Z := Over.homMk W.ι rfl
  let w : W.toScheme := ⟨z, h₁, h₂⟩
  have e : ((κ ≫ t) ≫ i) * (κ ≫ g) = κ ≫ ((t ≫ i) * g) := by rw [MonObj.comp_mul, Category.assoc]
  have k₁ : ⊤ ≤ (((κ ≫ t) ≫ i) * (κ ≫ g)).left ⁻¹ᵁ V := by
    rw [e]; exact fun y _ => y.2.1
  have k₂ : ⊤ ≤ (κ ≫ g).left ⁻¹ᵁ V := fun y _ => y.2.2
  have a : Units.map ((((κ ≫ t) ≫ i) * (κ ≫ g)).left.appLE V ⊤ k₁).hom.toMonoidHom u =
      chV (κ ≫ t) χ * Units.map ((κ ≫ g).left.appLE V ⊤ k₂).hom.toMonoidHom u :=
    Units.ext ((hu Z' _ _ k₁ k₂).trans (congrArg (· * _) (chV_val _ χ).symm))
  have b := congrArg (gm (𝟙 Z'.left) w ⊤) a
  rw [map_mul, gm_appLE, gm_appLE, ← gm_charUnit, e] at b
  rw [← gm_charUnit]
  apply Units.map_injective (f := (W.ι.stalkMap w).hom.toMonoidHom)
    (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap w)).1
  exact (gm_stalkMap W.ι w _ V h₁ u).trans (b.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_stalkMap W.ι w t.left ⊤ trivial _) (gm_stalkMap W.ι w g.left V h₂ u))).symm)
end GlobalTheory.WtBundle
