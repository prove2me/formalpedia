-- Prove2me | solution 1 for GlobalTheory.EquivDesc.exists_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:56:06.856148+00:00
-- url     : https://prove2.me/submissions/56d5401b-aa58-42c7-b4a0-dfedfebccc00

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_GlobalTheory_splitTorusPointsEquiv_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_appLE_of_eq


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
theorem _root_.solution {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] (i : splitTorus S X ⟶ G) (U : G.left.Opens)
    (u : Multiplicative X →* Γ(G.left, U)ˣ) (hu : ∀ χ, IsWt i _ (u (Multiplicative.ofAdd χ)).val χ) :
    ∃ τ : opn U ⟶ splitTorus S X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g g' : Z ⟶ opn U),
      g' ≫ opnι U = (t ≫ i) * (g ≫ opnι U) → g' ≫ τ = t * (g ≫ τ) := by
  let τ : opn U ⟶ splitTorus S X := (splitTorusPointsEquiv S X (opn U)).symm
    ((Units.map U.topIso.inv.hom.toMonoidHom).comp u)
  have hτ₀ : ∀ χ : X, τ.left.appTop.hom (charUnit S X χ).val =
      U.topIso.inv.hom (u (Multiplicative.ofAdd χ)).val := by
    intro χ
    rw [← splitTorusPointsEquiv_val, MulEquiv.apply_symm_apply]
    rfl
  have hle : ∀ {Z : Over S} (g : Z ⟶ opn U), ⊤ ≤ (g ≫ opnι U).left ⁻¹ᵁ U := by
    intro Z g x _
    exact (g.left x).2
  have hτ₁ : ∀ {Z : Over S} (g : Z ⟶ opn U) (χ : X), (g ≫ τ).left.appTop.hom (charUnit S X χ).val =
      ((g ≫ opnι U).left.appLE U ⊤ (hle g)).hom (u (Multiplicative.ofAdd χ)).val := by
    intro Z g χ
    let g' : Z.left ⟶ U := g.left
    have h : U.topIso.inv ≫ g'.appTop = (g' ≫ U.ι).appLE U ⊤ (hle g) := by
      rw [← Scheme.Hom.appLE_comp_appLE g' U.ι U ⊤ ⊤ (by simp) (by simp), Scheme.Hom.appTop,
        Scheme.Hom.app_eq_appLE, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
      rfl
    change g'.appTop.hom (τ.left.appTop.hom (charUnit S X χ).val) = _
    rw [hτ₀]
    exact congrArg (fun f => f.hom (u (Multiplicative.ofAdd χ)).val) h
  refine ⟨τ, fun Z t g g' hg => ?_⟩
  apply (splitTorusPointsEquiv S X Z).injective
  rw [map_mul]
  ext χ
  change (splitTorusPointsEquiv S X Z _ (Multiplicative.ofAdd χ)).val =
    (splitTorusPointsEquiv S X Z _ (Multiplicative.ofAdd χ)).val *
    (splitTorusPointsEquiv S X Z _ (Multiplicative.ofAdd χ)).val
  rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, hτ₁, hτ₁,
    TorusInj.appLE_of_eq (congrArg Over.Hom.left hg)]
  exact hu χ Z t (g ≫ opnι U) _ _
end GlobalTheory.EquivDesc
