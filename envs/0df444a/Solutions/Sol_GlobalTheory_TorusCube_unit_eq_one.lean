-- Prove2me | solution 1 for GlobalTheory.TorusCube.unit_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:00:00.066577+00:00
-- url     : https://prove2.me/submissions/d68eb369-7536-4572-96ad-eac392d58164

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SplitTorusGenCubical
import Theorems.Thm_GlobalTheory_TorusCube_toHom_one
import Theorems.Thm_GlobalTheory_TorusCube_exists_form
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torus_const_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torus_const_mul_chi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineX
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineY
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusCube
open Rosenlicht SplitTorusPoints Geo.Tor
namespace GlobalTheory.TorusCube
theorem _root_.solution (k : Type) [Field k] (X : Type) [AddCommGroup X] [TwoUniqueSums (X × X × X)]
    (w : Γ((splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X ⊗
      splitTorus (Spec (.of k)) X).left, ⊤)) (hw : IsUnit w)
    (h₀ : (lift (𝟙 _) (lift 1 1) : splitTorus (Spec (.of k)) X ⟶
      splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X).left.appTop.hom w = 1)
    (h₁ : (lift 1 (lift (𝟙 _) 1) : splitTorus (Spec (.of k)) X ⟶
      splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X).left.appTop.hom w = 1)
    (h₂ : (lift 1 (lift 1 (𝟙 _)) : splitTorus (Spec (.of k)) X ⟶
      splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X).left.appTop.hom w = 1)
    (Z : Over (Spec (.of k))) (x y u : Z ⟶ splitTorus (Spec (.of k)) X) :
    (lift x (lift y u)).left.appTop.hom w = 1 := by
  obtain ⟨c, a, b, d, hc, H⟩ := exists_form k X w hw
  rw [H] at h₀ h₁ h₂
  simp only [toHom_one, MonoidHom.one_apply, Units.val_one, _root_.mul_one, _root_.one_mul]
    at h₀ h₁ h₂
  have ha : a = 0 := torus_const_mul_chi k X (c₂ := 1) hc (h₀.trans (map_one _).symm)
  have hb : b = 0 := torus_const_mul_chi k X (c₂ := 1) hc (h₁.trans (map_one _).symm)
  have hd : d = 0 := torus_const_mul_chi k X (c₂ := 1) hc (h₂.trans (map_one _).symm)
  subst ha hb hd
  have hc1 : c = 1 := torus_const_injective k X (by simpa using h₀)
  rw [H, hc1]
  simp
end GlobalTheory.TorusCube
