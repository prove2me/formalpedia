-- Prove2me | solution 1 for GlobalTheory.SmoothLocusBaseChange.lift_mul_pullback_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:02:47.812484+00:00
-- url     : https://prove2.me/submissions/db078aaa-ea45-4c01-89f8-945c1480ece1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LiftMulHomPullbackFst
import Theorems.Thm_GlobalTheory_ProjPoint_hom_ext
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
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
open GlobalTheory GlobalTheory.SmoothLocusBaseChange
namespace GlobalTheory.SmoothLocusBaseChange
theorem _root_.solution {S S' : Scheme.{0}} (φ : S' ⟶ S) (G : Over S) [GrpObj G]
    {Z : Over S'} (x y : Z ⟶ (Over.pullback φ).obj G) {Z₀ : Over S} (i : Z₀.left ⟶ Z.left)
    (a b : Z₀ ⟶ G) (ha : a.left = i ≫ x.left ≫ pullback.fst _ _)
    (hb : b.left = i ≫ y.left ≫ pullback.fst _ _) :
    (lift a b ≫ μ[G]).left =
      i ≫ (lift x y ≫ μ[(Over.pullback φ).obj G]).left ≫ pullback.fst _ _ := by
  have key : (lift a b).left = i ≫ (lift x y).left ≫
      (Functor.LaxMonoidal.μ (Over.pullback φ) G G).left ≫ pullback.fst (G ⊗ G).hom φ := by
    apply pullback.hom_ext
    · have h1 : (lift a b).left ≫ pullback.fst _ _ = a.left := congrArg (·.left) (lift_fst a b)
      have h2 : (lift x y).left ≫ pullback.fst _ _ = x.left := congrArg (·.left) (lift_fst x y)
      refine (h1.trans ha).trans ?_
      rw [← h2]
      simp only [Category.assoc]
      erw [Over.μ_pullback_left_fst_fst]
    · have h1 : (lift a b).left ≫ pullback.snd _ _ = b.left := congrArg (·.left) (lift_snd a b)
      have h2 : (lift x y).left ≫ pullback.snd _ _ = y.left := congrArg (·.left) (lift_snd x y)
      refine (h1.trans hb).trans ?_
      rw [← h2]
      simp only [Category.assoc]
      erw [Over.μ_pullback_left_fst_snd]
  rw [Over.comp_left, key]
  simp only [Functor.obj.μ_def, Over.comp_left, Category.assoc, Over.pullback_map_left]
  erw [pullback.lift_fst]
end GlobalTheory.SmoothLocusBaseChange
