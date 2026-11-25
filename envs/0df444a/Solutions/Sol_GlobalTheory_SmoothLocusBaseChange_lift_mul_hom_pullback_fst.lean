-- Prove2me | solution 1 for GlobalTheory.SmoothLocusBaseChange.lift_mul_hom_pullback_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:17:13.454169+00:00
-- url     : https://prove2.me/submissions/c44858a1-bea4-4078-a488-18e9d566daa1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LiftMulHomPullbackFst
import Theorems.Thm_GlobalTheory_SmoothLocusBaseChange_lift_mul_pullback_fst
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
    {E : Over S'} [MonObj E] (q : E ⟶ (Over.pullback φ).obj G) [IsMonHom q]
    {Z : Over S'} (x y : Z ⟶ E) {Z₀ : Over S} (i : Z₀.left ⟶ Z.left)
    (a b : Z₀ ⟶ G) (ha : a.left = i ≫ x.left ≫ q.left ≫ pullback.fst _ _)
    (hb : b.left = i ≫ y.left ≫ q.left ≫ pullback.fst _ _) :
    (lift a b ≫ μ[G]).left =
      i ≫ (lift x y ≫ μ[E]).left ≫ q.left ≫ pullback.fst _ _ := by
  rw [lift_mul_pullback_fst φ G (x ≫ q) (y ≫ q) i a b (by simpa using ha) (by simpa using hb)]
  have : lift (x ≫ q) (y ≫ q) ≫ μ[(Over.pullback φ).obj G] = (lift x y ≫ μ[E]) ≫ q := by
    rw [Category.assoc, IsMonHom.mul_hom, lift_map_assoc]
  rw [this, Over.comp_left, Category.assoc]
end GlobalTheory.SmoothLocusBaseChange
