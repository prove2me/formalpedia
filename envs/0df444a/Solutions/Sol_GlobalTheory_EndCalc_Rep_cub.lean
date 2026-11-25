-- Prove2me | solution 1 for GlobalTheory.EndCalc.Rep.cub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:03:43.976468+00:00
-- url     : https://prove2.me/submissions/b09f0b4a-89b8-4e5a-9d54-76da9dbdb0b9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConnectedSpaceThickening
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniformizationEndomorphismOfLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UniformizationEndomorphismCalculus
import Theorems.Thm_GlobalTheory_Cartier_SecMaps_isGen
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_symm_zeroOver
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_some
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_toAffineLift
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_zero
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_symm_zeroOver
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub
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
attribute [local simp] GlobalTheory.WeierstrassCurve.affinePointEquiv_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.affinePointEquiv_symm_zeroOver
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_some
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_toAffineLift
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_zero
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ
attribute [local simp] GlobalTheory.WeierstrassCurve.projectivePointEquiv_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.projectivePointEquiv_symm_zeroOver



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.EndCalc
variable {R : Type} [CommRing R] [IsDomain R]
open FreeAbelianGroup
variable {D : DegPre R} {T₀ : Over (Spec (CommRingCat.of R))}
namespace GlobalTheory.EndCalc
namespace Rep
theorem _root_.solution (x x' y : T₀ ⟶ D.P.A) :
    Rep (of (x * x' * y) - of (x * x') - of (x * y) - of (x' * y) + of x + of x' + of y - of 1)
      fun _ ρ z J => th D z J (ρ ≫ x) (ρ ≫ x') (ρ ≫ y) := by
  refine ⟨thK, inferInstance, _, _, LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift x (lift x' y)).left,
    pullGen_isGen _ _ _ _ D.cub.isGen _, fun U _ h => (prod_cub x x' y h).trans ?_,
    fun T ρ z J hJ => val_cub D.cub ρ hJ _ _ _⟩
  simp only [map_add, map_sub, lift_apply_of, toMul_add, toMul_sub, toMul_ofMul, div_eq_mul_inv]
end Rep
end GlobalTheory.EndCalc
