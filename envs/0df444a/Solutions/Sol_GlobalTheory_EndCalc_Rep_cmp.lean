-- Prove2me | solution 1 for GlobalTheory.EndCalc.Rep.cmp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:00:05.054344+00:00
-- url     : https://prove2.me/submissions/614beaec-10ce-412f-b5be-2bfcdf977094

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
import Theorems.Thm_P2M_GlobalTheory_UT_OLinEnd_prod_O__7772f5470651
import Theorems.Thm_P2M_GlobalTheory_UT_OLinEnd_prod_O__inv_e4161887929d
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_O__comp_24bcd133e28a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull
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
theorem _root_.solution {a : D.P.A ⟶ D.P.A} {p χ : D.X} {u : CmpGen D a p χ} (hu : Normd u) (x : T₀ ⟶ D.P.A) :
    Rep (of (cP D T₀ p * x) - of (cP D T₀ p) - of x - of (cP D T₀ χ * (x ≫ a)) + of (cP D T₀ χ) + of (x ≫ a))
      fun _ ρ z J => val u (ρ ≫ x).left z J := by
  refine ⟨Fin 4 ⊕ Fin 4, inferInstance, _, _, LB.pullGen D.P.L _ _ u x.left, pullGen_isGen _ _ _ _ hu.1 _,
    fun U _ h => ?_, fun T ρ z J hJ => val_pull hJ _ _ _⟩
  refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
    ((Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ Oε k) (WeightPf.Oφ_comp x (𝟙 _) p k)).trans
      (OLinEnd.prod_Oφ D _ p h))
    ((Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ Oinvε k) (WeightPf.Oφ_comp x a χ k)).trans
      (OLinEnd.prod_Oφ_inv D _ χ h))).trans ?_
  rw [Category.comp_id]
  apply Additive.ofMul.injective
  simp only [map_add, map_sub, lift_apply_of, ofMul_mul, ofMul_inv, ofMul_toMul]
  abel
end Rep
end GlobalTheory.EndCalc
