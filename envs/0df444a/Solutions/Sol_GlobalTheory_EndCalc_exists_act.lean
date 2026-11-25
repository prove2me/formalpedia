-- Prove2me | solution 1 for GlobalTheory.EndCalc.exists_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:54:44.180695+00:00
-- url     : https://prove2.me/submissions/62a84976-1061-4a57-9671-12538ef38c20

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
import Theorems.Thm_GlobalTheory_EndCalc_cmp_zero
import Theorems.Thm_GlobalTheory_EndCalc_cmp_add_char
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm
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
import Theorems.Thm_P2M_GlobalTheory_UT_OLinEnd_prod_O__7772f5470651
import Theorems.Thm_P2M_GlobalTheory_UT_OLinEnd_prod_O__inv_e4161887929d
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_O__comp_24bcd133e28a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_gt
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
open GlobalTheory.TorusExt
variable {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G}
variable {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.EndCalc
theorem _root_.solution (hG : GlobalFnsSt) (E : EndU U) (g : GtPtF D.toPre F) : ∃ g', E.Act g g' := by
  have := E.homB
  have vv : ∀ χ y J, Good D.toPre.P.L y J → val (LB.mulGen D.toPre.P.L _ _ _ _ (g.s (E.h χ))
      (LB.pullGen D.toPre.P.L _ _ (E.u χ) g.b.left)) (𝟙 (TF (R := R) F).left) y J =
      charVal g (E.h χ) y J * val (E.u χ) g.b.left y J := fun χ y J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (by rw [Category.id_comp])))
  obtain ⟨g', hb, hv⟩ := exists_gt (g.b ≫ E.aB) (fun χ => LB.mulGen D.toPre.P.L _ _ _ _ (g.s (E.h χ))
      (LB.pullGen D.toPre.P.L _ _ (E.u χ) g.b.left))
    (fun χ => mulGen_isGen _ _ _ _ _ _ _ (g.isGen _) (pullGen_isGen _ _ _ _ (E.u_norm χ).1 _)) (fun χ V _ h => by
      refine (prod_sum₂ (K := Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := V) _ (prod_gt g.b (E.h χ) h)
        (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := V) _
          ((Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ Oε k)
            (WeightPf.Oφ_comp g.b (𝟙 _) (E.h χ) k)).trans (OLinEnd.prod_Oφ D.toPre _ (E.h χ) h))
          ((Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ Oinvε k)
            (WeightPf.Oφ_comp g.b E.aB χ k)).trans (OLinEnd.prod_Oφ_inv D.toPre _ χ h)))).trans ?_
      rw [prod_gt, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (fun y J hJ => by
      refine (vv 0 y J hJ).trans ?_
      rw [cmp_zero hG (E.u_norm 0) (map_zero _) rfl hJ, map_zero, charVal_zero g hJ, _root_.mul_one])
    (fun χ χ' y J hJ => by
      have e₁ := congrArg Additive.ofMul
        (cmp_add_char hG (E.u_norm χ) (E.u_norm χ') (E.u_norm (χ + χ')) (map_add _ _ _) hJ g.b)
      have e₂ := charVal_add g hJ (E.h χ) (E.h χ')
      rw [← map_add] at e₂
      have e₃ := congrArg Additive.ofMul e₂
      refine (congrArg₂ (· * ·) (vv _ y J hJ) rfl).trans (Eq.trans ?_ (congrArg₂ (· * ·) (vv _ y J hJ) (vv _ y J hJ)).symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul] at e₁ e₃ ⊢
      linear_combination (norm := abel) e₁ + e₃)
  exact ⟨g', hb, fun χ y J hJ => (hv χ y J hJ).trans (vv χ y J hJ)⟩
end GlobalTheory.EndCalc
