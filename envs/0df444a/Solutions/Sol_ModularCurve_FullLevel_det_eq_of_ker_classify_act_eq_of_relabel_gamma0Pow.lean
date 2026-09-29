-- Prove2me | solution 1 for ModularCurve.FullLevel.det_eq_of_ker_classify_act_eq_of_relabel_gamma0Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/a68adb60-e4bb-5b2e-bd79-ba4d50f00ae6

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_EllipticCurve_WeilPairingFun
import Theorems.Thm_WeierstrassCurve_Affine_weilPairing0_linComb_linComb_eq_zpow_det
import Theorems.Thm_ModularCurve_LevelRelabelling_toPoint_relabel_eq_zsmul_add_zsmul
import Theorems.Thm_ModularCurve_LevelRelabelling_relabel_map_eq_map_relabel
import Theorems.Thm_ModularCurve_LevelModuliPackageAbs_weilPairing0_mapRing_eq_of_ker_classify_eq_rigidDataPow
import Theorems.Thm_ModularCurve_IsLevelPStructure_relabel_of_isUnit_det
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_zlinComb_zlinComb_of_isUnit_det
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_GroupLaws_mul_comm_of_isOriginIdentity
import Theorems.Thm_ModularCurve_IsLevelPStructure_exists_eq_nsmul_add_nsmul_of_isLevelPStructure
import Theorems.Thm_WeierstrassCurve_Affine_weilPairing0_add_left
import Theorems.Thm_WeierstrassCurve_Affine_weilPairing0_add_right
import Theorems.Thm_WeierstrassCurve_Affine_weilPairing0_self
import Theorems.Thm_WeierstrassCurve_Affine_eq_zero_of_forall_weilPairing0_eq_one
import Theorems.Thm_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Theorems.Thm_ModularCurve_isUnit_indepElt_symm
import Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import Theorems.Thm_ModularCurve_LevelModuliPackageAbs_weilPairing0_drinfeld_mapRing_eq_of_ker_classify_eq_rigidDataPow
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_LevelTransport_map_relabel_eq_relabel_map
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPrimitiveRoot_weilPairing0_of_isLevel_of_isSectionThrough_ed2
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_zlinComb_of_isSectionThrough
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_IsLevel_exists_isSectionThrough_of_isUnit
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_iff_eval_prePsi_eq_zero_of_isSectionThrough
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_nsmul_eq_one_and_nsmul_eq_one
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_IsLevel_isUnit_indepElt_of_isSectionThrough
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_det_eq_of_ker_classify_act_eq_of_relabel_gamma0Pow
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_zero WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.RelativeGroupLaw.actionSndPoint_coe GoodReductionJacobian.RelativeGroupLaw.actionFstPoint_coe"

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.LevelRelabelling WeierstrassCurve WeierstrassCurve.Affine
open CategoryTheory AlgebraicGeometry WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

namespace C2dSol

section Torsion

variable {G : Type*} [AddCommGroup G]

theorem torsion_nsmul {n : ℕ} {S : G} (h : (n : ℤ) • S = 0) (m : ℕ) : (n : ℤ) • (m • S) = 0 := by
  rw [← natCast_zsmul, smul_smul, mul_comm, ← smul_smul, h, smul_zero]

theorem torsion_add {n : ℕ} {S T : G} (hS : (n : ℤ) • S = 0) (hT : (n : ℤ) • T = 0) :
    (n : ℤ) • (S + T) = 0 := by
  rw [smul_add, hS, hT, add_zero]

theorem zsmul_eq_val_nsmul {ℓ : ℕ} [NeZero ℓ] {P : G} (hP : (ℓ : ℤ) • P = 0) {z : ℤ} {a : ZMod ℓ}
    (hz : (z : ZMod ℓ) = a) : z • P = a.val • P := by
  have h1 : (z : ZMod ℓ) = ((a.val : ℤ) : ZMod ℓ) := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]; exact hz
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  obtain ⟨k, hk⟩ := h1
  have hz' : z = (a.val : ℤ) + (ℓ : ℤ) * (-k) := by linarith
  rw [hz', add_zsmul, natCast_zsmul, mul_comm, ← smul_smul, hP, smul_zero, add_zero]

theorem exists_nsmul_eq_of_zsmul {ℓ : ℕ} [NeZero ℓ] {P : G} (hP : (ℓ : ℤ) • P = 0) (k : ℤ) :
    ∃ m : ℕ, k • P = m • P := by
  refine ⟨((k : ZMod ℓ)).val, ?_⟩
  exact zsmul_eq_val_nsmul hP rfl

end Torsion

section Pairing

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K]
  (W : WeierstrassCurve F) [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing]
  {n : ℕ} (hn : (n : K) ≠ 0)

include hn

theorem pair_zero_left (T : (W⁄K).Point) (hT : (n : ℤ) • T = 0) : weilPairing0 W K n 0 T = 1 := by
  have h := weilPairing0_add_left W hn 0 0 T (smul_zero _) (smul_zero _) hT
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem pair_zero_right (S : (W⁄K).Point) (hS : (n : ℤ) • S = 0) : weilPairing0 W K n S 0 = 1 := by
  have h := weilPairing0_add_right W hn S 0 0 hS (smul_zero _) (smul_zero _)
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem pair_nsmul_left (m : ℕ) (S T : (W⁄K).Point) (hS : (n : ℤ) • S = 0) (hT : (n : ℤ) • T = 0) :
    weilPairing0 W K n (m • S) T = weilPairing0 W K n S T ^ m := by
  induction m with
  | zero => rw [zero_nsmul, pow_zero, pair_zero_left W hn T hT]
  | succ m ih =>
    rw [succ_nsmul, weilPairing0_add_left W hn _ _ _ (torsion_nsmul hS m) hS hT, ih, pow_succ]

theorem pair_nsmul_right (m : ℕ) (S T : (W⁄K).Point) (hS : (n : ℤ) • S = 0) (hT : (n : ℤ) • T = 0) :
    weilPairing0 W K n S (m • T) = weilPairing0 W K n S T ^ m := by
  induction m with
  | zero => rw [zero_nsmul, pow_zero, pair_zero_right W hn S hS]
  | succ m ih =>
    rw [succ_nsmul, weilPairing0_add_right W hn _ _ _ hS (torsion_nsmul hT m) hT, ih, pow_succ]

theorem pair_swap (S T : (W⁄K).Point) (hS : (n : ℤ) • S = 0) (hT : (n : ℤ) • T = 0) :
    weilPairing0 W K n T S = (weilPairing0 W K n S T)⁻¹ := by
  have h := weilPairing0_self W hn (S + T) (torsion_add hS hT)
  rw [weilPairing0_add_left W hn S T (S + T) hS hT (torsion_add hS hT),
    weilPairing0_add_right W hn S S T hS hS hT, weilPairing0_add_right W hn T S T hT hS hT,
    weilPairing0_self W hn S hS, weilPairing0_self W hn T hT, one_mul, mul_one] at h
  exact eq_inv_of_mul_eq_one_right h

theorem pair_lincomb (a b c d : ℕ) (P Q : (W⁄K).Point) (hP : (n : ℤ) • P = 0) (hQ : (n : ℤ) • Q = 0) :
    weilPairing0 W K n (a • P + b • Q) (c • P + d • Q) =
      weilPairing0 W K n P Q ^ (a * d) * (weilPairing0 W K n P Q ^ (b * c))⁻¹ := by
  have hQ' : (n : ℤ) • (c • P + d • Q) = 0 := torsion_add (torsion_nsmul hP c) (torsion_nsmul hQ d)
  rw [weilPairing0_add_left W hn _ _ _ (torsion_nsmul hP a) (torsion_nsmul hQ b) hQ',
    pair_nsmul_left W hn a P _ hP hQ', pair_nsmul_left W hn b Q _ hQ hQ',
    weilPairing0_add_right W hn P _ _ hP (torsion_nsmul hP c) (torsion_nsmul hQ d),
    weilPairing0_add_right W hn Q _ _ hQ (torsion_nsmul hP c) (torsion_nsmul hQ d),
    pair_nsmul_right W hn c P P hP hP, pair_nsmul_right W hn d P Q hP hQ,
    pair_nsmul_right W hn c Q P hQ hP, pair_nsmul_right W hn d Q Q hQ hQ,
    weilPairing0_self W hn P hP, weilPairing0_self W hn Q hQ, one_pow, one_mul, one_pow, mul_one,
    pair_swap W hn P Q hP hQ, ← pow_mul, ← pow_mul, inv_pow, mul_comm d a, mul_comm c b]

theorem pair_pow_eq_one (P Q : (W⁄K).Point) (hP : (n : ℤ) • P = 0) (hQ : (n : ℤ) • Q = 0) :
    weilPairing0 W K n P Q ^ n = 1 := by
  rw [← pair_nsmul_left W hn n P Q hP hQ, ← natCast_zsmul, hP, pair_zero_left W hn Q hQ]

end Pairing

section Span

variable {K : Type u} [Field K] [DecidableEq K] (V : WeierstrassCurve K) [V.IsElliptic]
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓK : (ℓ : K) ≠ 0)

include hℓ3 in
theorem odd_ell : Odd ℓ :=
  (Fact.out : ℓ.Prime).odd_of_ne_two (by omega)

omit [Fact ℓ.Prime] in
include hℓ3 in
theorem ell_ne_two : ℓ ≠ 2 := by omega

omit [DecidableEq K] [V.IsElliptic] in
theorem toPoint_eq_some {x y : K} (h : V.toAffine.Nonsingular x y) :
    toPoint V x y = Point.some x y h := by
  unfold toPoint
  rw [dif_pos h]

include hℓ3 in

theorem zsmul_some_eq_zero {D : LevelPData K} (hD : IsLevelPStructure V ℓ D)
    (nP : V.toAffine.Nonsingular D.xP D.yP) : (ℓ : ℤ) • Point.some D.xP D.yP nP = 0 := by
  rw [natCast_zsmul]
  apply (Point.nsmul_some_eq_zero_iff_eval_prePsi V (odd_ell ℓ hℓ3) nP).mpr
  rw [← WeierstrassCurve.preΨ_ofNat]
  exact hD.preΨ_P

include hℓ3 hℓK in

theorem exists_eq_lincomb {D : LevelPData K} (hD : IsLevelPStructure V ℓ D)
    (nP : V.toAffine.Nonsingular D.xP D.yP) (nQ : V.toAffine.Nonsingular D.xQ D.yQ)
    (S : V.toAffine.Point) (hS : (ℓ : ℤ) • S = 0) :
    ∃ i j : ℕ, S = i • Point.some D.xP D.yP nP + j • Point.some D.xQ D.yQ nQ := by
  have hΔ : IsUnit V.Δ := WeierstrassCurve.isUnit_Δ V
  have hℓP : (ℓ : ℤ) • Point.some D.xP D.yP nP = 0 := zsmul_some_eq_zero V ℓ hℓ3 hD nP
  have hℓPn : ℓ • Point.some D.xP D.yP nP = 0 := by rw [← natCast_zsmul]; exact hℓP
  rcases S with _ | ⟨x, y, h⟩
  · exact ⟨0, 0, by rw [← Point.zero_def, zero_nsmul, zero_nsmul, add_zero]⟩
  by_cases hmem : Point.some x y h ∈ AddSubgroup.zmultiples (Point.some D.xP D.yP nP)
  · obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    obtain ⟨m, hm⟩ := exists_nsmul_eq_of_zsmul (ℓ := ℓ) hℓP k
    exact ⟨m, 0, by rw [zero_nsmul, add_zero, ← hm, hk]⟩
  ·
    have hSn : ℓ • Point.some x y h = 0 := by rw [← natCast_zsmul]; exact hS
    have hψS : (V.preΨ (ℓ : ℤ)).eval x = 0 := by
      rw [WeierstrassCurve.preΨ_ofNat]
      exact (Point.nsmul_some_eq_zero_iff_eval_prePsi V (odd_ell ℓ hℓ3) h).mp hSn
    have hind : IsUnit (indepElt V ℓ D.xP x) := by
      rw [isUnit_iff_ne_zero]
      intro h0
      exact hmem ((indepElt_eq_zero_iff_mem_zmultiples (ell_ne_two ℓ hℓ3) nP h hℓPn).mp h0)
    have hind' : IsUnit (indepElt V ℓ x D.xP) :=
      isUnit_indepElt_symm V ℓ (ell_ne_two ℓ hℓ3) (isUnit_iff_ne_zero.mpr hℓK) hΔ hD.equation_P h.left
        hD.preΨ_P hψS hind
    have hDS : IsLevelPStructure V ℓ ⟨D.xP, D.yP, x, y⟩ :=
      { equation_P := hD.equation_P
        equation_Q := h.left
        preΨ_P := hD.preΨ_P
        preΨ_Q := hψS
        isUnit_indepElt_PQ := hind
        isUnit_indepElt_QP := hind' }
    obtain ⟨_, _, _, _, a, b, c, d, -, -, hcd⟩ :=
      IsLevelPStructure.exists_eq_nsmul_add_nsmul_of_isLevelPStructure ℓ hℓ3 hℓK V hΔ D _ hD hDS
    exact ⟨c.val, d.val, hcd⟩

end Span

section Det

theorem isUnit_det_of_dvd {m n : ℕ} (h : m ∣ n) (g : Matrix (Fin 2) (Fin 2) ℤ)
    (hg : IsUnit (g.map (Int.castRingHom (ZMod n))).det) : IsUnit ((g.det : ℤ) : ZMod m) := by
  have e : (g.map (Int.castRingHom (ZMod n))).det = ((g.det : ℤ) : ZMod n) := by
    rw [show g.map (Int.castRingHom (ZMod n)) = (Int.castRingHom (ZMod n)).mapMatrix g from rfl, ← RingHom.map_det]
    rfl
  rw [e] at hg
  have := hg.map (ZMod.castHom h (ZMod m))
  rwa [map_intCast] at this

theorem not_dvd_col {ℓ : ℕ} (hℓ : 1 < ℓ) (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit ((g.det : ℤ) : ZMod ℓ)) (j : Fin 2) :
    ¬ ((ℓ : ℤ) ∣ g 0 j ∧ (ℓ : ℤ) ∣ g 1 j) := by
  rintro ⟨h0, h1⟩
  have hdvd : (ℓ : ℤ) ∣ g.det := by
    rw [Matrix.det_fin_two]
    fin_cases j
    · exact dvd_sub (dvd_mul_of_dvd_left h0 _) (dvd_mul_of_dvd_right h1 _)
    · exact dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_left h0 _)
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd] at hg
  haveI : Nontrivial (ZMod ℓ) := ZMod.nontrivial_iff.mpr hℓ.ne'
  exact not_isUnit_zero hg

end Det

section Indep

variable {K : Type u} [Field K] [DecidableEq K] (V : WeierstrassCurve K) [V.IsElliptic]
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)

omit [V.IsElliptic] [Fact ℓ.Prime] in

theorem mem_zmultiples_of_zsmul_add_zsmul_eq_zero (hℓ : Prime (ℓ : ℤ)) {P' Q' : V.toAffine.Point}
    (hQ' : (ℓ : ℤ) • Q' = 0) {a b : ℤ} (h : a • P' + b • Q' = 0) (hb : ¬ (ℓ : ℤ) ∣ b) :
    Q' ∈ AddSubgroup.zmultiples P' := by
  obtain ⟨u, v, huv⟩ := (Prime.coprime_iff_not_dvd hℓ).mpr hb

  refine AddSubgroup.mem_zmultiples_iff.mpr ⟨-(v * a), ?_⟩
  have h1 : v • (a • P' + b • Q') = 0 := by rw [h, smul_zero]
  rw [smul_add, smul_smul, smul_smul] at h1
  have h2 : (v * b) • Q' = Q' := by
    rw [show v * b = 1 - u * ℓ by linear_combination huv, sub_smul, one_smul, ← smul_smul, hQ', smul_zero, sub_zero]
  rw [h2] at h1
  rw [neg_smul]
  exact add_eq_zero_iff_neg_eq.mp h1

include hℓ3 in

theorem zsmul_add_zsmul_ne_zero {D : LevelPData K} (hD : IsLevelPStructure V ℓ D)
    (nP : V.toAffine.Nonsingular D.xP D.yP) (nQ : V.toAffine.Nonsingular D.xQ D.yQ)
    (a b : ℤ) (hab : ¬ ((ℓ : ℤ) ∣ a ∧ (ℓ : ℤ) ∣ b)) :
    a • Point.some D.xP D.yP nP + b • Point.some D.xQ D.yQ nQ ≠ 0 := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hℓP : (ℓ : ℤ) • Point.some D.xP D.yP nP = 0 := zsmul_some_eq_zero V ℓ hℓ3 hD nP
  have hℓQ : (ℓ : ℤ) • Point.some D.xQ D.yQ nQ = 0 := zsmul_some_eq_zero V ℓ hℓ3 hD.swap nQ
  have hℓPn : ℓ • Point.some D.xP D.yP nP = 0 := by rw [← natCast_zsmul]; exact hℓP
  have hℓQn : ℓ • Point.some D.xQ D.yQ nQ = 0 := by rw [← natCast_zsmul]; exact hℓQ
  have hQP : Point.some D.xQ D.yQ nQ ∉ AddSubgroup.zmultiples (Point.some D.xP D.yP nP) := fun hmem =>
    (isUnit_iff_ne_zero.mp hD.isUnit_indepElt_PQ)
      ((indepElt_eq_zero_iff_mem_zmultiples (ell_ne_two ℓ hℓ3) nP nQ hℓPn).mpr hmem)
  have hPQ : Point.some D.xP D.yP nP ∉ AddSubgroup.zmultiples (Point.some D.xQ D.yQ nQ) := fun hmem =>
    (isUnit_iff_ne_zero.mp hD.isUnit_indepElt_QP)
      ((indepElt_eq_zero_iff_mem_zmultiples (ell_ne_two ℓ hℓ3) nQ nP hℓQn).mpr hmem)
  intro h0
  by_cases hb : (ℓ : ℤ) ∣ b
  · have ha : ¬ (ℓ : ℤ) ∣ a := fun ha => hab ⟨ha, hb⟩
    rw [add_comm] at h0
    exact hPQ (mem_zmultiples_of_zsmul_add_zsmul_eq_zero V ℓ hprime hℓP h0 ha)
  · exact hQP (mem_zmultiples_of_zsmul_add_zsmul_eq_zero V ℓ hprime hℓQ h0 hb)

end Indep

section EllCore

variable {K : Type u} [Field K] (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra K Ω]
  (W : WeierstrassCurve K) [W.IsElliptic]
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓK : (ℓ : K) ≠ 0)

include hℓ3 hℓK in
theorem det_eq_of_weilPairing0_relabel_eq (D : LevelPData K) (hD : IsLevelPStructure W ℓ D)
    (g₁ g₂ : Matrix (Fin 2) (Fin 2) ℤ) (hg₁ : IsUnit ((g₁.det : ℤ) : ZMod ℓ)) (hg₂ : IsUnit ((g₂.det : ℤ) : ZMod ℓ))
    (h : ((weilPairing0 W Ω ℓ
        (toPoint (W⁄Ω) (algebraMap K Ω (LevelPData.relabel W g₁ D).xP) (algebraMap K Ω (LevelPData.relabel W g₁ D).yP))
        (toPoint (W⁄Ω) (algebraMap K Ω (LevelPData.relabel W g₁ D).xQ) (algebraMap K Ω (LevelPData.relabel W g₁ D).yQ)) : Ωˣ) : Ω) =
      ((weilPairing0 W Ω ℓ
        (toPoint (W⁄Ω) (algebraMap K Ω (LevelPData.relabel W g₂ D).xP) (algebraMap K Ω (LevelPData.relabel W g₂ D).yP))
        (toPoint (W⁄Ω) (algebraMap K Ω (LevelPData.relabel W g₂ D).xQ) (algebraMap K Ω (LevelPData.relabel W g₂ D).yQ)) : Ωˣ) : Ω)) :
    ((g₁.det : ℤ) : ZMod ℓ) = ((g₂.det : ℤ) : ZMod ℓ) := by

  have hdec : ‹DecidableEq Ω› = Classical.decEq Ω := Subsingleton.elim _ _
  subst hdec
  classical
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hℓΩ : (ℓ : Ω) ≠ 0 := fun h0 => hℓK (by
    have : algebraMap K Ω (ℓ : K) = 0 := by rw [map_natCast, h0]
    exact (map_eq_zero_iff _ (algebraMap K Ω).injective).mp this)

  set V : WeierstrassCurve Ω := W⁄Ω with hV
  have hVmap : V = W.map (algebraMap K Ω) := rfl
  haveI hVell : V.IsElliptic := by rw [hVmap]; infer_instance
  haveI : IsDedekindDomain (W⁄Ω).CoordinateRing := WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain V
  set D' : LevelPData Ω := D.map (algebraMap K Ω) with hD'
  have hDV : IsLevelPStructure V ℓ D' := hD.map (algebraMap K Ω)
  have nP : V.toAffine.Nonsingular D'.xP D'.yP := (V.toAffine.equation_iff_nonsingular.mp hDV.equation_P)
  have nQ : V.toAffine.Nonsingular D'.xQ D'.yQ := (V.toAffine.equation_iff_nonsingular.mp hDV.equation_Q)
  set P : (W⁄Ω).Point := Point.some D'.xP D'.yP nP with hPdef
  set Q : (W⁄Ω).Point := Point.some D'.xQ D'.yQ nQ with hQdef
  have htP : toPoint V D'.xP D'.yP = P := toPoint_eq_some _ nP
  have htQ : toPoint V D'.xQ D'.yQ = Q := toPoint_eq_some _ nQ
  have hℓP : (ℓ : ℤ) • P = 0 := zsmul_some_eq_zero V ℓ hℓ3 hDV nP
  have hℓQ : (ℓ : ℤ) • Q = 0 := zsmul_some_eq_zero V ℓ hℓ3 hDV.swap nQ

  have hread : ∀ (g : Matrix (Fin 2) (Fin 2) ℤ), IsUnit ((g.det : ℤ) : ZMod ℓ) →
      toPoint (W⁄Ω) (algebraMap K Ω (LevelPData.relabel W g D).xP) (algebraMap K Ω (LevelPData.relabel W g D).yP) =
        g 0 0 • P + g 1 0 • Q ∧
      toPoint (W⁄Ω) (algebraMap K Ω (LevelPData.relabel W g D).xQ) (algebraMap K Ω (LevelPData.relabel W g D).yQ) =
        g 0 1 • P + g 1 1 • Q := by
    intro g hg
    have e1 : (LevelPData.relabel W g D).map (algebraMap K Ω) = LevelPData.relabel V g D' :=
      (relabel_map_eq_map_relabel (algebraMap K Ω) W g D).symm
    have hx : algebraMap K Ω (LevelPData.relabel W g D).xP = (LevelPData.relabel V g D').xP := by
      rw [← e1, LevelPData.map_xP]
    have hy : algebraMap K Ω (LevelPData.relabel W g D).yP = (LevelPData.relabel V g D').yP := by
      rw [← e1, LevelPData.map_yP]
    have hx' : algebraMap K Ω (LevelPData.relabel W g D).xQ = (LevelPData.relabel V g D').xQ := by
      rw [← e1, LevelPData.map_xQ]
    have hy' : algebraMap K Ω (LevelPData.relabel W g D).yQ = (LevelPData.relabel V g D').yQ := by
      rw [← e1, LevelPData.map_yQ]
    have h1 : g 0 0 • toPoint V D'.xP D'.yP + g 1 0 • toPoint V D'.xQ D'.yQ ≠ 0 := by
      rw [htP, htQ]; exact zsmul_add_zsmul_ne_zero V ℓ hℓ3 hDV nP nQ _ _ (not_dvd_col (by omega) g hg 0)
    have h2 : g 0 1 • toPoint V D'.xP D'.yP + g 1 1 • toPoint V D'.xQ D'.yQ ≠ 0 := by
      rw [htP, htQ]; exact zsmul_add_zsmul_ne_zero V ℓ hℓ3 hDV nP nQ _ _ (not_dvd_col (by omega) g hg 1)
    obtain ⟨r1, r2⟩ := toPoint_relabel_eq_zsmul_add_zsmul V g D' h1 h2
    change toPoint V _ _ = _ ∧ toPoint V _ _ = _
    rw [hx, hy, hx', hy', r1, r2, htP, htQ]
    exact ⟨rfl, rfl⟩
  obtain ⟨a1, b1⟩ := hread g₁ hg₁
  obtain ⟨a2, b2⟩ := hread g₂ hg₂
  rw [a1, b1, a2, b2, weilPairing0_linComb_linComb_eq_zpow_det W hℓΩ P Q hℓP hℓQ g₁,
    weilPairing0_linComb_linComb_eq_zpow_det W hℓΩ P Q hℓP hℓQ g₂] at h
  set e : Ωˣ := weilPairing0 W Ω ℓ P Q with hedef
  have h' : e ^ g₁.det = e ^ g₂.det := Units.ext h

  have hpow : e ^ ℓ = 1 := pair_pow_eq_one W hℓΩ P Q hℓP hℓQ
  have hne : e ≠ 1 := by
    intro he1
    have hQ0 : Q = 0 := by
      refine eq_zero_of_forall_weilPairing0_eq_one W hℓΩ Q hℓQ fun S hS => ?_
      obtain ⟨i, j, rfl⟩ := exists_eq_lincomb V ℓ hℓ3 hℓΩ hDV nP nQ S hS
      rw [weilPairing0_add_left W hℓΩ _ _ _ (torsion_nsmul hℓP i) (torsion_nsmul hℓQ j) hℓQ,
        pair_nsmul_left W hℓΩ i P Q hℓP hℓQ, pair_nsmul_left W hℓΩ j Q Q hℓQ hℓQ,
        weilPairing0_self W hℓΩ Q hℓQ, one_pow, mul_one, ← hedef, he1, one_pow]
    exact Point.some_ne_zero nQ hQ0
  have hprim : IsPrimitiveRoot e ℓ := (orderOf_eq_prime hpow hne) ▸ IsPrimitiveRoot.orderOf e
  have hdvd : (ℓ : ℤ) ∣ g₁.det - g₂.det := by
    rw [← hprim.zpow_eq_one_iff_dvd, zpow_sub, h', mul_inv_cancel]
  exact ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr hdvd).symm

end EllCore

end C2dSol

namespace C2dQ

open scoped Classical

section Helpers

variable {K : Type} [Field K]

theorem nonsingular_of_through (X : WeierstrassCurve.Projective K) [X.IsElliptic] {S : Section X} {x y : K}
    (h : IsSectionThrough S x y) : X.toAffine.Nonsingular x y :=
  X.toAffine.equation_iff_nonsingular.mp
    (((equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough X).1 x y).mpr ⟨S, h⟩)

theorem coords_unique (X : WeierstrassCurve.Projective K) {S : Section X} {x y x' y' : K}
    (h : IsSectionThrough S x y) (h' : IsSectionThrough S x' y') : x = x' ∧ y = y' :=
  ((equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough X).2 S S x y x' y' h h').mp rfl

theorem toPoint_eq_some (X : WeierstrassCurve K) {x y : K} (h : X.toAffine.Nonsingular x y) :
    toPoint X x y = Point.some x y h := dif_pos h

theorem weilPairing0_zero_left (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    (X : WeierstrassCurve K) [X.IsElliptic] [IsDedekindDomain (X⁄Ω).CoordinateRing]
    {n : ℕ} (hn : (n : Ω) ≠ 0) (T : (X⁄Ω).Point) (hT : (n : ℤ) • T = 0) :
    weilPairing0 X Ω n 0 T = 1 := by
  have h := weilPairing0_add_left X hn 0 0 T (by simp) (by simp) hT
  rw [add_zero] at h
  exact mul_left_cancel (a := weilPairing0 X Ω n 0 T) (by rw [← h, mul_one])

end Helpers

section Reading

variable (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
  (q : ℕ) [Fact q.Prime] (hq3 : 3 ≤ q) (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
  {K : Type} [Field K] [Algebra A K] (hqK : ((q : ℕ) : K) ≠ 0)
  (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]

set_option maxHeartbeats 4000000 in
include h𝒢 h𝒢O hq3 h𝒯 hqK in

theorem weil_relabel (x : RawDrinfeldPair K) [x.curve.IsElliptic] (hx : RawDrinfeldPair.IsLevel 𝒢 q x.curve x)
    (hΔ : IsUnit x.curve.Δ) (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit ((g.det : ℤ) : ZMod q))
    (xP yP xQ yQ : K) (hP : IsSectionThrough x.P xP yP) (hQ : IsSectionThrough x.Q xQ yQ)
    (xP' yP' xQ' yQ' : K)
    (hP' : IsSectionThrough (RawDrinfeldPair.relabel 𝒢 g x hΔ).P xP' yP')
    (hQ' : IsSectionThrough (RawDrinfeldPair.relabel 𝒢 g x hΔ).Q xQ' yQ') :
    weilPairing0 x.curve Ω q (toPoint (x.curve⁄Ω) (algebraMap K Ω xP') (algebraMap K Ω yP'))
        (toPoint (x.curve⁄Ω) (algebraMap K Ω xQ') (algebraMap K Ω yQ')) =
      weilPairing0 x.curve Ω q (toPoint (x.curve⁄Ω) (algebraMap K Ω xP) (algebraMap K Ω yP))
        (toPoint (x.curve⁄Ω) (algebraMap K Ω xQ) (algebraMap K Ω yQ)) ^ g.det := by
  classical
  have hqp : q.Prime := Fact.out
  have hq2 : q ≠ 2 := by omega
  have hqodd : Odd q := hqp.odd_of_ne_two hq2
  have hqΩ : ((q : ℕ) : Ω) ≠ 0 := fun h0 => hqK (by
    have : algebraMap K Ω (q : K) = 0 := by rw [map_natCast, h0]
    exact (map_eq_zero_iff _ (algebraMap K Ω).injective).mp this)
  set W := x.curve with hW
  set G := 𝒢 K W hΔ with hG
  haveI : IsDedekindDomain (W⁄Ω).CoordinateRing := by
    haveI : (W⁄Ω).IsElliptic := by
      change (W.map (algebraMap K Ω)).IsElliptic; infer_instance
    exact WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain (W⁄Ω)

  have nP := nonsingular_of_through W hP
  have nQ := nonsingular_of_through W hQ
  set P₀ : W.toAffine.Point := Point.some xP yP nP with hP₀
  set Q₀ : W.toAffine.Point := Point.some xQ yQ nQ with hQ₀
  have htP : toPoint W xP yP = P₀ := toPoint_eq_some W nP
  have htQ : toPoint W xQ yQ = Q₀ := toPoint_eq_some W nQ
  obtain ⟨hΔ', hbasis⟩ := hx.2
  have htors := IsDrinfeldBasis.nsmul_eq_one_and_nsmul_eq_one W (𝒢 K W hΔ') (h𝒢 K W hΔ') q x.P x.Q hbasis
  have hqunit : IsUnit ((q : ℕ) : K) := isUnit_iff_ne_zero.mpr hqK
  have hqP : q • P₀ = 0 := by
    have h1 := (nsmul_eq_one_iff_eval_prePsi_eq_zero_of_isSectionThrough 𝒢 h𝒢 h𝒢O q hq2 K hqunit W hΔ' x.P xP yP hP).mp htors.1
    rw [WeierstrassCurve.preΨ_ofNat] at h1
    exact (Point.nsmul_some_eq_zero_iff_eval_prePsi W hqodd nP).mpr h1
  have hqQ : q • Q₀ = 0 := by
    have h1 := (nsmul_eq_one_iff_eval_prePsi_eq_zero_of_isSectionThrough 𝒢 h𝒢 h𝒢O q hq2 K hqunit W hΔ' x.Q xQ yQ hQ).mp htors.2
    rw [WeierstrassCurve.preΨ_ofNat] at h1
    exact (Point.nsmul_some_eq_zero_iff_eval_prePsi W hqodd nQ).mpr h1

  have hKcol : ∀ a b : ℤ, a • P₀ + b • Q₀ = 0 → (q : ℤ) ∣ a ∧ (q : ℤ) ∣ b := by
    intro a b hab
    obtain ⟨hiPQ, hiQP⟩ := RawDrinfeldPair.IsLevel.isUnit_indepElt_of_isSectionThrough q hq2 A 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 W hqunit
      x hx xP yP xQ yQ hP hQ
    have hQnot : Q₀ ∉ AddSubgroup.zmultiples P₀ := fun hm =>
      hiPQ.ne_zero ((ModularCurve.indepElt_eq_zero_iff_mem_zmultiples hq2 nP nQ hqP).mpr hm)
    have hPnot : P₀ ∉ AddSubgroup.zmultiples Q₀ := fun hm =>
      hiQP.ne_zero ((ModularCurve.indepElt_eq_zero_iff_mem_zmultiples hq2 nQ nP hqQ).mpr hm)
    have hqP' : (q : ℤ) • P₀ = 0 := by rw [natCast_zsmul]; exact hqP
    have hqQ' : (q : ℤ) • Q₀ = 0 := by rw [natCast_zsmul]; exact hqQ

    have hinv : ∀ c : ℤ, ¬ (q : ℤ) ∣ c → ∃ c' k : ℤ, c' * c = 1 + k * q := by
      intro c hc
      have hcop : IsCoprime c (q : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        have := Int.gcd_dvd_right c q
        rcases (Nat.dvd_prime hqp).mp (by exact_mod_cast this) with h1 | h1
        · exact_mod_cast h1
        · exfalso; apply hc
          have := Int.gcd_dvd_left c q
          rw [h1] at this; exact_mod_cast this
      obtain ⟨u, v, huv⟩ := hcop
      exact ⟨u, -v, by linarith⟩
    by_contra hnot
    rcases not_and_or.mp hnot with ha | hb
    ·
      rcases em ((q : ℤ) ∣ b) with hb | hb
      · obtain ⟨k, hk⟩ := hb
        have hb0 : b • Q₀ = 0 := by rw [hk, mul_comm, mul_smul, hqQ', smul_zero]
        rw [hb0, add_zero] at hab
        obtain ⟨a', k', hk'⟩ := hinv a ha
        have : P₀ = 0 := by
          calc P₀ = (1 + k' * q) • P₀ := by rw [add_smul, one_smul, mul_smul, hqP', smul_zero, add_zero]
            _ = a' • (a • P₀) := by rw [smul_smul, hk']
            _ = 0 := by rw [hab, smul_zero]
        exact (Point.some_ne_zero nP) this
      · obtain ⟨b', k', hk'⟩ := hinv b hb
        apply hQnot
        have hbQ : b • Q₀ = -(a • P₀) := eq_neg_of_add_eq_zero_right hab
        have : Q₀ = (b' * -a) • P₀ := by
          calc Q₀ = (1 + k' * q) • Q₀ := by rw [add_smul, one_smul, mul_smul, hqQ', smul_zero, add_zero]
            _ = b' • (b • Q₀) := by rw [smul_smul, hk']
            _ = (b' * -a) • P₀ := by rw [hbQ, ← neg_smul, smul_smul]
        rw [this]; exact AddSubgroup.zsmul_mem_zmultiples P₀ _
    ·
      obtain ⟨b', k', hk'⟩ := hinv b hb
      apply hQnot
      have hbQ : b • Q₀ = -(a • P₀) := eq_neg_of_add_eq_zero_right hab
      have : Q₀ = (b' * -a) • P₀ := by
        calc Q₀ = (1 + k' * q) • Q₀ := by rw [add_smul, one_smul, mul_smul, hqQ', smul_zero, add_zero]
          _ = b' • (b • Q₀) := by rw [smul_smul, hk']
          _ = (b' * -a) • P₀ := by rw [hbQ, ← neg_smul, smul_smul]
      rw [this]; exact AddSubgroup.zsmul_mem_zmultiples P₀ _
  have hdetmod : ((g.det : ℤ) : ZMod q) ≠ 0 := hg.ne_zero
  have hnotcol : ∀ a b c d : ℤ, g.det = a * d - c * b → ¬ ((q : ℤ) ∣ a ∧ (q : ℤ) ∣ b) := by
    rintro a b c d hdet ⟨h1, h2⟩
    apply hdetmod
    rw [hdet, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_sub (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right h2 _)
  have hK1 : g 0 0 • P₀ + g 1 0 • Q₀ ≠ 0 := fun h0 =>
    hnotcol (g 0 0) (g 1 0) (g 0 1) (g 1 1) (by rw [Matrix.det_fin_two]) (hKcol _ _ h0)
  have hK2 : g 0 1 • P₀ + g 1 1 • Q₀ ≠ 0 := fun h0 =>
    hnotcol (g 0 1) (g 1 1) (-g 0 0) (-g 1 0) (by rw [Matrix.det_fin_two]; ring) (hKcol _ _ h0)

  have hread : ∀ (a b : ℤ) (x' y' : K), a • P₀ + b • Q₀ ≠ 0 →
      IsSectionThrough (zlinComb (𝒢 K W hΔ) x.P x.Q a b) x' y' → toPoint W x' y' = a • P₀ + b • Q₀ := by
    intro a b x' y' hne hthr
    generalize hR : a • P₀ + b • Q₀ = R at hne
    rcases R with _ | ⟨xr, yr, hr⟩
    · exact absurd rfl hne
    have h2 := (isSectionThrough_zlinComb_of_isSectionThrough A 𝒢 h𝒢 h𝒢O W hΔ x.P x.Q xP yP xQ yQ hP hQ a b).2
      xr yr hr (by rw [htP, htQ]; exact hR)
    obtain ⟨ex, ey⟩ := coords_unique W hthr h2
    subst ex ey
    exact toPoint_eq_some W hr
  have hRP : toPoint W xP' yP' = g 0 0 • P₀ + g 1 0 • Q₀ := hread _ _ _ _ hK1 hP'
  have hRQ : toPoint W xQ' yQ' = g 0 1 • P₀ + g 1 1 • Q₀ := hread _ _ _ _ hK2 hQ'

  set D : ModularCurve.LevelPData K := ⟨xP, yP, xQ, yQ⟩ with hD
  have nP' := nonsingular_of_through W hP'
  have nQ' := nonsingular_of_through W hQ'
  have hcoP : (LevelPData.relabel W g D).xP = xP' ∧ (LevelPData.relabel W g D).yP = yP' := by
    constructor
    · show (ofPoint W (g 0 0 • toPoint W xP yP + g 1 0 • toPoint W xQ yQ)).1 = xP'
      rw [htP, htQ, ← hRP, toPoint_eq_some W nP']; rfl
    · show (ofPoint W (g 0 0 • toPoint W xP yP + g 1 0 • toPoint W xQ yQ)).2 = yP'
      rw [htP, htQ, ← hRP, toPoint_eq_some W nP']; rfl
  have hcoQ : (LevelPData.relabel W g D).xQ = xQ' ∧ (LevelPData.relabel W g D).yQ = yQ' := by
    constructor
    · show (ofPoint W (g 0 1 • toPoint W xP yP + g 1 1 • toPoint W xQ yQ)).1 = xQ'
      rw [htP, htQ, ← hRQ, toPoint_eq_some W nQ']; rfl
    · show (ofPoint W (g 0 1 • toPoint W xP yP + g 1 1 • toPoint W xQ yQ)).2 = yQ'
      rw [htP, htQ, ← hRQ, toPoint_eq_some W nQ']; rfl

  set V : WeierstrassCurve Ω := W⁄Ω with hV
  haveI hVE : V.IsElliptic := by rw [hV]; change (W.map (algebraMap K Ω)).IsElliptic; infer_instance
  set D' : ModularCurve.LevelPData Ω := D.map (algebraMap K Ω) with hD'
  set P₁ : (W⁄Ω).Point := toPoint V (algebraMap K Ω xP) (algebraMap K Ω yP) with hP₁
  set Q₁ : (W⁄Ω).Point := toPoint V (algebraMap K Ω xQ) (algebraMap K Ω yQ) with hQ₁
  have hinjΩ : Function.Injective (algebraMap K Ω) := (algebraMap K Ω).injective
  have nP₁ : V.toAffine.Nonsingular (algebraMap K Ω xP) (algebraMap K Ω yP) :=
    (WeierstrassCurve.Affine.map_nonsingular (W := W.toAffine) hinjΩ xP yP).mpr nP
  have nQ₁ : V.toAffine.Nonsingular (algebraMap K Ω xQ) (algebraMap K Ω yQ) :=
    (WeierstrassCurve.Affine.map_nonsingular (W := W.toAffine) hinjΩ xQ yQ).mpr nQ
  have hP₁s : P₁ = Point.some _ _ nP₁ := toPoint_eq_some V nP₁
  have hQ₁s : Q₁ = Point.some _ _ nQ₁ := toPoint_eq_some V nQ₁
  have hpreP : (W.preΨ' q).eval xP = 0 := by
    have h1 := (nsmul_eq_one_iff_eval_prePsi_eq_zero_of_isSectionThrough 𝒢 h𝒢 h𝒢O q hq2 K hqunit W hΔ' x.P xP yP hP).mp htors.1
    rwa [WeierstrassCurve.preΨ_ofNat] at h1
  have hpreQ : (W.preΨ' q).eval xQ = 0 := by
    have h1 := (nsmul_eq_one_iff_eval_prePsi_eq_zero_of_isSectionThrough 𝒢 h𝒢 h𝒢O q hq2 K hqunit W hΔ' x.Q xQ yQ hQ).mp htors.2
    rwa [WeierstrassCurve.preΨ_ofNat] at h1
  have hVpre : V.preΨ' q = (W.preΨ' q).map (algebraMap K Ω) := by
    rw [hV]; exact W.map_preΨ' (algebraMap K Ω) q
  have hqP₁ : (q : ℤ) • P₁ = 0 := by
    rw [natCast_zsmul, hP₁s]
    apply (Point.nsmul_some_eq_zero_iff_eval_prePsi V hqodd nP₁).mpr
    rw [hVpre, Polynomial.eval_map, Polynomial.eval₂_at_apply, hpreP, map_zero]
  have hqQ₁ : (q : ℤ) • Q₁ = 0 := by
    rw [natCast_zsmul, hQ₁s]
    apply (Point.nsmul_some_eq_zero_iff_eval_prePsi V hqodd nQ₁).mpr
    rw [hVpre, Polynomial.eval_map, Polynomial.eval₂_at_apply, hpreQ, map_zero]

  have hprim := WeierstrassCurve.DrinfeldGlobal.isPrimitiveRoot_weilPairing0_of_isLevel_of_isSectionThrough_ed2 A 𝒢 h𝒢 h𝒢O q hq3 𝒯 h𝒯 hqK Ω W x hx D hP hQ
  change IsPrimitiveRoot ((weilPairing0 W Ω q P₁ Q₁ : Ωˣ) : Ω) q at hprim
  have hprimU : IsPrimitiveRoot (weilPairing0 W Ω q P₁ Q₁) q := IsPrimitiveRoot.coe_units_iff.mp hprim

  have hcol : ∀ a b : ℤ, a • P₁ + b • Q₁ = 0 → (q : ℤ) ∣ a ∧ (q : ℤ) ∣ b := by
    intro a b habΩ
    constructor
    · have h1 := weilPairing0_linComb_linComb_eq_zpow_det W (K := Ω) hqΩ P₁ Q₁ hqP₁ hqQ₁ !![a, 0; b, 1]
      simp only [Matrix.det_fin_two_of, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, zero_smul, one_smul, zero_add, mul_one, zero_mul, sub_zero] at h1
      rw [habΩ, weilPairing0_zero_left Ω W hqΩ Q₁ hqQ₁] at h1
      exact (hprimU.zpow_eq_one_iff_dvd a).mp h1.symm
    · have h1 := weilPairing0_linComb_linComb_eq_zpow_det W (K := Ω) hqΩ P₁ Q₁ hqP₁ hqQ₁ !![a, 1; b, 0]
      simp only [Matrix.det_fin_two_of, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, zero_smul, one_smul, add_zero, one_mul, mul_zero, zero_sub] at h1
      rw [habΩ, weilPairing0_zero_left Ω W hqΩ P₁ hqP₁] at h1
      have := (hprimU.zpow_eq_one_iff_dvd (-b)).mp h1.symm
      exact (dvd_neg.mp this)
  have hDP : toPoint V D'.xP D'.yP = P₁ := by rw [hP₁, hD', LevelPData.map_xP, LevelPData.map_yP]
  have hDQ : toPoint V D'.xQ D'.yQ = Q₁ := by rw [hQ₁, hD', LevelPData.map_xQ, LevelPData.map_yQ]
  have hΩ1 : g 0 0 • toPoint V D'.xP D'.yP + g 1 0 • toPoint V D'.xQ D'.yQ ≠ 0 := by
    rw [hDP, hDQ]; exact fun h0 => hnotcol (g 0 0) (g 1 0) (g 0 1) (g 1 1) (by rw [Matrix.det_fin_two]) (hcol _ _ h0)
  have hΩ2 : g 0 1 • toPoint V D'.xP D'.yP + g 1 1 • toPoint V D'.xQ D'.yQ ≠ 0 := by
    rw [hDP, hDQ]; exact fun h0 => hnotcol (g 0 1) (g 1 1) (-g 0 0) (-g 1 0) (by rw [Matrix.det_fin_two]; ring) (hcol _ _ h0)
  obtain ⟨r1, r2⟩ := toPoint_relabel_eq_zsmul_add_zsmul V g D' hΩ1 hΩ2
  have e1 : (LevelPData.relabel W g D).map (algebraMap K Ω) = LevelPData.relabel V g D' :=
    (relabel_map_eq_map_relabel (algebraMap K Ω) W g D).symm
  have hP'₁ : toPoint V (algebraMap K Ω xP') (algebraMap K Ω yP') = g 0 0 • P₁ + g 1 0 • Q₁ := by
    rw [← hcoP.1, ← hcoP.2, ← LevelPData.map_xP (algebraMap K Ω), ← LevelPData.map_yP (algebraMap K Ω), e1, r1, hDP, hDQ]
  have hQ'₁ : toPoint V (algebraMap K Ω xQ') (algebraMap K Ω yQ') = g 0 1 • P₁ + g 1 1 • Q₁ := by
    rw [← hcoQ.1, ← hcoQ.2, ← LevelPData.map_xQ (algebraMap K Ω), ← LevelPData.map_yQ (algebraMap K Ω), e1, r2, hDP, hDQ]
  change weilPairing0 W Ω q (toPoint V (algebraMap K Ω xP') (algebraMap K Ω yP')) (toPoint V (algebraMap K Ω xQ') (algebraMap K Ω yQ')) =
    weilPairing0 W Ω q P₁ Q₁ ^ g.det
  rw [hP'₁, hQ'₁]
  exact weilPairing0_linComb_linComb_eq_zpow_det W (K := Ω) hqΩ P₁ Q₁ hqP₁ hqQ₁ g

include h𝒢 h𝒢O hq3 h𝒯 hqK in

theorem weil_primitive (x : RawDrinfeldPair K) [x.curve.IsElliptic] (hx : RawDrinfeldPair.IsLevel 𝒢 q x.curve x)
    (xP yP xQ yQ : K) (hP : IsSectionThrough x.P xP yP) (hQ : IsSectionThrough x.Q xQ yQ) :
    IsPrimitiveRoot (weilPairing0 x.curve Ω q (toPoint (x.curve⁄Ω) (algebraMap K Ω xP) (algebraMap K Ω yP))
        (toPoint (x.curve⁄Ω) (algebraMap K Ω xQ) (algebraMap K Ω yQ))) q :=
  IsPrimitiveRoot.coe_units_iff.mp (WeierstrassCurve.DrinfeldGlobal.isPrimitiveRoot_weilPairing0_of_isLevel_of_isSectionThrough_ed2 A 𝒢 h𝒢 h𝒢O q hq3 𝒯 h𝒯 hqK Ω x.curve x hx ⟨xP, yP, xQ, yQ⟩ hP hQ)

end Reading

theorem weil_congr {K : Type} [Field K] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (q : ℕ)
    {W W' : WeierstrassCurve K} (e : W = W') (hW : W.IsElliptic) (hW' : W'.IsElliptic) (a b c d : Ω) :
    (letI := hW; weilPairing0 W Ω q (toPoint (W⁄Ω) a b) (toPoint (W⁄Ω) c d)) =
      (letI := hW'; weilPairing0 W' Ω q (toPoint (W'⁄Ω) a b) (toPoint (W'⁄Ω) c d)) := by
  subst e; rfl

theorem det_eq_mod_q
    (A : Type) [CommRing A] (ℓ M' q : ℕ) [Fact ℓ.Prime] [NeZero M'] [Fact q.Prime] (hq3 : 3 ≤ q)
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (P₀ : LevelModuliPackageAbs A (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    (K : Type) [Field K] [Algebra A K] (hqK : ((q : ℕ) : K) ≠ 0)
    (ζ : A) (hζ : IsPrimitiveRoot (algebraMap A K ζ) q)
    (y y₁ y₂ : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw K) (hΔy : IsUnit y.level.2.2.curve.Δ)
    (g₁ g₂ : Matrix (Fin 2) (Fin 2) ℤ) (hg₁ : IsUnit ((g₁.det : ℤ) : ZMod q)) (hg₂ : IsUnit ((g₂.det : ℤ) : ZMod q))
    (hc₁ : y₁.curve = y.curve) (hd₁ : y₁.level.2.2 = RawDrinfeldPair.relabel 𝒢 g₁ y.level.2.2 hΔy)
    (hc₂ : y₂.curve = y.curve) (hd₂ : y₂.level.2.2 = RawDrinfeldPair.relabel 𝒢 g₂ y.level.2.2 hΔy)
    (h : RingHom.ker (P₀.classify (Quot.mk _ y₁)).toRingHom = RingHom.ker (P₀.classify (Quot.mk _ y₂)).toRingHom) :
    ((g₁.det : ℤ) : ZMod q) = ((g₂.det : ℤ) : ZMod q) := by
  classical
  let Ω := AlgebraicClosure K
  have hqp : q.Prime := Fact.out
  have hqΩ : ((q : ℕ) : Ω) ≠ 0 := fun h0 => hqK (by
    have : algebraMap K Ω (q : K) = 0 := by rw [map_natCast, h0]
    exact (map_eq_zero_iff _ (algebraMap K Ω).injective).mp this)
  have hqunitΩ : IsUnit ((q : ℕ) : Ω) := isUnit_iff_ne_zero.mpr hqΩ
  set φA : K →ₐ[A] Ω := IsScalarTower.toAlgHom A K Ω with hφA

  set z := (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing φA y with hzdef
  set z₁ := (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing φA y₁ with hz₁def
  set z₂ := (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing φA y₂ with hz₂def
  set x := z.level.2.2 with hxdef
  have hzL : RawDrinfeldPair.IsLevel 𝒢 q z.curve z.level.2.2 := z.isLevel.2.2
  have hX : x.curve = z.curve := hzL.1
  have hΔx : IsUnit x.curve.Δ := by rw [hX]; exact z.isUnit_Δ
  haveI hxE : x.curve.IsElliptic := ⟨hΔx⟩
  have hLx : RawDrinfeldPair.IsLevel 𝒢 q x.curve x := by rw [hX]; exact hzL

  have hrel : ∀ (y' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw K) (g : Matrix (Fin 2) (Fin 2) ℤ),
      y'.level.2.2 = RawDrinfeldPair.relabel 𝒢 g y.level.2.2 hΔy →
      ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing φA y').level.2.2 = RawDrinfeldPair.relabel 𝒢 g x hΔx := by
    intro y' g hd
    show 𝒯.map φA y'.level.2.2 = RawDrinfeldPair.relabel 𝒢 g (𝒯.map φA y.level.2.2) hΔx
    rw [hd]
    exact LevelTransport.map_relabel_eq_relabel_map 𝒢 h𝒢 h𝒢O q 𝒯 h𝒯 hVC hCO K Ω φA g y.level.2.2 hΔy hΔx
  have hz₁ := hrel y₁ g₁ hd₁
  have hz₂ := hrel y₂ g₂ hd₂

  obtain ⟨⟨xP, yP, hP⟩, ⟨xQ, yQ, hQ⟩⟩ :=
    RawDrinfeldPair.IsLevel.exists_isSectionThrough_of_isUnit q A 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 x.curve hqunitΩ x hLx
  obtain ⟨⟨xP₁, yP₁, hP₁⟩, ⟨xQ₁, yQ₁, hQ₁⟩⟩ :=
    RawDrinfeldPair.IsLevel.exists_isSectionThrough_of_isUnit q A 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 z₁.curve hqunitΩ z₁.level.2.2 z₁.isLevel.2.2
  obtain ⟨⟨xP₂, yP₂, hP₂⟩, ⟨xQ₂, yQ₂, hQ₂⟩⟩ :=
    RawDrinfeldPair.IsLevel.exists_isSectionThrough_of_isUnit q A 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 z₂.curve hqunitΩ z₂.level.2.2 z₂.isLevel.2.2

  have hEq := ModularCurve.LevelModuliPackageAbs.weilPairing0_drinfeld_mapRing_eq_of_ker_classify_eq_rigidDataPow A ℓ M' q hq3 hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO P₀ K ζ hζ Ω
    (Quot.mk _ y₁) (Quot.mk _ y₂) h y₁ y₂ rfl rfl ⟨xP₁, yP₁, xQ₁, yQ₁⟩ ⟨xP₂, yP₂, xQ₂, yQ₂⟩ ⟨hP₁, hQ₁⟩ ⟨hP₂, hQ₂⟩

  have hr₁ := weil_relabel A 𝒢 h𝒢 h𝒢O q hq3 𝒯 h𝒯 hqΩ Ω x hLx hΔx g₁ hg₁ xP yP xQ yQ hP hQ xP₁ yP₁ xQ₁ yQ₁
    (hz₁ ▸ hP₁) (hz₁ ▸ hQ₁)
  have hr₂ := weil_relabel A 𝒢 h𝒢 h𝒢O q hq3 𝒯 h𝒯 hqΩ Ω x hLx hΔx g₂ hg₂ xP yP xQ yQ hP hQ xP₂ yP₂ xQ₂ yQ₂
    (hz₂ ▸ hP₂) (hz₂ ▸ hQ₂)
  have hprim := weil_primitive A 𝒢 h𝒢 h𝒢O q hq3 𝒯 h𝒯 hqΩ Ω x hLx xP yP xQ yQ hP hQ
  simp only [Algebra.algebraMap_self_apply] at hr₁ hr₂ hprim
  set e₀ := weilPairing0 x.curve Ω q (toPoint (x.curve⁄Ω) xP yP) (toPoint (x.curve⁄Ω) xQ yQ) with he₀

  have hzc : z.curve = y.curve.map (φA : K →+* Ω) := rfl
  have e1 : z₁.curve = x.curve := by
    rw [hX, hzc, show z₁.curve = y₁.curve.map (φA : K →+* Ω) from rfl, hc₁]
  have e2 : z₂.curve = x.curve := by
    rw [hX, hzc, show z₂.curve = y₂.curve.map (φA : K →+* Ω) from rfl, hc₂]
  have hEq' : e₀ ^ g₁.det = e₀ ^ g₂.det := by
    rw [← hr₁, ← hr₂]
    apply Units.ext
    rw [← weil_congr Ω q e1 ⟨z₁.isUnit_Δ⟩ hxE, ← weil_congr Ω q e2 ⟨z₂.isUnit_Δ⟩ hxE]
    exact hEq
  have hdvd : (q : ℤ) ∣ g₁.det - g₂.det := by
    rw [← hprim.zpow_eq_one_iff_dvd, zpow_sub, hEq', mul_inv_cancel]
  have : ((g₁.det - g₂.det : ℤ) : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hdvd
  rwa [Int.cast_sub, sub_eq_zero] at this

end C2dQ

open C2dSol in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓA : IsUnit ((ℓ : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (P₀ : LevelModuliPackageAbs A (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    [Algebra.FiniteType A P₀.B₀]
    (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K)
    (hx : (((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x : ↥K) : LaurentSeries L) =
      ModularCurve.jqNModC L (q * ℓ))
    (g₁ g₂ : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet₁ : IsUnit (g₁.map (Int.castRingHom (ZMod (q * ℓ)))).det) (hdet₂ : IsUnit (g₂.map (Int.castRingHom (ZMod (q * ℓ)))).det)
    (σ₁ σ₂ : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.ProblemAut)
    (hσ₁ : ∀ (T : Type) [Field T] [Algebra A T]
        (y y' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (hΔ : IsUnit y.level.2.2.curve.Δ),
        y'.curve = y.curve →
        y'.level.1 = y.level.1 →
        y'.level.2.1 = ModularCurve.LevelRelabelling.LevelPData.relabel y.curve g₁ y.level.2.1 →
        y'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g₁ y.level.2.2 hΔ →
        σ₁.act (Quot.mk _ y) = Quot.mk _ y')
    (hσ₂ : ∀ (T : Type) [Field T] [Algebra A T]
        (y y' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (hΔ : IsUnit y.level.2.2.curve.Δ),
        y'.curve = y.curve →
        y'.level.1 = y.level.1 →
        y'.level.2.1 = ModularCurve.LevelRelabelling.LevelPData.relabel y.curve g₂ y.level.2.1 →
        y'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g₂ y.level.2.2 hΔ →
        σ₂.act (Quot.mk _ y) = Quot.mk _ y')
    (h : RingHom.ker (P₀.classify (σ₁.act x)).toRingHom = RingHom.ker (P₀.classify (σ₂.act x)).toRingHom) :
    ((g₁.det : ℤ) : ZMod ℓ) = ((g₂.det : ℤ) : ZMod ℓ) ∧ ((g₁.det : ℤ) : ZMod q) = ((g₂.det : ℤ) : ZMod q) := by
  classical
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  haveI : CharZero ↥K := by infer_instance
  have hℓK' : (ℓ : ↥K) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne ℓ)

  obtain ⟨y, rfl⟩ := Quot.exists_rep x
  have hΔy : IsUnit y.level.2.2.curve.Δ := by
    obtain ⟨hc, -⟩ := y.isLevel.2.2
    rw [hc]; exact y.isUnit_Δ
  have hg₁ℓ := isUnit_det_of_dvd (Dvd.intro_left q rfl) g₁ hdet₁
  have hg₂ℓ := isUnit_det_of_dvd (Dvd.intro_left q rfl) g₂ hdet₂
  have hg₁q := isUnit_det_of_dvd (Dvd.intro ℓ rfl) g₁ hdet₁
  have hg₂q := isUnit_det_of_dvd (Dvd.intro ℓ rfl) g₂ hdet₂

  let rel : ∀ (g : Matrix (Fin 2) (Fin 2) ℤ), IsUnit ((g.det : ℤ) : ZMod ℓ) → IsUnit ((g.det : ℤ) : ZMod q) →
      (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw ↥K := fun g hgℓ hgq =>
    show LevelComponent.Raw ((gamma0PowComponent A M' hM).prod ((levelPComponent A ℓ hℓ).prod (levelComponent A 𝒢 q 𝒯))) ↥K from
    LevelComponent.Raw.mk y.curve y.isUnit_Δ
      (y.level.1, LevelPData.relabel y.curve g y.level.2.1, RawDrinfeldPair.relabel 𝒢 g y.level.2.2 hΔy)
      (by
        refine And.intro y.isLevel.1 (And.intro ?_ ?_)
        · exact IsLevelPStructure.relabel_of_isUnit_det ℓ hℓ3 hℓK' y.curve y.isUnit_Δ _ y.isLevel.2.1 g hgℓ
        · obtain ⟨hc, hΔ₀, hB⟩ := y.isLevel.2.2
          refine And.intro hc (Exists.intro hΔ₀ ?_)
          exact IsDrinfeldBasis.zlinComb_zlinComb_of_isUnit_det _
            (GroupLaws.mul_comm_of_isOriginIdentity 𝒢 h𝒢 h𝒢O hVC hCO _ _ hΔ₀) q _ _ hB g hgq)
  set y₁ := rel g₁ hg₁ℓ hg₁q with hy₁
  set y₂ := rel g₂ hg₂ℓ hg₂q with hy₂
  have e₁ : σ₁.act (Quot.mk _ y) = Quot.mk _ y₁ := hσ₁ ↥K y y₁ hΔy rfl rfl rfl rfl
  have e₂ : σ₂.act (Quot.mk _ y) = Quot.mk _ y₂ := hσ₂ ↥K y y₂ hΔy rfl rfl rfl rfl

  obtain ⟨ζ, hζ⟩ : ∃ ζ : A, IsPrimitiveRoot (algebraMap A ↥K ζ) ℓ := by
    have hpos : 0 < q * ℓ := Nat.pos_of_ne_zero (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (NeZero.ne ℓ))
    have hξq : IsPrimitiveRoot (ξ ^ q) ℓ := hξ.pow hpos rfl
    have hint : IsIntegral A (ξ ^ q) := by
      refine IsIntegral.of_pow (Nat.pos_of_ne_zero (NeZero.ne ℓ)) ?_
      rw [hξq.pow_eq_one]; exact isIntegral_one
    obtain ⟨ζ, hζ⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := L)).mp hint
    refine ⟨ζ, ?_⟩
    rw [IsScalarTower.algebraMap_apply A L ↥K, hζ]
    exact hξq.map_of_injective (algebraMap L ↥K).injective

  let Ω := AlgebraicClosure ↥K
  have hE := LevelModuliPackageAbs.weilPairing0_mapRing_eq_of_ker_classify_eq_rigidDataPow A ℓ M' q hℓ3 hℓA hℓ hM 𝒢 𝒯 P₀
    ↥K ζ hζ Ω (σ₁.act (Quot.mk _ y)) (σ₂.act (Quot.mk _ y)) h y₁ y₂ e₁.symm e₂.symm

  set φ : ↥K →+* Ω := algebraMap ↥K Ω with hφ
  set W' : WeierstrassCurve Ω := y.curve.map φ with hW'
  set D' : LevelPData Ω := y.level.2.1.map φ with hD'
  haveI hW'ell : W'.IsElliptic := ⟨y.curve.isUnit_Δ_map φ y.isUnit_Δ⟩
  have hD'lev : IsLevelPStructure W' ℓ D' := y.isLevel.2.1.map φ
  have hℓΩ : (ℓ : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne ℓ)
  have hRM : ∀ g : Matrix (Fin 2) (Fin 2) ℤ,
      (LevelPData.relabel y.curve g y.level.2.1).map φ = LevelPData.relabel W' g D' := fun g =>
    (relabel_map_eq_map_relabel φ y.curve g y.level.2.1).symm
  have hE' : ((weilPairing0 W' Ω ℓ
        (toPoint (W'⁄Ω) (algebraMap Ω Ω (LevelPData.relabel W' g₁ D').xP) (algebraMap Ω Ω (LevelPData.relabel W' g₁ D').yP))
        (toPoint (W'⁄Ω) (algebraMap Ω Ω (LevelPData.relabel W' g₁ D').xQ) (algebraMap Ω Ω (LevelPData.relabel W' g₁ D').yQ)) : Ωˣ) : Ω) =
      ((weilPairing0 W' Ω ℓ
        (toPoint (W'⁄Ω) (algebraMap Ω Ω (LevelPData.relabel W' g₂ D').xP) (algebraMap Ω Ω (LevelPData.relabel W' g₂ D').yP))
        (toPoint (W'⁄Ω) (algebraMap Ω Ω (LevelPData.relabel W' g₂ D').xQ) (algebraMap Ω Ω (LevelPData.relabel W' g₂ D').yQ)) : Ωˣ) : Ω) := by
    simp only [Algebra.algebraMap_self_apply, ← hRM]
    exact hE
  refine ⟨det_eq_of_weilPairing0_relabel_eq Ω W' ℓ hℓ3 hℓΩ D' hD'lev g₁ g₂ hg₁ℓ hg₂ℓ hE', ?_⟩

  have hq3 : 3 ≤ q := by omega
  have hqK' : ((q : ℕ) : ↥K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  obtain ⟨ζq, hζq⟩ : ∃ ζq : A, IsPrimitiveRoot (algebraMap A ↥K ζq) q := by
    have hpos : 0 < ℓ * q := Nat.pos_of_ne_zero (Nat.mul_ne_zero (NeZero.ne ℓ) (Fact.out : q.Prime).ne_zero)
    have hξ' : IsPrimitiveRoot ξ (ℓ * q) := by rw [Nat.mul_comm]; exact hξ
    have hξℓ : IsPrimitiveRoot (ξ ^ ℓ) q := hξ'.pow hpos rfl
    have hint : IsIntegral A (ξ ^ ℓ) := by
      refine IsIntegral.of_pow (Nat.pos_of_ne_zero (Fact.out : q.Prime).ne_zero) ?_
      rw [hξℓ.pow_eq_one]; exact isIntegral_one
    obtain ⟨ζq, hζq⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := L)).mp hint
    refine ⟨ζq, ?_⟩
    rw [IsScalarTower.algebraMap_apply A L ↥K, hζq]
    exact hξℓ.map_of_injective (algebraMap L ↥K).injective
  have h' : RingHom.ker (P₀.classify (Quot.mk _ y₁)).toRingHom = RingHom.ker (P₀.classify (Quot.mk _ y₂)).toRingHom := by
    rw [← e₁, ← e₂]; exact h
  exact C2dQ.det_eq_mod_q A ℓ M' q hq3 hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO P₀ ↥K hqK' ζq hζq y y₁ y₂ hΔy g₁ g₂ hg₁q hg₂q
    rfl rfl rfl rfl h'

end S_ModularCurve_FullLevel_det_eq_of_ker_classify_act_eq_of_relabel_gamma0Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_det_eq_of_ker_classify_act_eq_of_relabel_gamma0Pow (solution)
