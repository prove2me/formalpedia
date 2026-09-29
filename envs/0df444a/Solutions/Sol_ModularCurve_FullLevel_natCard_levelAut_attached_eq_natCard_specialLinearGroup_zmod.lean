-- Prove2me | solution 1 for ModularCurve.FullLevel.natCard_levelAut_attached_eq_natCard_specialLinearGroup_zmod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/1387f302-84f0-5435-a043-0950ee001d3d

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_WeierstrassCurve_RationalEnd
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_map_eq_one_or_eq_neg_one_of_isLevelAutAt_one_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_levelAut_eq_one_of_map_eq_one_or_eq_neg_one_of_exists_ringHom
import Theorems.Thm_CongruenceSubgroup_exists_mem_Gamma_map_eq_of_not_dvd
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_natCard_levelAut_attached_eq_natCard_specialLinearGroup_zmod
p2m_attr_erase "instance" "HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedMonoid HomogeneousIdealQuotientGrading.quotGradingGradedMonoid HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedAlgebraOfHomogeneous HomogeneousIdealQuotientGrading.quotGradingGradedRingOfHomogeneous ModularCurve.LevelModuliDatum.Twist.instCommRing ModularCurve.LevelModuliDatum.Twist.instAlgebra ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul ModularCurve.instIsElliptic_tateLaurent AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType ModularCurve.LevelModuliPackageAbs.instCommRing"
p2m_attr_erase "instance" "ModularCurve.LevelModuliPackageAbs.instAlgebra ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing ModularCurve.LevelP.instCommRingVCRing ModularCurve.LevelP.instCommRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelPRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelQRingBorelPRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingVCPolyVCRing ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatUnivBasisRingXVCRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelPRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingVCRing ModularCurve.LevelP.instAlgebraVCPolyVCRing ModularCurve.LevelP.instAlgebraBorelPRingBorelRing ModularCurve.LevelP.instAwayBorelPRingBorelDenomBorelRing WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateBase ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "WeierstrassProjModel.schemeHomOverComp_coe WeierstrassProjModel.RelativeGroupLaw.mk.sizeOf_spec WeierstrassProjModel.RelativeGroupLaw.nsmul_zero WeierstrassProjModel.RelativeGroupLaw.nsmul_succ WeierstrassProjModel.projModelHomogeneousIdealCR_toIdeal WeierstrassProjModel.RelativeGroupLaw.mk.injEq WeierstrassProjModel.RelativeGroupLaw.mem_torsionSubset HomogeneousIdealQuotientGrading.pieceHom_coe HomogeneousIdealQuotientGrading.quotDecompose_mk HomogeneousIdealQuotientGrading.quotGradingPieceHom_coe NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst ModularCurve.LevelComponent.mk.sizeOf_spec ModularCurve.LevelComponent.mk.injEq ModularCurve.LevelComponent.Raw.mk.injEq ModularCurve.LevelComponent.Raw.mk.sizeOf_spec ModularCurve.RigidWeierstrassData.mk.sizeOf_spec ModularCurve.RigidWeierstrassData.mk.injEq ModularCurve.LevelModuliPackage.mk.sizeOf_spec ModularCurve.LevelModuliDatum.mk.sizeOf_spec ModularCurve.LevelModuliDatum.SemilinearProblemAut.mk.injEq ModularCurve.LevelModuliDatum.SemilinearProblemAut.mk.sizeOf_spec ModularCurve.LevelModuliDatum.ProblemAut.mk.sizeOf_spec ModularCurve.LevelModuliPackage.mk.injEq ModularCurve.LevelModuliDatum.ProblemAut.mk.injEq ModularCurve.LevelModuliDatum.mk.injEq ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.mk.injEq WeierstrassCurve.DrinfeldGlobal.DrinfeldTransport.mk.injEq WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.mk.sizeOf_spec WeierstrassCurve.DrinfeldGlobal.DrinfeldTransport.mk.sizeOf_spec AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst"
p2m_attr_erase "simp" "AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.injEq WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.sizeOf_spec WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X DrinfeldCurve.LocalChart.ChartPresentation.mk.sizeOf_spec DrinfeldCurve.LocalChart.ChartPresentation.mk.injEq ModularCurve.LevelModuliPackageAbs.mk.sizeOf_spec ModularCurve.LevelModuliPackageAbs.mk.injEq ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add ModularCurve.LevelP.VCRing.lift_vcVar ModularCurve.LevelP.BorelPRing.lift_xQ ModularCurve.LevelP.twoPointLift_xQ ModularCurve.LevelP.PsiRoot.lift_ofBase ModularCurve.LevelP.univVC_u ModularCurve.LevelP.twoPointLift_yP ModularCurve.LevelP.univVC_r ModularCurve.LevelP.TorsionPointRing.lift_torsionPtX ModularCurve.LevelP.TorsionPointRing.lift_ofPsiRoot ModularCurve.LevelP.TorsionPointRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_C ModularCurve.LevelP.BorelQRing.lift_of ModularCurve.LevelP.BorelPRing.lift_yQ ModularCurve.LevelP.BorelPRing.lift_ofUniv"
p2m_attr_erase "simp" "ModularCurve.LevelP.univVC_t ModularCurve.LevelP.BorelRing.lift_ofUniv ModularCurve.LevelP.univVC_s ModularCurve.LevelP.twoPointLift_xP ModularCurve.LevelP.twoPointLift_yQ ModularCurve.LevelP.TorsionPointRing.lift_torsionPtY ModularCurve.LevelP.BorelQRing.lift_borelQY ModularCurve.LevelP.VCRing.lift_algebraMap ModularCurve.LevelP.VCRing.lift_ofUniv ModularCurve.LevelP.PsiRoot.lift_psiRootX ModularCurve.LevelP.BorelRing.lift_algebraMap ModularCurve.LevelP.BorelPRing.lift_yP ModularCurve.LevelP.BasisRing.lift_ofTwoPoint ModularCurve.LevelP.BasisRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_X ModularCurve.LevelP.genericLift_X ModularCurve.LevelP.twoPointLift_ofBase ModularCurve.LevelP.BorelPRing.lift_xP compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂"
p2m_attr_erase "simp" "TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one"
p2m_attr_erase "simp" "ModularCurve.cuspShift_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 12800000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace K2bAux

open scoped MatrixGroups

theorem exists_emb (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (m : ℕ) [NeZero m]
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ m) :
    ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / m) := by
  haveI hQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h := AlgebraicClosure.isAlgebraic ℚ
    convert h <;> first | rfl | with_reducible_and_instances rfl | exact Subsingleton.elim _ _
  haveI : Algebra.IsAlgebraic ℚ ↥k₀ :=
    Algebra.IsAlgebraic.of_injective (k₀.val) (k₀.val).toRingHom.injective
  have hmin : minpoly ℚ ξ = Polynomial.cyclotomic m ℚ :=
    (Polynomial.cyclotomic_eq_minpoly_rat hξ (Nat.pos_of_ne_zero (NeZero.ne m))).symm
  have hroot : Complex.exp (2 * Real.pi * Complex.I / m) ∈ (minpoly ℚ ξ).rootSet ℂ := by
    rw [hmin, Polynomial.mem_rootSet]
    refine ⟨Polynomial.cyclotomic_ne_zero m ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact (Polynomial.isRoot_cyclotomic_iff.mpr (Complex.isPrimitiveRoot_exp m (NeZero.ne m))).eq_zero
  rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ ξ] at hroot
  obtain ⟨ψ, hψ⟩ := hroot
  exact ⟨ψ.toRingHom, hψ⟩

theorem intCast_eq_one_of_dvd {M N : ℕ} (h : M ∣ N) {x : ℤ} (hx : ((x : ℤ) : ZMod N) = 1) : ((x : ℤ) : ZMod M) = 1 := by
  rw [← Int.cast_one, ZMod.intCast_eq_intCast_iff_dvd_sub] at hx ⊢
  exact dvd_trans (Int.natCast_dvd_natCast.mpr h) hx

theorem intCast_eq_zero_of_dvd {M N : ℕ} (h : M ∣ N) {x : ℤ} (hx : ((x : ℤ) : ZMod N) = 0) : ((x : ℤ) : ZMod M) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hx ⊢
  exact dvd_trans (Int.natCast_dvd_natCast.mpr h) hx

theorem mem_Gamma_of_dvd {M N : ℕ} (h : M ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma N) :
    γ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  exact ⟨intCast_eq_one_of_dvd h hγ.1, intCast_eq_zero_of_dvd h hγ.2.1, intCast_eq_zero_of_dvd h hγ.2.2.1,
    intCast_eq_one_of_dvd h hγ.2.2.2⟩

theorem mem_Gamma0_of_mem_Gamma {M N : ℕ} (h : M ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma N) :
    γ ∈ CongruenceSubgroup.Gamma0 M := by
  rw [CongruenceSubgroup.Gamma0_mem]
  have h' := mem_Gamma_of_dvd h hγ
  rw [CongruenceSubgroup.Gamma_mem] at h'
  exact h'.2.2.1

theorem mem_Gamma_mul {a b : ℕ} (hab : Nat.Coprime a b) {γ : SL(2, ℤ)}
    (ha : γ ∈ CongruenceSubgroup.Gamma a) (hb : γ ∈ CongruenceSubgroup.Gamma b) :
    γ ∈ CongruenceSubgroup.Gamma (a * b) := by
  rw [CongruenceSubgroup.Gamma_mem] at ha hb ⊢
  have hc : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hab
  have key1 : ∀ x : ℤ, ((x : ℤ) : ZMod a) = 1 → ((x : ℤ) : ZMod b) = 1 → ((x : ℤ) : ZMod (a * b)) = 1 := by
    intro x hxa hxb
    rw [← Int.cast_one, ZMod.intCast_eq_intCast_iff_dvd_sub] at hxa hxb ⊢
    push_cast
    exact hc.mul_dvd hxa hxb
  have key0 : ∀ x : ℤ, ((x : ℤ) : ZMod a) = 0 → ((x : ℤ) : ZMod b) = 0 → ((x : ℤ) : ZMod (a * b)) = 0 := by
    intro x hxa hxb
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hxa hxb ⊢
    push_cast
    exact hc.mul_dvd hxa hxb
  exact ⟨key1 _ ha.1 hb.1, key0 _ ha.2.1 hb.2.1, key0 _ ha.2.2.1 hb.2.2.1, key1 _ ha.2.2.2 hb.2.2.2⟩

theorem map_ne_neg_one {q N : ℕ} (hq : 3 ≤ q) (hqN : q ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma q)
    (h : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ = -1) : False := by
  have h00 := congrArg (fun m : SL(2, ZMod N) => (m : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0) h
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom,
    Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply, Matrix.one_apply_eq] at h00
  rw [CongruenceSubgroup.Gamma_mem] at hγ
  have h1 := hγ.1
  have h00' : (N : ℤ) ∣ -1 - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by rw [Int.cast_neg, Int.cast_one]; exact h00)
  have h1' : (q : ℤ) ∣ 1 - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by rw [Int.cast_one]; exact h1)
  have hqd : (q : ℤ) ∣ -1 - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) := dvd_trans (Int.natCast_dvd_natCast.mpr hqN) h00'
  have h2 : (q : ℤ) ∣ (1 - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ)) - (-1 - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ)) :=
    dvd_sub h1' hqd
  rw [show (1 - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ)) - (-1 - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ)) = ((2 : ℕ) : ℤ) by
    push_cast; ring] at h2
  have : q ≤ 2 := Nat.le_of_dvd two_pos (Int.natCast_dvd_natCast.mp h2)
  omega

end K2bAux

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ' : ℕ) [Fact ℓ'.Prime] (hℓ'3 : 3 ≤ ℓ') (hℓ'q : ℓ' ≠ q) (hℓ'M : ¬ ℓ' ∣ M')
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ (q * ℓ'))

    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hKℓ : Kℓ = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M')))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ]
    (jℓ : ↥Kℓ) (hjℓ : ((jℓ : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (jℓ ≠ 0)] :
    Nat.card {τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ //
        ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
          ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ Kℓ τ} =
    Nat.card (SL(2, ZMod ℓ')) := by
  classical
  haveI hmne : NeZero (q * ℓ') := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero⟩
  haveI hqMne : NeZero (q * M') := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (NeZero.ne M')⟩
  have hqp : q.Prime := Fact.out
  have hℓp : ℓ'.Prime := Fact.out

  obtain ⟨ι, hι'⟩ := K2bAux.exists_emb k₀ (q * ℓ') ξ hξ
  have hι : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ')) :=
    ⟨ι, by rw [hι']; simp only [Nat.cast_mul]⟩

  obtain ⟨huniq, hmul, hone⟩ := ModularCurve.FullLevel.AuxLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom
    q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M ↥k₀ ξ hξ hι Kℓ hKℓ
  have hex := ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
    q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M ↥k₀ ξ hξ hι Kℓ hKℓ
  have htriv := ModularCurve.FullLevel.AuxLevel.levelAut_eq_one_of_map_eq_one_or_eq_neg_one_of_exists_ringHom
    q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M ↥k₀ ξ hξ hι Kℓ hKℓ
  have hℓ'qM' : ¬ ℓ' ∣ q * M' := fun h =>
    (hℓp.dvd_mul.mp h).elim (fun h1 => hℓ'q ((Nat.prime_dvd_prime_iff_eq hℓp hqp).mp h1)) hℓ'M
  obtain ⟨hlift, hkerℓ, -⟩ := CongruenceSubgroup.exists_mem_Gamma_map_eq_of_not_dvd (q * M') ℓ' hℓ'qM'

  haveI : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := hdvr
  have hqA : ((q : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    have hq' : (((q : ℕ) : ↥A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := by norm_cast
    rw [← ValuationSubring.coe_mem_nonunits_iff, hq']; exact hA
  have hAq : ((q : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈ IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨u, hu1⟩ := hu.exists_right_inv
    have hmemA : ((u : ↥k₀) : AlgebraicClosure ℚ) ∈ A := u.2
    have e1 : ((q : ℕ) : ↥A) * ⟨((u : ↥k₀) : AlgebraicClosure ℚ), hmemA⟩ = 1 := by
      apply Subtype.ext
      have := congrArg (fun z : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) => (((z : ↥k₀)) : AlgebraicClosure ℚ)) hu1
      push_cast at this ⊢
      simpa using this
    have : IsUnit ((q : ℕ) : ↥A) := IsUnit.of_mul_eq_one _ e1
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp hqA) this
  have hunitA : ∀ n : ℕ, Nat.Coprime n q → IsUnit ((n : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := by
    intro n hn
    by_contra hnu
    have hn𝔪 : ((n : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈ IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hnu
    have hc : IsCoprime ((n : ℤ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((q : ℤ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) :=
      (Nat.isCoprime_iff_coprime.mpr hn).map (Int.castRingHom ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    obtain ⟨a, b, hab⟩ := hc
    have h1 : (1 : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈ IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := by
      rw [← hab]
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
      · simpa using hn𝔪
      · simpa using hAq
    exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))).ne_top h1
  have hℓA : IsUnit ((ℓ' : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := hunitA ℓ' ((Nat.coprime_primes hℓp hqp).mpr hℓ'q)
  have hM'A : IsUnit ((M' : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := hunitA M' ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hqM').symm

  have hfaith : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ Kℓ 1 →
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (q * ℓ'))) γ = 1 ∨
        Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (q * ℓ'))) γ = -1 :=
    fun γ hγ h1 => ModularCurve.FullLevel.AuxLevel.map_eq_one_or_eq_neg_one_of_isLevelAutAt_one_of_exists_ringHom
      q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M ↥k₀ ξ hξ hι Kℓ hKℓ ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) hAq jℓ hjℓ hℓA hM'A γ hγ h1

  choose γg hγg using hlift
  have hγq : ∀ g, γg g ∈ CongruenceSubgroup.Gamma q := fun g => K2bAux.mem_Gamma_of_dvd (Dvd.intro M' rfl) (hγg g).1
  have hγ0 : ∀ g, γg g ∈ CongruenceSubgroup.Gamma0 M' := fun g => K2bAux.mem_Gamma0_of_mem_Gamma (Dvd.intro_left q rfl) (hγg g).1
  have hτex : ∀ g : SL(2, ZMod ℓ'), ∃ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ,
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') (γg g)⁻¹ Kℓ τ :=
    fun g => hex (γg g) (hγ0 g)
  choose τg hτg using hτex

  have hker : ∀ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma q → δ ∈ CongruenceSubgroup.Gamma0 M' →
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ℓ')) δ = 1 →
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') δ⁻¹ Kℓ 1 := by
    intro δ hδq hδ0 hδℓ
    have hδℓ' : δ ∈ CongruenceSubgroup.Gamma ℓ' := (hkerℓ δ).mp hδℓ
    have hδqℓ : δ ∈ CongruenceSubgroup.Gamma (q * ℓ') :=
      K2bAux.mem_Gamma_mul ((Nat.coprime_primes hqp hℓp).mpr (Ne.symm hℓ'q)) hδq hδℓ'
    obtain ⟨σ, hσ⟩ := hex δ hδ0
    have hσ1 : σ = 1 := htriv δ hδ0 (Or.inl (CongruenceSubgroup.Gamma_mem'.mp hδqℓ)) σ hσ
    rw [hσ1] at hσ
    exact hσ
  let F : SL(2, ZMod ℓ') → {τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ //
      ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
        ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ Kℓ τ} :=
    fun g => ⟨τg g, γg g, hγq g, hγ0 g, hτg g⟩
  symm
  refine Nat.card_eq_of_bijective F ⟨?_, ?_⟩
  ·
    intro g g' hgg'
    have hτ : τg g = τg g' := congrArg Subtype.val hgg'
    obtain ⟨σ, hσ⟩ := hex (γg g')⁻¹ (Subgroup.inv_mem _ (hγ0 g'))

    have h1' := hmul (γg g')⁻¹ ((γg g')⁻¹)⁻¹ (Subgroup.inv_mem _ (hγ0 g')) (by rw [inv_inv]; exact hγ0 g') (τg g') σ (hτg g') hσ
    rw [inv_mul_cancel] at h1'
    have hone' := hone 1 (Subgroup.one_mem _) (Subgroup.one_mem _)
    have hprod : τg g' * σ = 1 := huniq 1 (Subgroup.one_mem _) _ _ h1' hone'

    have h2 := hmul (γg g)⁻¹ ((γg g')⁻¹)⁻¹ (Subgroup.inv_mem _ (hγ0 g)) (by rw [inv_inv]; exact hγ0 g') (τg g) σ (hτg g) hσ
    rw [hτ, hprod, inv_inv, show γg g' * (γg g)⁻¹ = (γg g * (γg g')⁻¹)⁻¹ by rw [mul_inv_rev, inv_inv]] at h2
    have hmem0 : γg g * (γg g')⁻¹ ∈ CongruenceSubgroup.Gamma0 M' := Subgroup.mul_mem _ (hγ0 g) (Subgroup.inv_mem _ (hγ0 g'))
    have hmemq : γg g * (γg g')⁻¹ ∈ CongruenceSubgroup.Gamma q := Subgroup.mul_mem _ (hγq g) (Subgroup.inv_mem _ (hγq g'))
    rcases hfaith _ hmem0 h2 with hpos | hneg
    ·
      have hΓ : γg g * (γg g')⁻¹ ∈ CongruenceSubgroup.Gamma ℓ' :=
        K2bAux.mem_Gamma_of_dvd (Dvd.intro_left q rfl) (CongruenceSubgroup.Gamma_mem'.mpr hpos)
      have hmap : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ℓ')) (γg g * (γg g')⁻¹) = 1 := (hkerℓ _).mpr hΓ
      rw [map_mul, map_inv, (hγg g).2, (hγg g').2, mul_inv_eq_one] at hmap
      exact hmap
    · exact (K2bAux.map_ne_neg_one (by omega) (Dvd.intro ℓ' rfl) hmemq hneg).elim
  ·
    rintro ⟨τ, γ, hγq', hγ0', hτ⟩
    refine ⟨Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ℓ')) γ, Subtype.ext ?_⟩
    show τg (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ℓ')) γ) = τ
    set g := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ℓ')) γ with hg

    have hδq : (γg g)⁻¹ * γ ∈ CongruenceSubgroup.Gamma q := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hγq g)) hγq'
    have hδ0 : (γg g)⁻¹ * γ ∈ CongruenceSubgroup.Gamma0 M' := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hγ0 g)) hγ0'
    have hδℓ : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ℓ')) ((γg g)⁻¹ * γ) = 1 := by
      rw [map_mul, map_inv, (hγg g).2, ← hg, inv_mul_cancel]
    have hδ1 := hker _ hδq hδ0 hδℓ
    have h3 := hmul (γg g)⁻¹ ((γg g)⁻¹ * γ)⁻¹ (Subgroup.inv_mem _ (hγ0 g)) (Subgroup.inv_mem _ hδ0) (τg g) 1 (hτg g) hδ1
    rw [mul_one, ← mul_inv_rev, mul_inv_cancel_left] at h3
    exact huniq γ⁻¹ (Subgroup.inv_mem _ hγ0') _ _ h3 hτ

end S_ModularCurve_FullLevel_natCard_levelAut_attached_eq_natCard_specialLinearGroup_zmod
end P2MW
export P2MW.S_ModularCurve_FullLevel_natCard_levelAut_attached_eq_natCard_specialLinearGroup_zmod (solution)
