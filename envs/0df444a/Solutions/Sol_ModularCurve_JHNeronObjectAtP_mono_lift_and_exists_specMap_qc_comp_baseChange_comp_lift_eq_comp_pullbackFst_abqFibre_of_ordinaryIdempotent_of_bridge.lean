-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.mono_lift_and_exists_specMap_qc_comp_baseChange_comp_lift_eq_comp_pullbackFst_abqFibre_of_ordinaryIdempotent_of_bridge
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/387ef630-b457-5e5d-9890-da00ca4ae40d

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_GluedPic0SliceOps
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_abqFibre_one_comp_baseChange_hecke_U_eq_comp_relFrobenius_comp_abqFibre_one_of_not_sq_dvd
import Theorems.Thm_AlgebraicGeometry_isClosedImmersion_pullbackLift_of_isClosedImmersion_pullbackLift_of_isPullback
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_specMap_nsmulAlgHom_comp_eq_comp_schemeNsmul_of_forall_point_mul
import Theorems.Thm_HopfAlgebra_exists_forall_pow_pow_eq_algebraMap_counit_of_isLocalRing_zmodp
import Theorems.Thm_AlgebraicGeometry_specMap_comp_pullbackLift_eq_pullbackLift_comp_pullbackMap_of_comp_eq_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_mono_lift_and_exists_specMap_qc_comp_baseChange_comp_lift_eq_comp_pullbackFst_abqFibre_of_ordinaryIdempotent_of_bridge
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve"
p2m_attr_erase "instance" "WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice"
p2m_attr_erase "simp" "PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ"
p2m_attr_erase "simp" "ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_jqNGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.JZeroNeronObjectAtP

p2m_open "ModularCurve.XHDRLevel~ΓN"

namespace OrdAxis

theorem nsmulAlgHom_tmul {R : Type} [CommRing R] (k : Type) [CommRing k] [Algebra R k]
    (A : Type) [CommRing A] [Bialgebra R A] (n : ℕ) (s : k) (a : A) :
    PDivisibleGroup.Hopf.nsmulAlgHom k (k ⊗[R] A) n (s ⊗ₜ[R] a) = s ⊗ₜ[R] PDivisibleGroup.Hopf.nsmulAlgHom R A n a := by
  classical
  induction n generalizing s a with
  | zero =>
    rw [PDivisibleGroup.Hopf.nsmulAlgHom_zero_apply, PDivisibleGroup.Hopf.nsmulAlgHom_zero_apply,
      TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | succ n ih =>
    let 𝓡 := Coalgebra.Repr.arbitrary R a
    rw [PDivisibleGroup.Hopf.nsmulAlgHom_succ, PDivisibleGroup.Hopf.nsmulAlgHom_succ]
    show (WithConv.toConv (PDivisibleGroup.Hopf.nsmulAlgHom k (k ⊗[R] A) n) * WithConv.toConv (AlgHom.id k (k ⊗[R] A))) (s ⊗ₜ[R] a) =
      s ⊗ₜ[R] (WithConv.toConv (PDivisibleGroup.Hopf.nsmulAlgHom R A n) * WithConv.toConv (AlgHom.id R A)) a
    rw [AlgHom.convMul_apply, AlgHom.convMul_apply, TensorProduct.comul_tmul, CommSemiring.comul_apply, ← 𝓡.eq,
      TensorProduct.tmul_sum, map_sum, map_sum, map_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
    show PDivisibleGroup.Hopf.nsmulAlgHom k (k ⊗[R] A) n ((1 : k) ⊗ₜ[R] 𝓡.left i) * (s ⊗ₜ[R] 𝓡.right i) =
      s ⊗ₜ[R] (PDivisibleGroup.Hopf.nsmulAlgHom R A n (𝓡.left i) * 𝓡.right i)
    rw [ih, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end OrdAxis

namespace X1R

open AlgebraicGeometry.Scheme

universe u

theorem natCast_eq_zero_Γ_pullback {G S : Scheme.{u}} (g : G ⟶ S) {k : Type u} [CommRing k]
    (s : Spec (CommRingCat.of k) ⟶ S) {p : ℕ} (hk : (p : k) = 0) :
    (p : Γ(pullback g s, ⊤)) = 0 := by
  have h1 : (p : Γ(Spec (CommRingCat.of k), ⊤)) = 0 := natCast_eq_zero_ΓSpec hk
  have h2 := congrArg (fun t => (pullback.snd g s).appTop.hom t) h1
  simpa using h2

theorem frobenius_fst_comp_eq {G S : Scheme.{u}} (g : G ⟶ S) {k : Type u} [CommRing k]
    (s : Spec (CommRingCat.of k) ⟶ S) (p : ℕ) (hp : p.Prime) (hk : (p : k) = 0)
    (hs : (Spec (CommRingCat.of k)).frobenius p 1 hp (natCast_eq_zero_ΓSpec hk) ≫ s = s)
    (h0 : (p : Γ(pullback g s, ⊤)) = 0) :
    ((pullback g s).frobenius p 1 hp h0 ≫ pullback.fst g s) ≫ g = pullback.snd g s ≫ s := by
  rw [Category.assoc, pullback.condition, ← Category.assoc,
    frobenius_comp (pullback.snd g s) p 1 hp h0 (natCast_eq_zero_ΓSpec hk), Category.assoc, hs]

theorem pow_eq_of_ringHom_ratLocalizedAt (p : ℕ) [hp : Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    (g : ModularCurve.XHDRLevel.R p →+* K) (x : ModularCurve.XHDRLevel.R p) : g x ^ p = g x := by
  have hfix : ∀ z : ZMod p, (algebraMap (ZMod p) K z) ^ p = algebraMap (ZMod p) K z := fun z => by
    rw [← map_pow, ZMod.pow_card]
  have hden : (x : ℚ).den.Coprime p := x.2
  have hx : x * ((x : ℚ).den : ModularCurve.XHDRLevel.R p) = (((x : ℚ).num : ℤ) : ModularCurve.XHDRLevel.R p) := by
    apply Subtype.ext
    push_cast
    exact Rat.mul_den_eq_num (x : ℚ)
  have h1 : g x * algebraMap (ZMod p) K ((x : ℚ).den : ZMod p) = algebraMap (ZMod p) K ((x : ℚ).num : ZMod p) := by
    have := congrArg g hx
    rw [map_mul, map_natCast, map_intCast] at this
    rwa [map_natCast, map_intCast]
  have hne : algebraMap (ZMod p) K ((x : ℚ).den : ZMod p) ≠ 0 := by
    rw [map_ne_zero_iff _ (algebraMap (ZMod p) K).injective, Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have h2 : p ∣ Nat.gcd (x : ℚ).den p := Nat.dvd_gcd hdvd dvd_rfl
    rw [hden.gcd_eq_one, Nat.dvd_one] at h2
    exact hp.out.one_lt.ne' h2
  have h2 : g x = algebraMap (ZMod p) K ((x : ℚ).num : ZMod p) * (algebraMap (ZMod p) K ((x : ℚ).den : ZMod p))⁻¹ :=
    (eq_mul_inv_iff_mul_eq₀ hne).mpr h1
  rw [h2, mul_pow, inv_pow, hfix, hfix]

theorem powChar_comp_ringHom_ratLocalizedAt (p : ℕ) [hp : Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    (hK : (p : K) = 0) (g : ModularCurve.XHDRLevel.R p →+* K) :
    (powCharRingHom K p 1 hp.out hK).comp g = g := by
  ext x
  simp only [RingHom.comp_apply, powCharRingHom_apply, pow_one, pow_eq_of_ringHom_ratLocalizedAt]

end X1R

namespace X1K

open AlgebraicGeometry.Scheme

noncomputable def npow {C : Type*} [Category C] {Y : C} (f : Y ⟶ Y) : ℕ → (Y ⟶ Y)
  | 0 => 𝟙 Y
  | n + 1 => npow f n ≫ f

@[scoped simp] theorem npow_zero {C : Type*} [Category C] {Y : C} (f : Y ⟶ Y) : npow f 0 = 𝟙 Y := rfl

theorem npow_succ {C : Type*} [Category C] {Y : C} (f : Y ⟶ Y) (n : ℕ) : npow f (n + 1) = npow f n ≫ f := rfl

theorem npow_comp_of_comp_eq {C : Type*} [Category C] {X Y : C} {b : X ⟶ X} {i : X ⟶ Y} {f : Y ⟶ Y}
    (h : b ≫ i = i ≫ f) (n : ℕ) : npow b n ≫ i = i ≫ npow f n := by
  induction n with
  | zero => simp
  | succ n ih => rw [npow_succ, npow_succ, Category.assoc, h, ← Category.assoc, ih, Category.assoc]

theorem specMap_of_eq_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    {f : R →+* T} {g : S →+* T} {h : R →+* S} (hfg : f = g.comp h) :
    Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom h) := by
  rw [hfg, CommRingCat.ofHom_comp, Spec.map_comp]

theorem specMap_ofHom_id (R : Type) [CommRing R] : Spec.map (CommRingCat.ofHom (RingHom.id R)) = 𝟙 _ := by
  rw [CommRingCat.ofHom_id]
  exact Spec.map_id _

noncomputable def frobAlgHom (p : ℕ) [hp : Fact p.Prime] (B : Type) [CommRing B] [Algebra (ZMod p) B] (k : ℕ) :
    B →ₐ[ZMod p] B :=
  { toRingHom := powCharRingHom B p k hp.out
      (by rw [← map_natCast (algebraMap (ZMod p) B), ZMod.natCast_self, map_zero])
    commutes' := fun r => by
      show (algebraMap (ZMod p) B r) ^ p ^ k = algebraMap (ZMod p) B r
      rw [← map_pow, ZMod.pow_card_pow] }

@[scoped simp] theorem frobAlgHom_apply (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] [Algebra (ZMod p) B] (k : ℕ) (x : B) :
    frobAlgHom p B k x = x ^ p ^ k := rfl

theorem eq_one_of_mul_self {R : Type} [CommRing R] {A T : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (t : T ⟶ Spec (CommRingCat.of R)) (y : SchemeHomOver t f)
    (hy : G.mul t y y = y) : y = G.one t := by
  calc y = G.mul t (G.one t) y := (G.one_mul t y).symm
    _ = G.mul t (G.mul t (G.inv t y) y) y := by rw [G.inv_mul_cancel]
    _ = G.mul t (G.inv t y) (G.mul t y y) := by rw [G.mul_assoc]
    _ = G.mul t (G.inv t y) y := by rw [hy]
    _ = G.one t := G.inv_mul_cancel t y

set_option maxHeartbeats 12800000 in

theorem kill (p : ℕ) [hp : Fact p.Prime]
    {k : Type} [CommRing k] [Algebra (ZMod p) k] (hk0 : (p : k) = 0)
    {G L S : Scheme.{0}} (g : G ⟶ S) (f : L ⟶ S) (s : Spec (CommRingCat.of k) ⟶ S)
    (hs : (Spec (CommRingCat.of k)).frobenius p 1 hp.out (natCast_eq_zero_ΓSpec hk0) ≫ s = s)
    (a : pullback g s ⟶ pullback f s) (ha : a ≫ pullback.snd f s = pullback.snd g s)
    (e : Spec (CommRingCat.of k) ⟶ pullback f s)
    (U : pullback g s ⟶ pullback g s)
    (h0 : (p : Γ(pullback f s, ⊤)) = 0)
    (hΦ : ((pullback f s).frobenius p 1 hp.out h0 ≫ pullback.fst f s) ≫ f = pullback.snd f s ≫ s)
    (D : pullback f s ⟶ pullback f s) (hD : D ≫ pullback.snd f s = pullback.snd f s)
    (hUa : U ≫ a = a ≫ pullback.lift ((pullback f s).frobenius p 1 hp.out h0 ≫ pullback.fst f s) (pullback.snd f s) hΦ ≫ D)
    (B Gc : Type) [CommRing B] [HopfAlgebra (ZMod p) B] [CommRing Gc] [HopfAlgebra (ZMod p) Gc]
    [Module.Finite (ZMod p) Gc] (hGc : IsLocalRing Gc)
    (qc : B →ₐc[ZMod p] Gc) (ε u w : B →ₐc[ZMod p] B)
    (hwuε : ∀ b, w (u (ε b)) = ε b) (hεu : ∀ b, ε (u b) = u (ε b))
    (ι : Spec (CommRingCat.of (k ⊗[ZMod p] B)) ⟶ pullback g s)
    (hιs : ι ≫ pullback.snd g s = Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] B) Algebra.TensorProduct.includeLeftRingHom))
    (hU : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k k) (u : B →ₐ[ZMod p] B)).toRingHom) ≫ ι = ι ≫ U)
    (heG : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lift (AlgHom.id k k) ((Algebra.ofId (ZMod p) k).comp (Bialgebra.counitAlgHom (ZMod p) B)) (fun _ _ => Commute.all _ _)).toRingHom) ≫ ι ≫ a = e) :
    ∃ pr : Spec (CommRingCat.of (k ⊗[ZMod p] Gc)) ⟶ pullback a e,
      Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.map (AlgHom.id k k) (qc : B →ₐ[ZMod p] Gc)).comp (Algebra.TensorProduct.map (AlgHom.id k k) (ε : B →ₐ[ZMod p] B))).toRingHom) ≫ ι = pr ≫ pullback.fst a e := by
  classical

  obtain ⟨N, -, hN⟩ := HopfAlgebra.exists_forall_pow_pow_eq_algebraMap_counit_of_isLocalRing_zmodp p Gc hGc

  have hiter : ∀ (n : ℕ) (b : B), ε b = (⇑w)^[n] (ε ((⇑u)^[n] b)) := by
    intro n
    induction n with
    | zero => intro b; rfl
    | succ n ih =>
      intro b
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply, ← ih (u b), hεu, hwuε]

  have hUn : ∀ n : ℕ, Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k k)
      ((u : B →ₐ[ZMod p] B) ^ n)).toRingHom) ≫ ι = ι ≫ npow U n := by
    intro n
    induction n with
    | zero =>
      have h1 : (Algebra.TensorProduct.map (AlgHom.id k k) ((u : B →ₐ[ZMod p] B) ^ 0)).toRingHom = RingHom.id _ := by
        apply RingHom.ext
        intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul c b => simp
        | add x y hx hy => simp only [map_add, hx, hy]
      rw [h1, specMap_ofHom_id, Category.id_comp, npow_zero, Category.comp_id]
    | succ n ih =>
      have h1 : (Algebra.TensorProduct.map (AlgHom.id k k) ((u : B →ₐ[ZMod p] B) ^ (n + 1))).toRingHom =
          (Algebra.TensorProduct.map (AlgHom.id k k) ((u : B →ₐ[ZMod p] B) ^ n)).toRingHom.comp
            (Algebra.TensorProduct.map (AlgHom.id k k) (u : B →ₐ[ZMod p] B)).toRingHom := by
        apply RingHom.ext
        intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul c b => simp [pow_succ, AlgHom.mul_apply]
        | add x y hx hy => simp only [map_add, hx, hy]
      rw [specMap_of_eq_comp h1, Category.assoc, hU, ← Category.assoc, ih, Category.assoc, npow_succ]

  have hUan := npow_comp_of_comp_eq hUa

  have hXD : ∀ (m : Spec (CommRingCat.of (k ⊗[ZMod p] Gc)) ⟶ L)
      (hm : m ≫ f = Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] Gc) Algebra.TensorProduct.includeLeftRingHom) ≫ s),
      ∃ (m' : Spec (CommRingCat.of (k ⊗[ZMod p] Gc)) ⟶ L) (hm' : m' ≫ f = Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] Gc) Algebra.TensorProduct.includeLeftRingHom) ≫ s),
        pullback.lift m (Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] Gc) Algebra.TensorProduct.includeLeftRingHom)) hm ≫ D = pullback.lift m' (Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] Gc) Algebra.TensorProduct.includeLeftRingHom)) hm' := by
    intro m hm
    refine ⟨pullback.lift m _ hm ≫ D ≫ pullback.fst f s, ?_, ?_⟩
    · simp only [Category.assoc, pullback.condition]
      rw [← Category.assoc D, hD, ← Category.assoc, pullback.lift_snd]
    · apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst]
      · simp only [Category.assoc, pullback.lift_snd, hD]

  have hA0 : (p : k ⊗[ZMod p] Gc) = 0 := by
    rw [← map_natCast (algebraMap (ZMod p) (k ⊗[ZMod p] Gc)), ZMod.natCast_self, map_zero]
  have hsplit : powCharRingHom (k ⊗[ZMod p] Gc) p 1 hp.out hA0 =
      (Algebra.TensorProduct.map (AlgHom.id k k) (frobAlgHom p Gc 1)).toRingHom.comp
        (Algebra.TensorProduct.map (frobAlgHom p k 1) (AlgHom.id (ZMod p) Gc)).toRingHom := by
    apply RingHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [hp.out.ne_zero]
    | tmul c b => simp [Algebra.TensorProduct.tmul_pow]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hkil : (Algebra.TensorProduct.map (frobAlgHom p k 1) (AlgHom.id (ZMod p) Gc)).toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom : k →+* k ⊗[ZMod p] Gc) =
      ((Algebra.TensorProduct.includeLeftRingHom : k →+* k ⊗[ZMod p] Gc)).comp (powCharRingHom k p 1 hp.out hk0) := by
    ext c
    simp
  have hgil : ∀ j : ℕ, (Algebra.TensorProduct.map (AlgHom.id k k) (frobAlgHom p Gc j)).toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom : k →+* k ⊗[ZMod p] Gc) =
      (Algebra.TensorProduct.includeLeftRingHom : k →+* k ⊗[ZMod p] Gc) := by
    intro j
    ext c
    simp
  have hXF : ∀ (m : Spec (CommRingCat.of (k ⊗[ZMod p] Gc)) ⟶ L)
      (hm : m ≫ f = Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] Gc) Algebra.TensorProduct.includeLeftRingHom) ≫ s),
      ∃ (m' : Spec (CommRingCat.of (k ⊗[ZMod p] Gc)) ⟶ L) (hm' : m' ≫ f = Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] Gc) Algebra.TensorProduct.includeLeftRingHom) ≫ s),
        pullback.lift m (Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] Gc) Algebra.TensorProduct.includeLeftRingHom)) hm ≫ pullback.lift ((pullback f s).frobenius p 1 hp.out h0 ≫ pullback.fst f s) (pullback.snd f s) hΦ =
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k k) (frobAlgHom p Gc 1)).toRingHom) ≫ pullback.lift m' (Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] Gc) Algebra.TensorProduct.includeLeftRingHom)) hm' := by
    intro m hm
    refine ⟨Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (frobAlgHom p k 1) (AlgHom.id (ZMod p) Gc)).toRingHom) ≫ m, ?_, ?_⟩
    · rw [Category.assoc, hm, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hkil,
        CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ← frobenius_Spec p 1 hp.out hk0, hs]
    · apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst]
        rw [← frobenius_comp_assoc (pullback.lift m (Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] Gc) Algebra.TensorProduct.includeLeftRingHom)) hm) p 1 hp.out (natCast_eq_zero_ΓSpec hA0) h0,
          pullback.lift_fst, frobenius_Spec p 1 hp.out hA0, hsplit, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      · simp only [Category.assoc, pullback.lift_snd]
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hgil]

  have hgg : ∀ j : ℕ, (Algebra.TensorProduct.map (AlgHom.id k k) (frobAlgHom p Gc (j + 1))).toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id k k) (frobAlgHom p Gc j)).toRingHom.comp (Algebra.TensorProduct.map (AlgHom.id k k) (frobAlgHom p Gc 1)).toRingHom := by
    intro j
    apply RingHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c b =>
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_comp, Function.comp_apply,
        Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, frobAlgHom_apply]
      rw [← pow_mul, pow_one, ← pow_succ']
    | add x y hx hy => simp only [map_add, hx, hy]

  have hclass : ∀ (n j : ℕ) (m : Spec (CommRingCat.of (k ⊗[ZMod p] Gc)) ⟶ L)
      (hm : m ≫ f = Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] Gc) Algebra.TensorProduct.includeLeftRingHom) ≫ s),
      ∃ (m' : Spec (CommRingCat.of (k ⊗[ZMod p] Gc)) ⟶ L) (hm' : m' ≫ f = Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] Gc) Algebra.TensorProduct.includeLeftRingHom) ≫ s),
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k k) (frobAlgHom p Gc j)).toRingHom) ≫ pullback.lift m (Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] Gc) Algebra.TensorProduct.includeLeftRingHom)) hm) ≫
            npow (pullback.lift ((pullback f s).frobenius p 1 hp.out h0 ≫ pullback.fst f s) (pullback.snd f s) hΦ ≫ D) n =
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k k) (frobAlgHom p Gc (j + n))).toRingHom) ≫ pullback.lift m' (Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] Gc) Algebra.TensorProduct.includeLeftRingHom)) hm' := by
    intro n
    induction n with
    | zero =>
      intro j m hm
      exact ⟨m, hm, by rw [npow_zero, Category.comp_id, Nat.add_zero]⟩
    | succ n ih =>
      intro j m hm
      obtain ⟨m₁, hm₁, h₁⟩ := ih j m hm
      obtain ⟨m₂, hm₂, h₂⟩ := hXF m₁ hm₁
      obtain ⟨m₃, hm₃, h₃⟩ := hXD m₂ hm₂
      refine ⟨m₃, hm₃, ?_⟩
      rw [npow_succ, ← Category.assoc _ (npow _ n), h₁, Category.assoc,
        ← Category.assoc (pullback.lift m₁ (Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] Gc) Algebra.TensorProduct.includeLeftRingHom)) hm₁), h₂, Category.assoc, h₃,
        ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hgg, ← Nat.add_assoc]

  have hθ : (Algebra.TensorProduct.map (AlgHom.id k k) (frobAlgHom p Gc N)).toRingHom =
      ((Algebra.TensorProduct.includeLeftRingHom : k →+* k ⊗[ZMod p] Gc)).comp (Algebra.TensorProduct.lift (AlgHom.id k k) ((Algebra.ofId (ZMod p) k).comp (Bialgebra.counitAlgHom (ZMod p) Gc)) (fun _ _ => Commute.all _ _)).toRingHom := by
    apply RingHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c b =>
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_comp, Function.comp_apply,
        Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, frobAlgHom_apply, hN,
        Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp, Algebra.ofId_apply, Bialgebra.counitAlgHom_apply,
        Algebra.TensorProduct.includeLeftRingHom_apply]
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, TensorProduct.smul_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hθil : ((Algebra.TensorProduct.lift (AlgHom.id k k) ((Algebra.ofId (ZMod p) k).comp (Bialgebra.counitAlgHom (ZMod p) Gc)) (fun _ _ => Commute.all _ _)).toRingHom).comp (Algebra.TensorProduct.includeLeftRingHom : k →+* k ⊗[ZMod p] Gc) = RingHom.id k := by
    ext c
    simp

  obtain ⟨yr, hyr⟩ : ∃ yr : k ⊗[ZMod p] B →+* k ⊗[ZMod p] Gc, yr = ((Algebra.TensorProduct.map (AlgHom.id k k) (qc : B →ₐ[ZMod p] Gc)).comp ((Algebra.TensorProduct.map (AlgHom.id k k) ((w : B →ₐ[ZMod p] B) ^ N)).comp (Algebra.TensorProduct.map (AlgHom.id k k) (ε : B →ₐ[ZMod p] B)))).toRingHom := ⟨_, rfl⟩
  have hε_fac : ((Algebra.TensorProduct.map (AlgHom.id k k) (qc : B →ₐ[ZMod p] Gc)).comp (Algebra.TensorProduct.map (AlgHom.id k k) (ε : B →ₐ[ZMod p] B))).toRingHom = yr.comp (Algebra.TensorProduct.map (AlgHom.id k k) ((u : B →ₐ[ZMod p] B) ^ N)).toRingHom := by
    rw [hyr]
    apply RingHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c b =>
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_comp, Function.comp_apply, AlgHom.coe_comp,
        Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, AlgHom.coe_pow, BialgHom.coe_toAlgHom]
      rw [← hiter N b]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hyr_il : yr.comp (Algebra.TensorProduct.includeLeftRingHom : k →+* k ⊗[ZMod p] B) = (Algebra.TensorProduct.includeLeftRingHom : k →+* k ⊗[ZMod p] Gc) := by
    rw [hyr]
    ext c
    simp

  have hz_snd : (Spec.map (CommRingCat.ofHom yr) ≫ ι ≫ a) ≫ pullback.snd f s = Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] Gc) Algebra.TensorProduct.includeLeftRingHom) := by
    rw [Category.assoc, Category.assoc, ha, hιs, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hyr_il]
  obtain ⟨m₀, hm₀, hz⟩ : ∃ (m₀ : Spec (CommRingCat.of (k ⊗[ZMod p] Gc)) ⟶ L) (hm₀ : m₀ ≫ f = Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] Gc) Algebra.TensorProduct.includeLeftRingHom) ≫ s),
      Spec.map (CommRingCat.ofHom yr) ≫ ι ≫ a = pullback.lift m₀ (Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] Gc) Algebra.TensorProduct.includeLeftRingHom)) hm₀ := by
    refine ⟨(Spec.map (CommRingCat.ofHom yr) ≫ ι ≫ a) ≫ pullback.fst f s, ?_, ?_⟩
    · rw [Category.assoc, pullback.condition, ← Category.assoc, hz_snd]
    · apply pullback.hom_ext
      · rw [pullback.lift_fst]
      · rw [pullback.lift_snd, hz_snd]
  have hgg0 : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k k) (frobAlgHom p Gc 0)).toRingHom) = 𝟙 _ := by
    have h1 : (Algebra.TensorProduct.map (AlgHom.id k k) (frobAlgHom p Gc 0)).toRingHom = RingHom.id _ := by
      apply RingHom.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul c b => simp
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [h1, specMap_ofHom_id]
  obtain ⟨m', hm', hcl⟩ := hclass N 0 m₀ hm₀
  have hconst : Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.map (AlgHom.id k k) (qc : B →ₐ[ZMod p] Gc)).comp (Algebra.TensorProduct.map (AlgHom.id k k) (ε : B →ₐ[ZMod p] B))).toRingHom) ≫ ι ≫ a =
      Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] Gc) Algebra.TensorProduct.includeLeftRingHom) ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lift (AlgHom.id k k) ((Algebra.ofId (ZMod p) k).comp (Bialgebra.counitAlgHom (ZMod p) Gc)) (fun _ _ => Commute.all _ _)).toRingHom) ≫
        pullback.lift m' (Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] Gc) Algebra.TensorProduct.includeLeftRingHom)) hm' := by
    calc Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.map (AlgHom.id k k) (qc : B →ₐ[ZMod p] Gc)).comp (Algebra.TensorProduct.map (AlgHom.id k k) (ε : B →ₐ[ZMod p] B))).toRingHom) ≫ ι ≫ a
        = (Spec.map (CommRingCat.ofHom yr) ≫ ι ≫ a) ≫ npow (pullback.lift ((pullback f s).frobenius p 1 hp.out h0 ≫ pullback.fst f s) (pullback.snd f s) hΦ ≫ D) N := by
          rw [specMap_of_eq_comp hε_fac]
          simp only [Category.assoc]
          rw [reassoc_of% (hUn N), hUan N]
      _ = (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k k) (frobAlgHom p Gc 0)).toRingHom) ≫ pullback.lift m₀ (Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] Gc) Algebra.TensorProduct.includeLeftRingHom)) hm₀) ≫
            npow (pullback.lift ((pullback f s).frobenius p 1 hp.out h0 ≫ pullback.fst f s) (pullback.snd f s) hΦ ≫ D) N := by rw [hz, hgg0, Category.id_comp]
      _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k k) (frobAlgHom p Gc (0 + N))).toRingHom) ≫ pullback.lift m' (Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] Gc) Algebra.TensorProduct.includeLeftRingHom)) hm' := hcl
      _ = _ := by rw [Nat.zero_add, specMap_of_eq_comp hθ, Category.assoc]

  have hx0 : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lift (AlgHom.id k k) ((Algebra.ofId (ZMod p) k).comp (Bialgebra.counitAlgHom (ZMod p) Gc)) (fun _ _ => Commute.all _ _)).toRingHom) ≫ Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] Gc) Algebra.TensorProduct.includeLeftRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hθil, specMap_ofHom_id]
  have hθπ : ((Algebra.TensorProduct.lift (AlgHom.id k k) ((Algebra.ofId (ZMod p) k).comp (Bialgebra.counitAlgHom (ZMod p) Gc)) (fun _ _ => Commute.all _ _)).toRingHom).comp ((Algebra.TensorProduct.map (AlgHom.id k k) (qc : B →ₐ[ZMod p] Gc)).comp (Algebra.TensorProduct.map (AlgHom.id k k) (ε : B →ₐ[ZMod p] B))).toRingHom = (Algebra.TensorProduct.lift (AlgHom.id k k) ((Algebra.ofId (ZMod p) k).comp (Bialgebra.counitAlgHom (ZMod p) B)) (fun _ _ => Commute.all _ _)).toRingHom := by
    apply RingHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c b => simp [Algebra.TensorProduct.lift_tmul, CoalgHomClass.counit_comp_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hQ : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lift (AlgHom.id k k) ((Algebra.ofId (ZMod p) k).comp (Bialgebra.counitAlgHom (ZMod p) Gc)) (fun _ _ => Commute.all _ _)).toRingHom) ≫ pullback.lift m' (Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] Gc) Algebra.TensorProduct.includeLeftRingHom)) hm' = e := by
    symm
    calc e = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lift (AlgHom.id k k) ((Algebra.ofId (ZMod p) k).comp (Bialgebra.counitAlgHom (ZMod p) B)) (fun _ _ => Commute.all _ _)).toRingHom) ≫ ι ≫ a := heG.symm
      _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lift (AlgHom.id k k) ((Algebra.ofId (ZMod p) k).comp (Bialgebra.counitAlgHom (ZMod p) Gc)) (fun _ _ => Commute.all _ _)).toRingHom) ≫ Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.map (AlgHom.id k k) (qc : B →ₐ[ZMod p] Gc)).comp (Algebra.TensorProduct.map (AlgHom.id k k) (ε : B →ₐ[ZMod p] B))).toRingHom) ≫ ι ≫ a := by
          rw [specMap_of_eq_comp hθπ.symm, Category.assoc]
      _ = _ := by rw [hconst, ← Category.assoc, hx0, Category.id_comp]
  rw [hQ] at hconst
  refine ⟨pullback.lift (Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.map (AlgHom.id k k) (qc : B →ₐ[ZMod p] Gc)).comp (Algebra.TensorProduct.map (AlgHom.id k k) (ε : B →ₐ[ZMod p] B))).toRingHom) ≫ ι) (Spec.map (CommRingCat.ofHom (R := k) (S := k ⊗[ZMod p] Gc) Algebra.TensorProduct.includeLeftRingHom)) ?_, (pullback.lift_fst _ _ _).symm⟩
  rw [Category.assoc, hconst]

end X1K
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_mono_lift_and_exists_specMap_qc_comp_baseChange_comp_lift_eq_comp_pullbackFst_abqFibre_of_ordinaryIdempotent_of_bridge.X1K"

open ModularCurve ModularCurve.JHNeronObjectAtP in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)

    [Algebra Rh (ZMod p)]
    (hres : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)

    {h : ℕ} (𝒢 : PDivisibleGroup Rh p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H) (hΔ : Function.Injective Δ)
    (hfin : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.finPts (p ^ v) ↔
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (ρh : ModularCurve.XHDRLevel.R p →+* Rh) (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
    (hS0 : (algebraMap Rh (AlgebraicClosure ℚ)).comp ρh = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (hS1 : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
    (hS2 : ∀ (v : ℕ) (h1 : ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
          IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρh)) (ι v)
            (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h1))
    (hS3 : ∀ v : ℕ, ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
    (hS4 : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
          (O.pts (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))).1 =
            Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] (AlgebraicClosure ℚ)) : 𝒢.level v →+* (AlgebraicClosure ℚ))) ≫ ι v)
    (hS5 : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra Rh B] (x y : 𝒢.Point B v)
          (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)))
          (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh))),
          Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v =
            (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)) ⟨_, hx⟩ ⟨_, hy⟩).1)
    (hS6 : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (𝒢.transition v : 𝒢.level (v + 1) →+* 𝒢.level v)) ≫ ι (v + 1) = ι v)

    (hS8 : ∀ (v : ℕ)
          (h3 : ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
          (h4 : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3 ≫
              (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g) =
            Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
          let jv := pullback.lift
            (f := pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
            (g := Spec.map (CommRingCat.ofHom ρh))
            (pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3)
            (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h4
          IsOpenImmersion jv ∧ IsClosedImmersion jv ∧
          ∀ x : ↥(Limits.pullback (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
                  (Spec.map (CommRingCat.ofHom ρh))),
            (pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
                (Spec.map (CommRingCat.ofHom ρh))).base x = IsLocalRing.closedPoint Rh →
              x ∈ Set.range jv.base)

    (S : Set ℕ) (u : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v)
    (hu : ∀ v : ℕ, (𝒢.transition v).comp (u (v + 1)) = (u v).comp (𝒢.transition v))
    (huι : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (u v : 𝒢.level v →+* 𝒢.level v)) ≫ ι v =
      ι v ≫ (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).1)

    [NeZero (M / p)]
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

    (hsp : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (x : ↥(GluingData.admissible O.ssFinset))
      (_ : (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.2 = 0),
      ∃ s : SchemeHomOver Λ.σA O.g,
        (O.pts (Pic0.mk Dv)).1 = barPt Pl ≫ s.1 ∧
        O.ptsSp.symm (schemeHomOverComp ⟨resPt Pl, rfl⟩ s) = GluedPic0.mk O.ssFinset x)

    (hspΛ : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ).base Q₁.1 =
        (uκ₁ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥Pl).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ).base Q₂.1 =
        (uκ₂ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥Pl).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (Dw : Divisor.degZero (K := ResidueField ↥Pl) (F := Fbar p M H hpM (ResidueField ↥Pl)))
      (_ : (Dw : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) =
        Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Q₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver Λ.σA Λ.f,
        (Λ.pts (O.degPts i (Pic0.mk Dv))).1 = barPt Pl ≫ s₀.1 ∧
        Λ.ptsSp.symm (schemeHomOverComp ⟨resPt Pl, rfl⟩ s₀) = Pic0.mk Dw)

    (hdia0 : ∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C),
      ∃ h : (inv (𝔛.efib Pl hPl ρ hρ)).base
          ((fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥Pl).comp ρ)).base
            ((𝔛.efib Pl hPl ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib Pl hPl ρ hρ).C,
        (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P)

    (F Finv Fstar : Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) →+
      Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥Pl) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) →+
      Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)

    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)

    (hpull_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      schemeHomOverComp (Λ.L.mul s x y) (degPull i) =
        O.L.mul s (schemeHomOverComp x (degPull i)) (schemeHomOverComp y (degPull i)))

    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt Pl ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))

    (Wbar : JH M H →+ JH M H)
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hWbar : ∀ x : JH M H, Wbar x = wgen • x)
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)

    (hUPgen : ∀ x : JH M H,
      genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) x + Wbar x = αpull 1 (O.degPts 0 x))

    (σ : ↥O.ssFinset ≃ ↥O.ssFinset)
    (hσ : ∀ n : ↥O.ssFinset, (σ n).1.2 = n.1.1)

    (Φ : Place (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) ≃ Place (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)))
    (hΦ : ∀ v, Φ v = qExpFrobeniusPlaceModL (ResidueField ↥Pl) (ΓN p M H hpM) p v)
    (hFdiv : ∀ (D D' : Divisor.degZero (K := ResidueField ↥Pl) (F := Fbar p M H hpM (ResidueField ↥Pl))),
      (D' : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) =
        Finsupp.mapDomain Φ (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) →
      F (Pic0.mk D) = Pic0.mk D')

    (hpull1sp : ∀ (D : Divisor.degZero (K := ResidueField ↥Pl) (F := Fbar p M H hpM (ResidueField ↥Pl)))
      (x₁ : ↥(GluingData.admissible O.ssFinset)),
      (∀ s ∈ O.ssFinset, (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) s.1 = 0 ∧
        (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) (Φ s.1) = 0) →
      (x₁ : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).1 =
        (p : ℤ) • Finsupp.mapDomain Φ.symm (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) →
      (x₁ : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.1 =
        SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
          (CuspForm.gammaLift (M / p) pb)) • (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) →
      (x₁ : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.2 = 0 →
      O.ptsSp.symm (schemeHomOverComp (Λ.ptsSp (Pic0.mk D)) (degPull 1)) = GluedPic0.mk O.ssFinset x₁)

    (ε w : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v)
    (hεε : ∀ v : ℕ, (ε v).comp (ε v) = ε v)
    (hεtr : ∀ v : ℕ, (𝒢.transition v).comp (ε (v + 1)) = (ε v).comp (𝒢.transition v))
    (hεu : ∀ v : ℕ, (ε v).comp (u v) = (u v).comp (ε v))
    (hwtr : ∀ v : ℕ, (𝒢.transition v).comp (w (v + 1)) = (w v).comp (𝒢.transition v))
    (hεw : ∀ v : ℕ, (ε v).comp (w v) = w v) (hwε : ∀ v : ℕ, (w v).comp (ε v) = w v)
    (hwuε : ∀ v : ℕ, (w v).comp ((u v).comp (ε v)) = ε v)
    (huεw : ∀ v : ℕ, ((u v).comp (ε v)).comp (w v) = ε v)

    (v : ℕ)
    [Algebra (ZMod p) (ResidueField ↥Pl)] [Algebra Rh (ResidueField ↥Pl)] [IsScalarTower Rh (ZMod p) (ResidueField ↥Pl)]
    (hrκ : ∀ x : Rh, algebraMap Rh (ResidueField ↥Pl) x = IsLocalRing.residue ↥Pl ⟨algebraMap Rh (AlgebraicClosure ℚ) x, hRA x⟩)

    (hsq : (Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))).toRingHom.comp
        (Algebra.TensorProduct.includeRight : 𝒢.level v →ₐ[Rh] (ZMod p ⊗[Rh] 𝒢.level v)).toRingHom)) ≫ ι v) ≫ O.g =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : (ResidueField ↥Pl) →+* ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v)))) ≫ (resPt Pl ≫ Λ.σA))

    (Gc : Type) [CommRing Gc] [HopfAlgebra (ZMod p) Gc] [Coalgebra.IsCocomm (ZMod p) Gc] [Module.Finite (ZMod p) Gc]
    (Ge : Type) [CommRing Ge] [HopfAlgebra (ZMod p) Ge] [Coalgebra.IsCocomm (ZMod p) Ge] [Module.Finite (ZMod p) Ge]
    (qc : (ZMod p ⊗[Rh] 𝒢.level v) →ₐc[ZMod p] Gc) (πe : (ZMod p ⊗[Rh] 𝒢.level v) →ₐc[ZMod p] Ge)
    (Θ : (ZMod p ⊗[Rh] 𝒢.level v) →ₐc[ZMod p] Gc ⊗[ZMod p] Ge)
    (hGc : IsLocalRing Gc) (hGe : IsReduced Ge) (hqc : Function.Surjective qc) (hπe : Function.Surjective πe)
    (hΘ : Function.Bijective Θ)
    (hΘ' : ∀ b, Θ b = Algebra.TensorProduct.map (qc : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] Gc)
      (πe : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] Ge) (Coalgebra.comul (R := ZMod p) b)) :
    Mono (pullback.lift (f := O.g) (g := (resPt Pl ≫ Λ.σA)) _ _ hsq) ∧

    (∃ pr : Spec (CommRingCat.of ((ResidueField ↥Pl) ⊗[ZMod p] Gc)) ⟶
          Limits.pullback (O.abqFibre 1).1 ((Λ.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)).1,
      Spec.map (CommRingCat.ofHom (((Algebra.TensorProduct.map (AlgHom.id (ResidueField ↥Pl) (ResidueField ↥Pl))
          (qc : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] Gc)).comp
        (Algebra.TensorProduct.map (AlgHom.id (ResidueField ↥Pl) (ResidueField ↥Pl))
          ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) :
            (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))))).toRingHom) ≫ pullback.lift (f := O.g) (g := (resPt Pl ≫ Λ.σA)) _ _ hsq =
        pr ≫ pullback.fst (O.abqFibre 1).1 ((Λ.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)).1) ∧
    Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.map (AlgHom.id (ResidueField ↥Pl) (ResidueField ↥Pl))
        (PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v) p)).toRingHom)) ≫
        pullback.lift (f := O.g) (g := (resPt Pl ≫ Λ.σA)) _ _ hsq =
      pullback.lift (f := O.g) (g := (resPt Pl ≫ Λ.σA)) _ _ hsq ≫
        pullback.map O.g (resPt Pl ≫ Λ.σA) O.g (resPt Pl ≫ Λ.σA) (O.L.schemeNsmul p) (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id]; exact (O.L.schemeNsmul_over p).symm) (by rw [Category.comp_id, Category.id_comp]) := by
  classical

  have hs : resPt Pl ≫ Λ.σA = Spec.map (CommRingCat.ofHom (algebraMap Rh (ResidueField ↥Pl))) ≫ Spec.map (CommRingCat.ofHom ρh) := by
    rw [hσA]
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    have e1 : (⟨algebraMap Rh (AlgebraicClosure ℚ) (ρh x), hRA _⟩ : ↥Pl) = ρ x := Subtype.ext (by
      change algebraMap Rh (AlgebraicClosure ℚ) (ρh x) = Pl.subtype (ρ x)
      rw [← RingHom.comp_apply (algebraMap Rh (AlgebraicClosure ℚ)) ρh, hS0, ← RingHom.comp_apply Pl.subtype ρ, hρ])
    show IsLocalRing.residue ↥Pl (ρ x) = algebraMap Rh (ResidueField ↥Pl) (ρh x)
    rw [hrκ, e1]

  refine ⟨?_, ?_, ?_⟩
  ·
    have hA : IsPullback (Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))).toRingHom.comp (Algebra.TensorProduct.includeRight : 𝒢.level v →ₐ[Rh] (ZMod p ⊗[Rh] 𝒢.level v)).toRingHom)))
        ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : (ResidueField ↥Pl) →+* ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))))) : Spec (CommRingCat.of ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))) ⟶ _)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) (Spec.map (CommRingCat.ofHom (algebraMap Rh (ResidueField ↥Pl)))) := by

      let φ : (𝒢.level v ⊗[Rh] (ResidueField ↥Pl)) ≃+* ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v)) :=
        (Algebra.TensorProduct.comm Rh (𝒢.level v) (ResidueField ↥Pl)).toRingEquiv.trans
          (Algebra.TensorProduct.cancelBaseChange Rh (ZMod p) (ResidueField ↥Pl) (ResidueField ↥Pl) (𝒢.level v)).symm.toRingEquiv
      have hφl : φ.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom : 𝒢.level v →+* 𝒢.level v ⊗[Rh] (ResidueField ↥Pl)) =
          ((Algebra.TensorProduct.includeRight : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))).toRingHom.comp (Algebra.TensorProduct.includeRight : 𝒢.level v →ₐ[Rh] (ZMod p ⊗[Rh] 𝒢.level v)).toRingHom) := by
        ext x
        show φ (x ⊗ₜ[Rh] 1) = (1 : ResidueField ↥Pl) ⊗ₜ[ZMod p] ((1 : ZMod p) ⊗ₜ[Rh] x)
        show (Algebra.TensorProduct.cancelBaseChange Rh (ZMod p) (ResidueField ↥Pl) (ResidueField ↥Pl) (𝒢.level v)).symm
          ((Algebra.TensorProduct.comm Rh (𝒢.level v) (ResidueField ↥Pl)) (x ⊗ₜ[Rh] 1)) = _
        rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.cancelBaseChange_symm_tmul]
      have hφr : φ.toRingHom.comp ((Algebra.TensorProduct.includeRight : (ResidueField ↥Pl) →ₐ[Rh] 𝒢.level v ⊗[Rh] (ResidueField ↥Pl)).toRingHom) =
          (Algebra.TensorProduct.includeLeftRingHom : (ResidueField ↥Pl) →+* ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))) := by
        ext a
        show φ (1 ⊗ₜ[Rh] a) = a ⊗ₜ[ZMod p] 1
        show (Algebra.TensorProduct.cancelBaseChange Rh (ZMod p) (ResidueField ↥Pl) (ResidueField ↥Pl) (𝒢.level v)).symm
          ((Algebra.TensorProduct.comm Rh (𝒢.level v) (ResidueField ↥Pl)) (1 ⊗ₜ[Rh] a)) = _
        rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.cancelBaseChange_symm_tmul]
        rfl
      let i₀ : Spec (CommRingCat.of ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))) ≅ Spec (CommRingCat.of (𝒢.level v ⊗[Rh] (ResidueField ↥Pl))) :=
        { hom := Spec.map (CommRingCat.ofHom (R := 𝒢.level v ⊗[Rh] (ResidueField ↥Pl)) (S := (ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v)) φ.toRingHom)
          inv := Spec.map (CommRingCat.ofHom (R := (ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v)) (S := 𝒢.level v ⊗[Rh] (ResidueField ↥Pl)) φ.symm.toRingHom)
          hom_inv_id := by
            rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, RingEquiv.toRingHom_comp_symm_toRingHom]
            exact Spec.map_id _
          inv_hom_id := by
            rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, RingEquiv.symm_toRingHom_comp_toRingHom]
            exact Spec.map_id _ }
      let i : Spec (CommRingCat.of ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))) ≅
          pullback (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) (Spec.map (CommRingCat.ofHom (algebraMap Rh (ResidueField ↥Pl)))) :=
        i₀ ≪≫ (pullbackSpecIso Rh (𝒢.level v) (ResidueField ↥Pl)).symm
      have w1 : i.hom ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))).toRingHom.comp (Algebra.TensorProduct.includeRight : 𝒢.level v →ₐ[Rh] (ZMod p ⊗[Rh] 𝒢.level v)).toRingHom)) := by
        show (Spec.map (CommRingCat.ofHom (R := 𝒢.level v ⊗[Rh] (ResidueField ↥Pl)) (S := (ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v)) φ.toRingHom) ≫ (pullbackSpecIso Rh (𝒢.level v) (ResidueField ↥Pl)).inv) ≫ pullback.fst _ _ = _
        rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφl]
      have w2 : i.hom ≫ pullback.snd _ _ = ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : (ResidueField ↥Pl) →+* ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))))) : Spec (CommRingCat.of ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))) ⟶ _) := by
        show (Spec.map (CommRingCat.ofHom (R := 𝒢.level v ⊗[Rh] (ResidueField ↥Pl)) (S := (ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v)) φ.toRingHom) ≫ (pullbackSpecIso Rh (𝒢.level v) (ResidueField ↥Pl)).inv) ≫ pullback.snd _ _ = _
        rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
      refine IsPullback.of_iso_pullback ⟨?_⟩ i w1 w2
      rw [← w1, ← w2, Category.assoc, Category.assoc, pullback.condition]

    haveI := AlgebraicGeometry.isClosedImmersion_pullbackLift_of_isClosedImmersion_pullbackLift_of_isPullback O.g (Spec.map (CommRingCat.ofHom ρh)) (ι v) (hS1 v) (hS2 v (hS1 v))
      (resPt Pl ≫ Λ.σA) hs _ _ hA hsq
    infer_instance
  ·
    have hp : p.Prime := Fact.out
    have hκ0 : (p : ResidueField ↥Pl) = 0 := CharP.cast_eq_zero _ p

    have hsfix : (Spec (CommRingCat.of (ResidueField ↥Pl))).frobenius p 1 hp (Scheme.natCast_eq_zero_ΓSpec hκ0) ≫
        (resPt Pl ≫ Λ.σA) = resPt Pl ≫ Λ.σA := by
      rw [Scheme.frobenius_Spec p 1 hp hκ0, hσA]
      simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact X1R.powChar_comp_ringHom_ratLocalizedAt p hκ0 ((IsLocalRing.residue ↥Pl).comp ρ)

    have hp0Λ : (p : Γ(RelativeGroupLaw.baseChangeScheme (resPt Pl ≫ Λ.σA) Λ.f, ⊤)) = 0 :=
      X1R.natCast_eq_zero_Γ_pullback Λ.f (resPt Pl ≫ Λ.σA) hκ0
    have hΦΛ := X1R.frobenius_fst_comp_eq Λ.f (resPt Pl ≫ Λ.σA) p hp hκ0 hsfix hp0Λ

    have hABQ := ModularCurve.JHNeronObjectAtP.exists_abqFibre_one_comp_baseChange_hecke_U_eq_comp_relFrobenius_comp_abqFibre_one_of_not_sq_dvd
      p M H hpM hpM2 hHp hj 𝔛 Pl hPl Λ O ρ hρ hσA hsp hspΛ hdia0 F Finv Fstar hF hFinv hFstar pb hpb δ hδ αpull degPull hpull hpullsp
      Wbar wgen hWbar hwgen S hUPgen hp0Λ hΦΛ
    obtain ⟨D, hD⟩ := hABQ
    have hUa := congrArg Subtype.val hD
    simp only [NeronModelInfra.schemeHomOverComp_coe] at hUa

    have hUsq := AlgebraicGeometry.specMap_comp_pullbackLift_eq_pullbackLift_comp_pullbackMap_of_comp_eq_comp
      O.g (resPt Pl ≫ Λ.σA) (ι v) (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).1 (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).2
      (u v : 𝒢.level v →+* 𝒢.level v) (huι v) _ _ hsq
      (Algebra.TensorProduct.map (AlgHom.id (ResidueField ↥Pl) (ResidueField ↥Pl))
        (((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (u v)) : (ZMod p ⊗[Rh] 𝒢.level v) →ₐc[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v)) : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))).toRingHom
      (by ext x; simp) (by ext c; simp)

    have hwuε1 : ∀ b : (ZMod p ⊗[Rh] 𝒢.level v), (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (w v)) ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (u v)) ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) b)) = (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) b := by
      intro b
      have h0 : ∀ x, w v (u v (ε v x)) = ε v x := fun x => by simpa using DFunLike.congr_fun (hwuε v) x
      induction b using TensorProduct.induction_on with
      | zero => simp
      | tmul c x => simp [h0]
      | add x y hx hy => simp only [map_add, hx, hy]
    have hεu1 : ∀ b : (ZMod p ⊗[Rh] 𝒢.level v), (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (u v)) b) = (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (u v)) ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) b) := by
      intro b
      have h0 : ∀ x, ε v (u v x) = u v (ε v x) := fun x => by simpa using DFunLike.congr_fun (hεu v) x
      induction b using TensorProduct.induction_on with
      | zero => simp
      | tmul c x => simp [h0]
      | add x y hx hy => simp only [map_add, hx, hy]

    have hθil : ((Algebra.TensorProduct.lift (AlgHom.id (ResidueField ↥Pl) (ResidueField ↥Pl)) ((Algebra.ofId (ZMod p) (ResidueField ↥Pl)).comp (Bialgebra.counitAlgHom (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v))) (fun _ _ => Commute.all _ _)).toRingHom).comp (Algebra.TensorProduct.includeLeftRingHom : (ResidueField ↥Pl) →+* ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))) = RingHom.id _ := by
      ext c
      simp
    have hθtoA : ((Algebra.TensorProduct.lift (AlgHom.id (ResidueField ↥Pl) (ResidueField ↥Pl)) ((Algebra.ofId (ZMod p) (ResidueField ↥Pl)).comp (Bialgebra.counitAlgHom (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v))) (fun _ _ => Commute.all _ _)).toRingHom).comp ((Algebra.TensorProduct.includeRight : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))).toRingHom.comp (Algebra.TensorProduct.includeRight : 𝒢.level v →ₐ[Rh] (ZMod p ⊗[Rh] 𝒢.level v)).toRingHom) =
        ((algebraMap Rh (ResidueField ↥Pl)).comp ((Bialgebra.counitAlgHom Rh (𝒢.level v)).toRingHom)).comp
          (PDivisibleGroup.Hopf.nsmulAlgHom Rh (𝒢.level v) 0 : 𝒢.level v →+* 𝒢.level v) := by
      ext x
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.lift_tmul, AlgHom.coe_id, id_eq, AlgHom.coe_comp, Function.comp_apply, Algebra.ofId_apply,
        Bialgebra.counitAlgHom_apply, TensorProduct.counit_tmul, CommSemiring.counit_apply,
        PDivisibleGroup.Hopf.nsmulAlgHom_zero_apply, Bialgebra.counit_algebraMap, one_mul, map_one]
      rw [Algebra.smul_def, mul_one, ← IsScalarTower.algebraMap_apply]
    have hψ : (Spec.map (CommRingCat.ofHom ((algebraMap Rh (ResidueField ↥Pl)).comp ((Bialgebra.counitAlgHom Rh (𝒢.level v)).toRingHom))) ≫ ι v) ≫ O.g =
        𝟙 _ ≫ (resPt Pl ≫ Λ.σA) := by
      rw [Category.assoc, hS1 v, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Category.id_comp, hs]
      congr 3
      ext r
      simp [Bialgebra.counit_algebraMap]
    have hone_nat := congrArg Subtype.val (RelativeGroupLaw.one_natural O.L O.g (𝟙 _ ≫ (resPt Pl ≫ Λ.σA)) _ hψ)
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at hone_nat
    have hIN := ModularCurve.JHNeronObjectAtP.specMap_nsmulAlgHom_comp_eq_comp_schemeNsmul_of_forall_point_mul
      p M H hpM Pl hPl Λ O Rh 𝒢 ρh ι hS1 hS5 v 0
    have heGpt : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lift (AlgHom.id (ResidueField ↥Pl) (ResidueField ↥Pl)) ((Algebra.ofId (ZMod p) (ResidueField ↥Pl)).comp (Bialgebra.counitAlgHom (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v))) (fun _ _ => Commute.all _ _)).toRingHom) ≫ pullback.lift _ _ hsq =
        ((O.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)).1 := by
      rw [RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointOfBase_coe]
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          hθtoA, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hIN]
        show _ ≫ ι v ≫ (O.L.one O.g).1 = _
        rw [← Category.assoc, hone_nat]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hθil,
          X1K.specMap_ofHom_id]
    have heG : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lift (AlgHom.id (ResidueField ↥Pl) (ResidueField ↥Pl)) ((Algebra.ofId (ZMod p) (ResidueField ↥Pl)).comp (Bialgebra.counitAlgHom (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v))) (fun _ _ => Commute.all _ _)).toRingHom) ≫ pullback.lift _ _ hsq ≫ (O.abqFibre 1).1 =
        ((Λ.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)).1 := by
      have hone := X1K.eq_one_of_mul_self (Λ.L.baseChange (resPt Pl ≫ Λ.σA)) (𝟙 _)
        (NeronModelInfra.schemeHomOverComp ((O.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)) (O.abqFibre 1)) (by
          have hm := O.abqFibre_mul 1 (𝟙 _) ((O.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)) ((O.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _))
          rw [(O.L.baseChange (resPt Pl ≫ Λ.σA)).one_mul] at hm
          exact hm.symm)
      have h1 := congrArg Subtype.val hone
      rw [NeronModelInfra.schemeHomOverComp_coe, ← heGpt, Category.assoc] at h1
      exact h1

    exact X1K.kill p hκ0 O.g Λ.f (resPt Pl ≫ Λ.σA) hsfix (O.abqFibre 1).1 (O.abqFibre 1).2
      ((Λ.L.baseChange (resPt Pl ≫ Λ.σA)).one (𝟙 _)).1 _ hp0Λ hΦΛ D.1 D.2 hUa
      (ZMod p ⊗[Rh] 𝒢.level v) Gc hGc qc (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (u v)) (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (w v)) hwuε1 hεu1
      (pullback.lift _ _ hsq) (pullback.lift_snd _ _ _) hUsq heG
  ·
    have hea : ((Algebra.TensorProduct.map (AlgHom.id (ResidueField ↥Pl) (ResidueField ↥Pl)) (PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v) p)).toRingHom).comp ((Algebra.TensorProduct.includeRight : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))).toRingHom.comp (Algebra.TensorProduct.includeRight : 𝒢.level v →ₐ[Rh] (ZMod p ⊗[Rh] 𝒢.level v)).toRingHom) =
        (((Algebra.TensorProduct.includeRight : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))).toRingHom.comp (Algebra.TensorProduct.includeRight : 𝒢.level v →ₐ[Rh] (ZMod p ⊗[Rh] 𝒢.level v)).toRingHom)).comp (PDivisibleGroup.Hopf.nsmulAlgHom Rh (𝒢.level v) p : 𝒢.level v →+* 𝒢.level v) := by
      ext x
      show Algebra.TensorProduct.map (AlgHom.id (ResidueField ↥Pl) (ResidueField ↥Pl)) (PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v) p)
          ((1 : ResidueField ↥Pl) ⊗ₜ[ZMod p] ((1 : ZMod p) ⊗ₜ[Rh] x)) =
        (1 : ResidueField ↥Pl) ⊗ₜ[ZMod p] ((1 : ZMod p) ⊗ₜ[Rh] (PDivisibleGroup.Hopf.nsmulAlgHom Rh (𝒢.level v) p x))
      rw [Algebra.TensorProduct.map_tmul, OrdAxis.nsmulAlgHom_tmul]
      rfl
    have hec : ((Algebra.TensorProduct.map (AlgHom.id (ResidueField ↥Pl) (ResidueField ↥Pl)) (PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v) p)).toRingHom).comp (Algebra.TensorProduct.includeLeftRingHom : (ResidueField ↥Pl) →+* ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))) =
        (Algebra.TensorProduct.includeLeftRingHom : (ResidueField ↥Pl) →+* ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))) := by
      ext a
      show Algebra.TensorProduct.map (AlgHom.id (ResidueField ↥Pl) (ResidueField ↥Pl)) (PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v) p)
          (a ⊗ₜ[ZMod p] 1) = a ⊗ₜ[ZMod p] 1
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl
    exact AlgebraicGeometry.specMap_comp_pullbackLift_eq_pullbackLift_comp_pullbackMap_of_comp_eq_comp O.g (resPt Pl ≫ Λ.σA) (ι v)
      (O.L.schemeNsmul p) (O.L.schemeNsmul_over p) (PDivisibleGroup.Hopf.nsmulAlgHom Rh (𝒢.level v) p : 𝒢.level v →+* 𝒢.level v)
      (ModularCurve.JHNeronObjectAtP.specMap_nsmulAlgHom_comp_eq_comp_schemeNsmul_of_forall_point_mul p M H hpM Pl hPl Λ O Rh 𝒢 ρh ι hS1 hS5 v p)
      _ _ hsq ((Algebra.TensorProduct.map (AlgHom.id (ResidueField ↥Pl) (ResidueField ↥Pl)) (PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v) p)).toRingHom) hea hec

end S_ModularCurve_JHNeronObjectAtP_mono_lift_and_exists_specMap_qc_comp_baseChange_comp_lift_eq_comp_pullbackFst_abqFibre_of_ordinaryIdempotent_of_bridge
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_mono_lift_and_exists_specMap_qc_comp_baseChange_comp_lift_eq_comp_pullbackFst_abqFibre_of_ordinaryIdempotent_of_bridge (solution)
