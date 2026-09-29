-- Prove2me | solution 1 for ModularCurve.XOneP.branchIdeal_ne_maximalIdeal_and_ringKrullDim_stalk_le_two_and_germ_ne_zero_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/2d59b754-5e73-5aa5-af3f-764f93825cca

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_ModularCurve_DRModelPackageCrossingFrame
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_ringKrullDim_stalk_le_ringKrullDim_add_one
import Theorems.Thm_ModularCurve_XOneP_germ_mem_maximalIdeal_and_ringKrullDim_stalk_le_one_of_isGenericPoint_component_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_exists_valuationSubring_ringEquiv_stalk_apply_germ_eq_of_ringKrullDim_le_one_twoChartIntegralModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_eq_of_forall_specializes_imp_eq_of_ringEquiv_stalk_of_fst_eq_twoChartModel_x1_mul
import Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_branchIdeal_ne_maximalIdeal_and_ringKrullDim_stalk_le_two_and_germ_ne_zero_twoChartModel_x1_mul
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul"
p2m_attr_erase "instance" "CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation"
p2m_attr_erase "instance" "ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single"
p2m_attr_erase "simp" "ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply"
p2m_attr_erase "simp" "TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.qExpandAlgHomC_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add"
p2m_attr_erase "simp" "KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

universe u

namespace R1V5CrossingSideFacts

open TopologicalSpace

theorem eq_of_branchIdeal_eq_maximalIdeal {X : Scheme.{u}} {ξ x : X} (h : ξ ⤳ x)
    (hP : Scheme.branchIdeal h = IsLocalRing.maximalIdeal _) : ξ = x := by
  obtain ⟨U, hU, hxU, -⟩ :=
    (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have hξU : ξ ∈ U := h.mem_open U.2 hxU
  letI algx : Algebra (X.presheaf.obj (Opposite.op U)) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  letI algξ : Algebra (X.presheaf.obj (Opposite.op U)) (X.presheaf.stalk ξ) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨ξ, hξU⟩
  haveI locx : IsLocalization.AtPrime (X.presheaf.stalk x) (hU'.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU'.isLocalization_stalk ⟨x, hxU⟩
  haveI locξ : IsLocalization.AtPrime (X.presheaf.stalk ξ) (hU'.primeIdealOf ⟨ξ, hξU⟩).asIdeal :=
    hU'.isLocalization_stalk ⟨ξ, hξU⟩

  have hspec : ∀ f : (X.presheaf.obj (Opposite.op U)), (X.presheaf.stalkSpecializes h) (algebraMap (X.presheaf.obj (Opposite.op U)) (X.presheaf.stalk x) f)
      = algebraMap (X.presheaf.obj (Opposite.op U)) (X.presheaf.stalk ξ) f := by
    intro f
    exact TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hxU h f
  suffices heq : hU'.primeIdealOf ⟨ξ, hξU⟩ = hU'.primeIdealOf ⟨x, hxU⟩ by
    have h1 := hU'.fromSpec_primeIdealOf ⟨ξ, hξU⟩
    have h2 := hU'.fromSpec_primeIdealOf ⟨x, hxU⟩
    rw [heq] at h1
    exact h1.symm.trans h2
  by_contra hne
  have hne' : (hU'.primeIdealOf ⟨ξ, hξU⟩).asIdeal ≠ (hU'.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    fun h' => hne (PrimeSpectrum.ext h')
  rcases not_and_or.mp (fun hh => hne' (le_antisymm hh.1 hh.2)) with h1 | h2
  ·
    obtain ⟨f, hfξ, hfx⟩ := SetLike.not_le_iff_exists.mp h1
    have hu : IsUnit (algebraMap (X.presheaf.obj (Opposite.op U)) (X.presheaf.stalk x) f) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x)
        (hU'.primeIdealOf ⟨x, hxU⟩).asIdeal f).mpr hfx
    have hm : algebraMap (X.presheaf.obj (Opposite.op U)) (X.presheaf.stalk ξ) f ∈ IsLocalRing.maximalIdeal _ :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk ξ)
        (hU'.primeIdealOf ⟨ξ, hξU⟩).asIdeal f).mpr hfξ
    rw [← hspec] at hm
    exact (IsLocalRing.mem_maximalIdeal _).mp hm (hu.map _)
  ·
    obtain ⟨f, hfx, hfξ⟩ := SetLike.not_le_iff_exists.mp h2
    have hm : algebraMap (X.presheaf.obj (Opposite.op U)) (X.presheaf.stalk x) f ∈ IsLocalRing.maximalIdeal _ :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x)
        (hU'.primeIdealOf ⟨x, hxU⟩).asIdeal f).mpr hfx
    rw [← hP, Scheme.mem_branchIdeal_iff, hspec] at hm
    exact hfξ ((IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk ξ)
      (hU'.primeIdealOf ⟨ξ, hξU⟩).asIdeal f).mp hm)

theorem germ_ne_zero_of_germ_appTop_ne_zero {X Y : Scheme.{u}} (f : Y ⟶ X) (y : Y) (s : Γ(X, ⊤))
    (h : Y.presheaf.germ ⊤ y trivial (f.appTop s) ≠ 0) :
    X.presheaf.germ ⊤ (f.base y) trivial s ≠ 0 := by
  intro h0
  apply h
  have := Scheme.Hom.germ_stalkMap_apply f ⊤ y trivial s
  rw [h0, map_zero] at this
  exact this.symm

theorem germ_ΓSpecIso_inv_ne_zero {B : Type u} [CommRing B] [IsDomain B] (y : ↥(Spec (CommRingCat.of B)))
    (b : B) (hb : b ≠ 0) :
    (Spec (CommRingCat.of B)).presheaf.germ ⊤ y trivial ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) ≠ 0 := by
  intro h0
  have hinj := germ_injective_of_isIntegral (X := Spec (CommRingCat.of B)) (U := ⊤) y trivial
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of B)).inv b = 0 := hinj (by rw [h0, map_zero])
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of B)).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) = b := by
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  rw [h1, map_zero] at h2
  exact hb h2.symm

theorem ringKrullDim_le_two_and_germ_ne_zero
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)]
    (ϖA : A) (hϖA : IsLocalRing.maximalIdeal A = Ideal.span {ϖA})
    (x : ↥(ModularCurve.TwoChartModel A (↥K) j)) :

    ringKrullDim ((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk x) ≤ 2 ∧
    (ModularCurve.TwoChartModel A (↥K) j).presheaf.germ ⊤ x trivial ((ModularCurve.TwoChart.modelTo A (↥K) j).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ϖA)) ≠ 0 := by
  constructor
  · have hA : ringKrullDim A ≤ 1 := Ring.krullDimLE_iff.mp inferInstance
    calc ringKrullDim ((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk x)
        ≤ ringKrullDim A + 1 :=
          AlgebraicCurve.TwoChartIntegralModel.ringKrullDim_stalk_le_ringKrullDim_add_one A (↥K) j x
      _ ≤ 1 + 1 := add_le_add hA le_rfl
      _ = 2 := one_add_one_eq_two
  ·
    have hϖ0 : ϖA ≠ 0 := by
      intro h0
      apply IsDiscreteValuationRing.not_a_field A
      rw [hϖA, h0, Ideal.span_singleton_eq_bot]
    have hϖK : algebraMap A (↥K) ϖA ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply A L (↥K)]
      exact (map_ne_zero_iff _ (algebraMap L (↥K)).injective).mpr
        ((map_ne_zero_iff _ (IsFractionRing.injective A L)).mpr hϖ0)

    have key : ∀ (S : Subalgebra A (↥K)) (ι : Spec (CommRingCat.of ↥S) ⟶ ModularCurve.TwoChartModel A (↥K) j)
        (hι : ι ≫ ModularCurve.TwoChart.modelTo A (↥K) j = Spec.map (CommRingCat.ofHom (algebraMap A ↥S)))
        (y : ↥(Spec (CommRingCat.of ↥S))), ι.base y = x →
        (ModularCurve.TwoChartModel A (↥K) j).presheaf.germ ⊤ x trivial
          ((ModularCurve.TwoChart.modelTo A (↥K) j).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ϖA)) ≠ 0 := by
      intro S ι hι y hy
      subst hy
      apply germ_ne_zero_of_germ_appTop_ne_zero
      have hcomp : ι.appTop ((ModularCurve.TwoChart.modelTo A (↥K) j).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ϖA)) =
          (Scheme.ΓSpecIso (CommRingCat.of ↥S)).inv (algebraMap A (↥S) ϖA) := by
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hι, ← CommRingCat.comp_apply,
          ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
        rfl
      rw [hcomp]
      refine germ_ΓSpecIso_inv_ne_zero y _ ?_
      intro h0
      apply hϖK
      have : ((algebraMap A (↥S) ϖA : ↥S) : ↥K) = ((0 : ↥S) : ↥K) := congrArg (fun s : ↥S => (s : ↥K)) h0
      rwa [Subalgebra.coe_algebraMap, Subalgebra.coe_zero] at this
    rcases ModularCurve.TwoChart.mem_range_ιFin_or_mem_range_ιInf A (↥K) j x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact key _ (ModularCurve.TwoChart.ιFin A (↥K) j) (ModularCurve.TwoChart.ιFin_modelTo A (↥K) j) y hy
    · exact key _ (ModularCurve.TwoChart.ιInf A (↥K) j) (ModularCurve.TwoChart.ιInf_modelTo A (↥K) j) y hy

theorem genericPoint_notMem_range {C₁ C₂ Y : Scheme.{u}} (i₁ : C₁ ⟶ Y) (i₂ : C₂ ⟶ Y)
    [IsClosedImmersion i₂] [IsIntegral C₁] (hinf : (Set.univ : Set C₁).Infinite)
    (hfin : Finite ↥(pullback i₁ i₂)) :
    i₁.base (genericPoint C₁) ∉ Set.range i₂.base := by
  rintro ⟨s, hs⟩
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i₁) (g := i₂) (genericPoint C₁) s hs.symm
  have hcl : IsClosed (Set.range (pullback.fst i₁ i₂).base) :=
    (pullback.fst i₁ i₂).isClosedEmbedding.isClosed_range
  have huniv : Set.univ ⊆ Set.range (pullback.fst i₁ i₂).base :=
    ((genericPoint_spec C₁).mem_closed_set_iff hcl).mp ⟨z, hz⟩
  exact hinf ((Set.finite_range _).subset huniv)

theorem eq_of_specializes_genericPoint {C₁ C₂ Y : Scheme.{u}} (i₁ : C₁ ⟶ Y) (i₂ : C₂ ⟶ Y)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsIntegral C₁]
    (hcover : ∀ z : Y, z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base)
    (hnot : i₁.base (genericPoint C₁) ∉ Set.range i₂.base) :
    ∀ t : Y, t ⤳ i₁.base (genericPoint C₁) → t = i₁.base (genericPoint C₁) := by
  intro t ht
  rcases hcover t with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · have hs : s ⤳ genericPoint C₁ := (i₁.isClosedEmbedding.isInducing.specializes_iff).mp ht
    have : s = genericPoint C₁ :=
      (hs.antisymm ((genericPoint_spec C₁).specializes (Set.mem_univ s))).eq
    rw [this]
  · exact absurd (ht.mem_closed i₂.isClosedEmbedding.isClosed_range ⟨s, rfl⟩) hnot

theorem component_package
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C : Scheme.{0}) (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (i : SchemeHomOver c (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) [IsClosedImmersion i.1]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) [IsIntegral C]
    (z : ↥(ModularCurve.TwoChartModel A (↥K) j))
    (hz : z = (i.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (genericPoint C)) :
    (ModularCurve.TwoChartModel A (↥K) j).presheaf.germ ⊤ z trivial
        ((ModularCurve.TwoChart.modelTo A (↥K) j).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ϖ)) ∈
      IsLocalRing.maximalIdeal ((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk z) ∧
    Ring.KrullDimLE 1 ((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk z) ∧
    IsDomain ((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk z) ∧
    ∃ (V : ValuationSubring ↥K) (e : ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+* ↥V)
      (hzFin : z ∈ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)),
      (∀ a : A, algebraMap A ↥K a ∈ V) ∧
      (∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits) ∧
      (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) ∧
      (∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
        ((e (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) z hzFin).hom
            (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))) : ↥V) : ↥K) = (a : ↥K)) := by
  subst hz
  obtain ⟨hmem, hdim⟩ :=
    ModularCurve.XOneP.germ_mem_maximalIdeal_and_ringKrullDim_stalk_le_one_of_isGenericPoint_component_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj k C c i ϖ hϖ (genericPoint C) (genericPoint_spec C)
  obtain ⟨V, e, hzFin, h1, h2, h3, -, -, hpin⟩ :=
    ModularCurve.XOneP.exists_valuationSubring_ringEquiv_stalk_apply_germ_eq_of_ringKrullDim_le_one_twoChartIntegralModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj ϖ hϖ _ _ rfl hmem hdim
  exact ⟨hmem, Ring.krullDimLE_iff.mpr hdim, Function.Injective.isDomain e.toRingHom e.injective,
    V, e, hzFin, h1, h2, h3, hpin⟩

theorem fst_genericPoint_ne
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)),
      z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) [IsIntegral C₁] [IsIntegral C₂] :
    (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (i₁.1.base (genericPoint C₁)) ≠
      (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (i₂.1.base (genericPoint C₂)) := by
  intro heq
  have hfin : Finite ↥(pullback i₁.1 i₂.1) := Nat.finite_of_card_ne_zero (by omega)
  have hfin' : Finite ↥(pullback i₂.1 i₁.1) :=
    Finite.of_equiv _ (Scheme.homeoOfIso (pullbackSymmetry i₁.1 i₂.1)).toEquiv
  have hinf₁ : (Set.univ : Set ↥C₁).Infinite :=
    (AlgebraicCurve.infinite_setOf_isClosed_singleton c₁).mono (Set.subset_univ _)
  have hinf₂ : (Set.univ : Set ↥C₂).Infinite :=
    (AlgebraicCurve.infinite_setOf_isClosed_singleton c₂).mono (Set.subset_univ _)
  have hnot₁ := genericPoint_notMem_range i₁.1 i₂.1 hinf₁ hfin
  have hnot₂ := genericPoint_notMem_range i₂.1 i₁.1 hinf₂ hfin'
  have hmax₁ := eq_of_specializes_genericPoint i₁.1 i₂.1 hcover hnot₁
  have hmax₂ := eq_of_specializes_genericPoint i₂.1 i₁.1 (fun z => (hcover z).symm) hnot₂
  obtain ⟨-, -, -, V, e, hzFin, hV₁, hV₂, hV₃, hpin⟩ :=
    component_package p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ c₁ i₁ ϖ hϖ
      ((pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (i₁.1.base (genericPoint C₁))) rfl
  have key :=
    ModularCurve.XOneP.eq_of_forall_specializes_imp_eq_of_ringEquiv_stalk_of_fst_eq_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj k (i₁.1.base (genericPoint C₁)) (i₂.1.base (genericPoint C₂))
      hmax₁ hmax₂ V hV₁ hV₂ hV₃ hzFin e hpin heq
  exact hnot₁ ⟨genericPoint C₂, key.symm⟩

theorem main
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)),
      z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)
    (ϖA : A) (hϖA : IsLocalRing.maximalIdeal A = Ideal.span {ϖA})
    [IsIntegral C₁] [IsIntegral C₂] (x : ↥(ModularCurve.TwoChartModel A (↥K) j))
    (h₁ : (i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (genericPoint C₁) ⤳ x)
    (h₂ : (i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (genericPoint C₂) ⤳ x) :
    Scheme.branchIdeal h₁ ≠ IsLocalRing.maximalIdeal _ ∧ Scheme.branchIdeal h₂ ≠ IsLocalRing.maximalIdeal _ ∧
    ringKrullDim ((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk x) ≤ 2 ∧
    (ModularCurve.TwoChartModel A (↥K) j).presheaf.germ ⊤ x trivial
      ((ModularCurve.TwoChart.modelTo A (↥K) j).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ϖA)) ≠ 0 := by
  obtain ⟨h3, h4⟩ := ringKrullDim_le_two_and_germ_ne_zero p M L K A j ϖA hϖA x

  have hϖP₁ : (ModularCurve.TwoChartModel A (↥K) j).presheaf.germ ⊤ x trivial
      ((ModularCurve.TwoChart.modelTo A (↥K) j).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ϖA)) ∈
      Scheme.branchIdeal h₁ := by
    rw [Scheme.mem_branchIdeal_iff]
    erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
    exact (component_package p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ c₁ i₁ ϖA hϖA _ rfl).1
  have hϖP₂ : (ModularCurve.TwoChartModel A (↥K) j).presheaf.germ ⊤ x trivial
      ((ModularCurve.TwoChart.modelTo A (↥K) j).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ϖA)) ∈
      Scheme.branchIdeal h₂ := by
    rw [Scheme.mem_branchIdeal_iff]
    erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
    exact (component_package p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₂ c₂ i₂ ϖA hϖA _ rfl).1
  have hP₁0 : Scheme.branchIdeal h₁ ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hϖP₁
    exact h4 hϖP₁
  have hP₂0 : Scheme.branchIdeal h₂ ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hϖP₂
    exact h4 hϖP₂
  have hne := fst_genericPoint_ne p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover n hn hn0 ϖA hϖA
  refine ⟨?_, ?_, h3, h4⟩
  · intro hP
    have hx₁ := eq_of_branchIdeal_eq_maximalIdeal h₁ hP
    obtain ⟨-, hdim, hdom, -⟩ :=
      component_package p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ c₁ i₁ ϖA hϖA x hx₁.symm
    have hP' : Scheme.branchIdeal h₂ = IsLocalRing.maximalIdeal _ :=
      IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal_of_ne_bot inferInstance hP₂0)
    have hx₂ := eq_of_branchIdeal_eq_maximalIdeal h₂ hP'
    exact hne (hx₁.trans hx₂.symm)
  · intro hP
    have hx₂ := eq_of_branchIdeal_eq_maximalIdeal h₂ hP
    obtain ⟨-, hdim, hdom, -⟩ :=
      component_package p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₂ c₂ i₂ ϖA hϖA x hx₂.symm
    have hP' : Scheme.branchIdeal h₁ = IsLocalRing.maximalIdeal _ :=
      IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal_of_ne_bot inferInstance hP₁0)
    have hx₁ := eq_of_branchIdeal_eq_maximalIdeal h₁ hP'
    exact hne (hx₁.trans hx₂.symm)

end R1V5CrossingSideFacts

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)
    (ϖA : A) (hϖA : IsLocalRing.maximalIdeal A = Ideal.span {ϖA})
    [IsIntegral C₁] [IsIntegral C₂] (ν : ↥(pullback i₁.1 i₂.1))
    (h₁ : (i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (genericPoint C₁) ⤳ (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ν)
    (h₂ : (i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (genericPoint C₂) ⤳ (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ν) :
    Scheme.branchIdeal h₁ ≠ IsLocalRing.maximalIdeal _ ∧ Scheme.branchIdeal h₂ ≠ IsLocalRing.maximalIdeal _ ∧
    ringKrullDim ((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk ((pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ν)) ≤ 2 ∧
    (ModularCurve.TwoChartModel A (↥K) j).presheaf.germ ⊤ ((pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ν) trivial ((ModularCurve.TwoChart.modelTo A (↥K) j).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ϖA)) ≠ 0 :=
  R1V5CrossingSideFacts.main p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover n hn hn0 ϖA hϖA _ h₁ h₂

end S_ModularCurve_XOneP_branchIdeal_ne_maximalIdeal_and_ringKrullDim_stalk_le_two_and_germ_ne_zero_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_branchIdeal_ne_maximalIdeal_and_ringKrullDim_stalk_le_two_and_germ_ne_zero_twoChartModel_x1_mul (solution)
