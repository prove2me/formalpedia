-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_twoSidedPool_smoothLocus_closedPrime_two_of_atkinLehner_generic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ce7cb53e-6f55-5474-a20b-faffd6aab31f

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_chartAlgFin_forall_mem_range_comp_zero_and_not_mem_range_comp_one
import Theorems.Thm_ModularCurve_XHDRLevel_exists_ratAlgEquiv_chartAlgFin_algEquiv_of_atkinLehner_generic
import Theorems.Thm_ModularCurve_XHDRLevel_exists_ogg_unit_pair_chartAlgFin_gammaH
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_chartAlgFin_algEquiv_iotaFin_comp_w_eq_of_atkinLehner_generic_of_unitsMap
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_levelPolynomials_of_chartAlgFin
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_oneSidedPool_baseChange_of_levelPolynomials
import Theorems.Thm_ModularCurve_XHDRModelAtP_w_preimage_smoothLocus_eq_and_isSeparated_toBase
import Theorems.Thm_ModularCurve_XHDRModelAtP_fibre_w_mem_diff_connectedComponentIn_and_cuspZero_mem_baseChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoSidedPool_of_oneSided_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_twoSidedPool_smoothLocus_closedPrime_two_of_atkinLehner_generic
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01"
p2m_attr_erase "simp" "CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_jqNGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none PeriodPair.weierstrassCurve_a₆"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero"
p2m_attr_erase "simp" "TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve~coeffEmb_qExpand~coeffEmb_injective~DRModelPackageLevel ModularCurve.XHDRLevel"

open scoped MatrixGroups

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

namespace ClosedHReduce

p2m_open "ModularCurve~coeffEmb_qExpand~coeffEmb_injective~DRModelPackageLevel ModularCurve.XHDRLevel"

section coeff

variable (L : Type) [Field L] [Algebra ℚ L]

theorem coeffEmb_injective : Function.Injective (coeffEmb L) := by
  intro x y h
  ext k
  apply (algebraMap ℚ L).injective
  rw [← coeffEmb_coeff, ← coeffEmb_coeff, h]

theorem coeffEmb_qExpand (p : ℕ) [NeZero p] (x : LaurentSeries ℚ) :
    coeffEmb L (qExpand ℚ p x) = qExpand L p (coeffEmb L x) := by
  ext k
  by_cases hk : (p : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd p _ hk, qExpand_coeff_of_not_dvd p _ hk, map_zero]

end coeff

variable (p M : ℕ) [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

theorem sigma_law
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
          ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (σ : ↥(qExpFunctionFieldC ℚ (ΓM M H)) ≃ₐ[ℚ] ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    (ha : ∀ f : ↥(qExpFunctionFieldC ℚ (ΓM M H)),
        ((θ ⟨coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) f.2⟩ :
          ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) (((σ f : ↥(qExpFunctionFieldC ℚ (ΓM M H)))) : LaurentSeries ℚ)) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∀ (f : ↥(qExpFunctionFieldC ℚ (ΓM M H))) (u : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))), (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) →
      ((σ f : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = qExpand ℚ p (u : LaurentSeries ℚ) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro f u hfu
  apply coeffEmb_injective (AlgebraicClosure ℚ)
  rw [← ha f, coeffEmb_qExpand]
  exact hθ _ ⟨coeffEmb (AlgebraicClosure ℚ) (u : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) u.2⟩
    (by simp only [hfu])

theorem coe_theta_eq_sigma
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (σ : ↥(qExpFunctionFieldC ℚ (ΓM M H)) ≃ₐ[ℚ] ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    (ha : ∀ f : ↥(qExpFunctionFieldC ℚ (ΓM M H)),
        ((θ ⟨coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) f.2⟩ :
          ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) (((σ f : ↥(qExpFunctionFieldC ℚ (ΓM M H)))) : LaurentSeries ℚ))
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (hread : ∀ (b : ↥(chartAlgFin p (ΓM M H) hj)) (f : ↥(xHFunctionFieldBar M H)),
        (f : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) (((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) (((theta b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ))
    (b : ↥(chartAlgFin p (ΓM M H) hj)) :
    ((theta b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) = σ ((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) := by
  apply Subtype.ext
  apply coeffEmb_injective (AlgebraicClosure ℚ)
  exact (hread b ⟨_, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
    ((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩ rfl).symm.trans (ha _)

theorem theta_mul_eq_pow_twelve
    (σ : ↥(qExpFunctionFieldC ℚ (ΓM M H)) ≃ₐ[ℚ] ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (hθσ : ∀ b : ↥(chartAlgFin p (ΓM M H) hj),
      ((theta b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) = σ ((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))))
    (v₁ w₁ : ↥(chartAlgFin p (ΓM M H) hj))
    (hv₁ : (((v₁ : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = modularUnitSeries p)
    (hw₁ : (((w₁ : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = (p : LaurentSeries ℚ) ^ 12 * (modularUnitSeries p)⁻¹)
    (hvw : v₁ * w₁ = algebraMap (R p) ↥(chartAlgFin p (ΓM M H) hj) (((p : ℕ) : R p) ^ 12))
    (hσv : σ ((v₁ : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) = ((w₁ : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))))
    (v : ↥(chartAlgFin p (ΓM M H) hj))
    (hv : ((v : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = modularUnitSeries p ∨
      ((v : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = (p : LaurentSeries ℚ) ^ 12 * (modularUnitSeries p)⁻¹) :
    v * theta v = (p : ↥(chartAlgFin p (ΓM M H) hj)) ^ 12 := by
  classical

  have hinj : ∀ a b : ↥(chartAlgFin p (ΓM M H) hj),
      (((a : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
        (((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) → a = b :=
    fun a b h => Subtype.ext (Subtype.ext h)
  have hp12 : algebraMap (R p) ↥(chartAlgFin p (ΓM M H) hj) (((p : ℕ) : R p) ^ 12) = (p : ↥(chartAlgFin p (ΓM M H) hj)) ^ 12 := by
    rw [map_pow, map_natCast]
  have hvw' : v₁ * w₁ = (p : ↥(chartAlgFin p (ΓM M H) hj)) ^ 12 := hvw.trans hp12
  have hq0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hqLS : (p : LaurentSeries ℚ) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ (LaurentSeries ℚ))]
    exact (map_ne_zero_iff _ (algebraMap ℚ (LaurentSeries ℚ)).injective).2 hq0
  have hu0 : modularUnitSeries p ≠ 0 := modularUnitSeries_ne_zero p

  have hθv₁ : theta v₁ = w₁ := Subtype.ext ((hθσ v₁).trans hσv)

  have hw0 : ((w₁ : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ≠ 0 := by
    intro h
    have h' : (((w₁ : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = 0 := by rw [h]; rfl
    rw [hw₁] at h'
    exact mul_ne_zero (pow_ne_zero _ hqLS) (inv_ne_zero hu0) h'
  have hprodF : ((v₁ : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) * ((w₁ : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) =
      (p : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ^ 12 := by
    rw [← Subalgebra.coe_mul, hvw']
    simp
  have hσw : σ ((w₁ : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) = ((v₁ : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) := by
    have e := congrArg σ hprodF
    rw [map_mul, hσv, map_pow, map_natCast, ← hprodF, mul_comm ((v₁ : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H)))] at e
    exact mul_left_cancel₀ hw0 e
  have hθw₁ : theta w₁ = v₁ := Subtype.ext ((hθσ w₁).trans hσw)
  rcases hv with h | h
  · have hv' : v = v₁ := hinj _ _ (h.trans hv₁.symm)
    rw [hv', hθv₁, hvw']
  · have hv' : v = w₁ := hinj _ _ (h.trans hw₁.symm)
    rw [hv', hθw₁, mul_comm, hvw']

end ClosedHReduce

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
          ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
        𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (𝔭 : PrimeSpectrum (R p)) (h𝔭 : 𝔭.asIdeal ≠ ⊥) (hp2 : p = 2) (A₀ B₀ n₀ : ℕ) :
    ∃ (f : R p) (_ : f ∉ 𝔭.asIdeal) (b N₁ N₂ : ℕ)
      (_ : A₀ * b ^ n₀ + B₀ < N₁) (_ : A₀ * b ^ n₀ + B₀ < N₂)
      (R' : Type) (_ : CommRing R') (_ : Algebra (R p) R')
      (_ : Algebra (Localization.Away f) R') (_ : IsScalarTower (R p) (Localization.Away f) R')
      (_ : Module.Finite (Localization.Away f) R') (_ : Algebra.Etale (Localization.Away f) R')
      (_ : Module.FaithfullyFlat (Localization.Away f) R')
      (B : Fin N₁ → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra (Localization.Away f) (B i))
      (_ : ∀ i, Module.Finite (Localization.Away f) (B i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B i))
      (deg : Fin N₁ → ℕ) (_ : ∀ i, 1 ≤ deg i) (_ : ∀ i, deg i ≤ b)
      (φ : ∀ i, TensorProduct (Localization.Away f) R' (B i) ≃ₐ[R'] (Fin (deg i) → R'))
      (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f)))
      (_ : ∀ i, IsClosedImmersion (z i))
      (B' : Fin N₂ → Type) (_ : ∀ i, CommRing (B' i)) (_ : ∀ i, Algebra (Localization.Away f) (B' i))
      (_ : ∀ i, Module.Finite (Localization.Away f) (B' i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B' i))
      (deg' : Fin N₂ → ℕ) (_ : ∀ i, 1 ≤ deg' i) (_ : ∀ i, deg' i ≤ b)
      (φ' : ∀ i, TensorProduct (Localization.Away f) R' (B' i) ≃ₐ[R'] (Fin (deg' i) → R'))
      (z' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f)))
      (_ : ∀ i, IsClosedImmersion (z' i)),

      (∀ i, z i ≫ baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f) = specMap (Localization.Away f) (B i)) ∧
      (∀ i, Set.range (z i).base ⊆
        ((pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f)) ⁻¹ᵁ 𝔛.smoothLocus : (pullback (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))).Opens) :
          Set ↥(pullback (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))))) ∧
      (Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base)) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
        (i : Fin N₁),
        (pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s).base ⁻¹' Set.range (z i).base ⊆
          connectedComponentIn
            (((pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
                (pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k))) ∧

      (∃ j, deg' j ≤ 1) ∧
      (∀ i, z' i ≫ baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f) = specMap (Localization.Away f) (B' i)) ∧
      (∀ i, Set.range (z' i).base ⊆
        ((pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f)) ⁻¹ᵁ 𝔛.smoothLocus : (pullback (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))).Opens) :
          Set ↥(pullback (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))))) ∧
      (Pairwise fun i j => Disjoint (Set.range (z' i).base) (Set.range (z' j).base)) ∧
      (∀ i j, Disjoint (Set.range (z i).base) (Set.range (z' j).base)) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
        (i : Fin N₂), ¬ Smooth (pullback.snd (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s) →
        (pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s).base ⁻¹' Set.range (z' i).base ⊆
          (((pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
                (pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s)) \
          connectedComponentIn
            (((pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
                (pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k))) := by
  classical
  obtain ⟨v, hv, hdict⟩ :=
    ModularCurve.XHDRModelAtP.exists_chartAlgFin_forall_mem_range_comp_zero_and_not_mem_range_comp_one p M H hpM hpM2 hHp hj 𝔛
  obtain ⟨σ, thetaF, ha, -, -⟩ :=
    ModularCurve.XHDRLevel.exists_ratAlgEquiv_chartAlgFin_algEquiv_of_atkinLehner_generic p M H hpM hpM2 hHp hj θ hθ
  have hσ := ClosedHReduce.sigma_law p M H hpM θ hθ σ ha
  obtain ⟨v₁, w₁, hv₁, hw₁, hvw, hσv⟩ :=
    ModularCurve.XHDRLevel.exists_ogg_unit_pair_chartAlgFin_gammaH p M H hpM hpM2 hHp hj σ hσ
  obtain ⟨theta, hwchart, hwfin, hread⟩ :=
    ModularCurve.XHDRModelAtP.exists_chartAlgFin_algEquiv_iotaFin_comp_w_eq_of_atkinLehner_generic_of_unitsMap p M H hpM hpM2 hHp hj 𝔛
      θ hθ hwgen
  have hθσ := ClosedHReduce.coe_theta_eq_sigma p M H hj θ σ ha theta hread
  have hvθ : v * theta v = (p : ↥(chartAlgFin p (ΓM M H) hj)) ^ 12 :=
    ClosedHReduce.theta_mul_eq_pow_twelve p M H hj σ theta hθσ v₁ w₁ hv₁ hw₁ hvw hσv v hv
  obtain ⟨b, N₁, hN₁, g, rk, hmonic, hlev, hrk1, hrkb, hcop, hcopw, hcopv⟩ :=
    ModularCurve.XHDRModelAtP.exists_levelPolynomials_of_chartAlgFin p M H hpM hpM2 hHp hj 𝔛 v hv (theta v) hvθ A₀ B₀ n₀
  obtain ⟨R', _, _, _, _, _, _, _, B, _, _, _, _, deg, hdeg, hdegb, φ, z, _, hz₁, hz₂, hz₃, hz₄, hzinf, hzzero, hzw⟩ :=
    ModularCurve.XHDRModelAtP.exists_oneSidedPool_baseChange_of_levelPolynomials p M H hpM hpM2 hHp hj 𝔛 theta hwchart hwfin
      (1 : R p) v hdict b N₁ g rk hmonic
      (fun i => (hlev i).1) (fun i => (hlev i).2.1) (fun i => (hlev i).2.2.1) (fun i => (hlev i).2.2.2) hrk1 hrkb
      hcop hcopw hcopv
  obtain ⟨hwU, hsep⟩ := ModularCurve.XHDRModelAtP.w_preimage_smoothLocus_eq_and_isSeparated_toBase p M H hpM hj 𝔛
  haveI := hsep
  exact ⟨1, fun h => 𝔭.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h),
    AlgebraicGeometry.RelPicard.exists_twoSidedPool_of_oneSided_of_iso (R p) (toBase p (ΓM M H) hj) 𝔛.smoothLocus 𝔛.εinf 𝔛.εzero
      𝔛.w 𝔛.w_over 𝔛.w_sections hwU 𝔛.εzero_mem_smoothLocus A₀ B₀ n₀ 1
      (fun k _ _ s hns =>
        ModularCurve.XHDRModelAtP.fibre_w_mem_diff_connectedComponentIn_and_cuspZero_mem_baseChange p M H hpM hpM2 hj 𝔛 1 k s hns)
      b N₁ hN₁ R' B deg hdeg hdegb φ z hz₁ hz₂ hz₃ hz₄ hzinf hzzero hzw⟩

end S_ModularCurve_XHDRModelAtP_exists_twoSidedPool_smoothLocus_closedPrime_two_of_atkinLehner_generic
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_twoSidedPool_smoothLocus_closedPrime_two_of_atkinLehner_generic (solution)
