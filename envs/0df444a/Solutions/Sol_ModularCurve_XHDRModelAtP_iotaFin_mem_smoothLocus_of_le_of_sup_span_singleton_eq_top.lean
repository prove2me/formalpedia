-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/35a6d757-6af0-53b3-8e84-f8dab15aee9e

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
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_GaloisRep_ratLocalizedAt_isLocalRing
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_ModularCurve_XHDRModelAtP_mem_preimage_smoothLocus_iff_not_mem_range_comp_inter
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one"
p2m_attr_erase "simp" "ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun"
p2m_attr_erase "simp" "KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.XHDRLevel"

p2m_open_scoped "MatrixGroups Polynomial AlgebraicGeometry.Polynomial"

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace GeomSmoothH

open IsLocalRing

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

theorem natCast_mem_of_isMaximal (I : Ideal ↥(chartAlgFin p (ΓM M H) hj))
    [Module.Finite (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ I)]
    (Mx : Ideal ↥(chartAlgFin p (ΓM M H) hj)) [hM : Mx.IsMaximal] (hIM : I ≤ Mx) :
    (p : ↥(chartAlgFin p (ΓM M H) hj)) ∈ Mx := by
  haveI : Algebra.IsIntegral (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ I) := Algebra.IsIntegral.of_finite _ _
  haveI := GaloisRep.ratLocalizedAt.isLocalRing (p := p) Fact.out
  have hcomap : Ideal.comap (Ideal.Quotient.mk I) (Mx.map (Ideal.Quotient.mk I)) = Mx := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.2 hIM]
  have hne : Mx.map (Ideal.Quotient.mk I) ≠ ⊤ := fun h => hM.ne_top (by rw [← hcomap, h, Ideal.comap_top])
  haveI : (Mx.map (Ideal.Quotient.mk I)).IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective hM).resolve_left hne
  have hP := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R p) (Mx.map (Ideal.Quotient.mk I))
  have hPeq : Ideal.comap (algebraMap (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ I)) (Mx.map (Ideal.Quotient.mk I)) =
      Ideal.span {(p : R p)} := by
    rw [IsLocalRing.eq_maximalIdeal hP, GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p Fact.out]
  have hq : algebraMap (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ I) p ∈ Mx.map (Ideal.Quotient.mk I) := by
    rw [← Ideal.mem_comap, hPeq]; exact Ideal.mem_span_singleton_self _
  rw [← hcomap, Ideal.mem_comap, map_natCast]
  rwa [map_natCast] at hq

theorem ringHom_ext_charP {k : Type} [Field k] [CharP k p] (f g : R p →+* k) : f = g := by
  apply RingHom.ext
  intro x
  have hx : (x : ℚ).den.Coprime p := x.2
  have hden : (((x : ℚ).den : ℕ) : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k p]
    intro h
    have := Nat.Coprime.eq_one_of_dvd (hx.symm) |> fun e => e h
    exact (Fact.out : p.Prime).one_lt.ne' this

  have hnum : (((x : ℚ).num : ℚ)).den.Coprime p := by simp
  have hden' : ((((x : ℚ).den : ℕ) : ℚ)).den.Coprime p := by simp
  have hmul : x * ⟨(((x : ℚ).den : ℕ) : ℚ), hden'⟩ = ⟨((x : ℚ).num : ℚ), hnum⟩ := by
    apply Subtype.ext
    show (x : ℚ) * ((x : ℚ).den : ℚ) = ((x : ℚ).num : ℚ)
    exact Rat.mul_den_eq_num (x : ℚ)
  have hf := congrArg f hmul
  have hg := congrArg g hmul
  rw [map_mul] at hf hg
  have hfd : f ⟨(((x : ℚ).den : ℕ) : ℚ), hden'⟩ = ((x : ℚ).den : k) := by
    rw [show (⟨(((x : ℚ).den : ℕ) : ℚ), hden'⟩ : R p) = (((x : ℚ).den : ℕ) : R p) from Subtype.ext (by simp), map_natCast]
  have hgd : g ⟨(((x : ℚ).den : ℕ) : ℚ), hden'⟩ = ((x : ℚ).den : k) := by
    rw [show (⟨(((x : ℚ).den : ℕ) : ℚ), hden'⟩ : R p) = (((x : ℚ).den : ℕ) : R p) from Subtype.ext (by simp), map_natCast]
  have hfn : f ⟨((x : ℚ).num : ℚ), hnum⟩ = ((x : ℚ).num : k) := by
    rw [show (⟨((x : ℚ).num : ℚ), hnum⟩ : R p) = (((x : ℚ).num : ℤ) : R p) from Subtype.ext (by simp), map_intCast]
  have hgn : g ⟨((x : ℚ).num : ℚ), hnum⟩ = ((x : ℚ).num : k) := by
    rw [show (⟨((x : ℚ).num : ℚ), hnum⟩ : R p) = (((x : ℚ).num : ℤ) : R p) from Subtype.ext (by simp), map_intCast]
  rw [hfd, hfn] at hf
  rw [hgd, hgn] at hg
  exact mul_right_cancel₀ hden (hf.trans hg.symm)

theorem exists_ringHom_quotient (I : Ideal ↥(chartAlgFin p (ΓM M H) hj))
    [Module.Finite (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ I)]
    (𝔮 : Ideal ↥(chartAlgFin p (ΓM M H) hj)) [h𝔮 : 𝔮.IsMaximal] (hI𝔮 : I ≤ 𝔮)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] :
    ∃ φ : (↥(chartAlgFin p (ΓM M H) hj) ⧸ 𝔮) →+* κ, True := by
  classical
  letI : Field (↥(chartAlgFin p (ΓM M H) hj) ⧸ 𝔮) := Ideal.Quotient.field 𝔮
  have hp𝔮 : (p : ↥(chartAlgFin p (ΓM M H) hj)) ∈ 𝔮 := natCast_mem_of_isMaximal p M H hj I 𝔮 hI𝔮
  haveI : CharP (↥(chartAlgFin p (ΓM M H) hj) ⧸ 𝔮) p := by
    rw [CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)]
    rw [← map_natCast (Ideal.Quotient.mk 𝔮), Ideal.Quotient.eq_zero_iff_mem]
    exact hp𝔮
  letI := ZMod.algebra (↥(chartAlgFin p (ΓM M H) hj) ⧸ 𝔮) p
  letI := ZMod.algebra κ p

  haveI : Module.Finite (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ 𝔮) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ (R p) hI𝔮).toLinearMap (Ideal.Quotient.factor_surjective hI𝔮)
  haveI : Algebra.IsIntegral (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ 𝔮) := Algebra.IsIntegral.of_finite _ _
  have hcomp : (algebraMap (ZMod p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ 𝔮)).comp (GaloisRep.ratLocalizedAtResidue p) =
      algebraMap (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ 𝔮) := ringHom_ext_charP p _ _
  haveI : Algebra.IsAlgebraic (ZMod p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ 𝔮) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨P, hPm, hPx⟩ := Algebra.IsIntegral.isIntegral (R := R p) x
    refine ⟨P.map (GaloisRep.ratLocalizedAtResidue p), (hPm.map _).ne_zero, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
    exact hPx
  exact ⟨(IsAlgClosed.lift (R := ZMod p) (S := ↥(chartAlgFin p (ΓM M H) hj) ⧸ 𝔮) (M := κ) :
    (↥(chartAlgFin p (ΓM M H) hj) ⧸ 𝔮) →ₐ[ZMod p] κ).toRingHom, trivial⟩

end GeomSmoothH

namespace GeomSmoothH

open IsLocalRing

section ValRing

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)

include hA in
theorem natCast_mem_maximalIdeal : ((p : ℕ) : ↥A) ∈ maximalIdeal ↥A := by
  rw [← ValuationSubring.coe_mem_nonunits_iff]; exact hA

include hA in

theorem charP_residueField : CharP (ResidueField ↥A) p := by
  refine (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr ?_
  rw [← map_natCast (residue ↥A), residue_eq_zero_iff]
  exact natCast_mem_maximalIdeal p A hA

include hA in

theorem isUnit_natCast_of_coprime {n : ℕ} (hn : n.Coprime p) : IsUnit ((n : ℕ) : ↥A) := by
  by_contra hnu
  have hmem : ((n : ℕ) : ↥A) ∈ maximalIdeal ↥A := (mem_maximalIdeal _).mpr hnu
  have hp := natCast_mem_maximalIdeal p A hA
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * (n : ℤ) + b * (p : ℤ) = 1 := by
    refine ⟨Int.gcdA n p, Int.gcdB n p, ?_⟩
    have := Int.gcd_eq_gcd_ab (n : ℤ) (p : ℤ)
    rw [Int.gcd_natCast_natCast, hn] at this
    push_cast at this
    linarith
  have h1 : (1 : ↥A) ∈ maximalIdeal ↥A := by
    have : (a : ↥A) * (n : ℕ) + (b : ↥A) * (p : ℕ) = 1 := by exact_mod_cast congrArg (fun z : ℤ => (z : ↥A)) hab
    rw [← this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hp)
  exact (maximalIdeal.isMaximal ↥A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

include hA in

theorem mem_of_liesOverPrime (x : R p) : algebraMap ℚ (AlgebraicClosure ℚ) (x : ℚ) ∈ A := by
  have hx : (x : ℚ).den.Coprime p := x.2
  obtain ⟨u, hu⟩ := isUnit_natCast_of_coprime p A hA hx
  have hq : (x : ℚ) = ((x : ℚ).num : ℚ) * (((x : ℚ).den : ℚ))⁻¹ := by
    rw [← div_eq_mul_inv, Rat.num_div_den]
  rw [hq, map_mul, map_inv₀, map_intCast, map_natCast]
  refine A.toSubring.mul_mem (intCast_mem A.toSubring _) ?_
  have : ((((x : ℚ).den : ℕ) : AlgebraicClosure ℚ))⁻¹ = ((↑(u⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) := by
    apply inv_eq_of_mul_eq_one_right
    have h1 : (((x : ℚ).den : ℕ) : AlgebraicClosure ℚ) = ((↑u : ↥A) : AlgebraicClosure ℚ) := by
      rw [hu]; rfl
    rw [h1]
    show ((↑u : ↥A) : AlgebraicClosure ℚ) * ((↑u⁻¹ : ↥A) : AlgebraicClosure ℚ) = 1
    rw [← show (((↑u * ↑u⁻¹ : ↥A)) : AlgebraicClosure ℚ) = ((↑u : ↥A) : AlgebraicClosure ℚ) * ((↑u⁻¹ : ↥A) : AlgebraicClosure ℚ) from rfl,
      Units.mul_inv]
    rfl
  rw [this]
  exact SetLike.coe_mem _

end ValRing

section Embed

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)

noncomputable def rho : R p →+* ↥A :=
  ((algebraMap ℚ (AlgebraicClosure ℚ)).comp (GaloisRep.ratLocalizedAt p).subtype).codRestrict A.toSubring
    (fun x => mem_of_liesOverPrime p A hA x)

theorem rho_spec : A.subtype.comp (rho p A hA) = algebraMap (R p) (AlgebraicClosure ℚ) := by
  ext x
  rfl

include hA in

theorem isAlgebraic_residueField :
    letI := charP_residueField p A hA
    letI := ZMod.algebra (ResidueField ↥A) p
    Algebra.IsAlgebraic (ZMod p) (ResidueField ↥A) := by
  letI := charP_residueField p A hA
  letI := ZMod.algebra (ResidueField ↥A) p
  refine ⟨fun y => ?_⟩
  obtain ⟨x, rfl⟩ := residue_surjective y

  have halgQ : IsAlgebraic ℚ ((x : ↥A) : AlgebraicClosure ℚ) := by
    have h := @Algebra.IsAlgebraic.isAlgebraic ℚ (AlgebraicClosure ℚ) _ _ _ (AlgebraicClosure.isAlgebraic ℚ)
      ((x : ↥A) : AlgebraicClosure ℚ)
    convert h <;> first | rfl | exact Subsingleton.elim _ _
  have halgZ : IsAlgebraic ℤ ((x : ↥A) : AlgebraicClosure ℚ) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr halgQ
  obtain ⟨f, hf0, hfx⟩ := halgZ
  set g := f.primPart with hg
  have hgprim : g.IsPrimitive := f.isPrimitive_primPart
  have hgx : Polynomial.aeval ((x : ↥A) : AlgebraicClosure ℚ) g = 0 := by
    have h := f.eq_C_content_mul_primPart
    rw [h, map_mul, Polynomial.aeval_C] at hfx
    rcases mul_eq_zero.mp hfx with h1 | h1
    · exfalso
      rw [eq_intCast, Int.cast_eq_zero, Polynomial.content_eq_zero_iff] at h1
      exact hf0 h1
    · exact h1

  have hgA : Polynomial.aeval x g = 0 := by
    apply A.subtype_injective
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂,
      RingHom.ext_int (A.subtype.comp (algebraMap ℤ ↥A)) (algebraMap ℤ (AlgebraicClosure ℚ)), ← Polynomial.aeval_def]
    exact hgx
  have hgres : Polynomial.eval₂ (algebraMap ℤ (ResidueField ↥A)) (residue ↥A x) g = 0 := by
    have := congrArg (residue ↥A) hgA
    rwa [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂,
      RingHom.ext_int ((residue ↥A).comp (algebraMap ℤ ↥A)) (algebraMap ℤ (ResidueField ↥A))] at this

  set gp : Polynomial (ZMod p) := g.map (Int.castRingHom (ZMod p)) with hgp
  have hgp0 : gp ≠ 0 := by
    intro h0
    have hdvd : Polynomial.C (p : ℤ) ∣ g := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have : gp.coeff i = 0 := by rw [h0, Polynomial.coeff_zero]
      rw [hgp, Polynomial.coeff_map, Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      exact this
    have hu := (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hgprim) (p : ℤ) hdvd
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hu
    exact (Fact.out : p.Prime).one_lt.ne' hu
  refine ⟨gp, hgp0, ?_⟩
  rw [Polynomial.aeval_def, hgp, Polynomial.eval₂_map,
    RingHom.ext_int ((algebraMap (ZMod p) (ResidueField ↥A)).comp (Int.castRingHom (ZMod p))) (algebraMap ℤ (ResidueField ↥A))]
  exact hgres

include hA in

theorem exists_ringHom_residueField (k : Type) [Field k] [IsAlgClosed k] [CharP k p] :
    ∃ ι : ResidueField ↥A →+* k, True := by
  letI := charP_residueField p A hA
  letI := ZMod.algebra (ResidueField ↥A) p
  letI := ZMod.algebra k p
  haveI := isAlgebraic_residueField p A hA
  exact ⟨(IsAlgClosed.lift (R := ZMod p) (S := ResidueField ↥A) (M := k) : ResidueField ↥A →ₐ[ZMod p] k).toRingHom, trivial⟩

end Embed

section Pt

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

theorem exists_fibre_point (I : Ideal ↥(chartAlgFin p (ΓM M H) hj))
    [Module.Finite (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ I)]
    (𝔮 : PrimeSpectrum ↥(chartAlgFin p (ΓM M H) hj)) [h𝔮 : 𝔮.asIdeal.IsMaximal] (hI𝔮 : I ≤ 𝔮.asIdeal)
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : R p →+* κ) :
    ∃ y : ↥(fibre (Γ := ΓM M H) (hj := hj) toκ),
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ))).base y = (ιFin p (ΓM M H) hj).base 𝔮 := by
  classical
  letI : Field (↥(chartAlgFin p (ΓM M H) hj) ⧸ 𝔮.asIdeal) := Ideal.Quotient.field 𝔮.asIdeal
  obtain ⟨φ, -⟩ := exists_ringHom_quotient p M H hj I 𝔮.asIdeal hI𝔮 κ
  let φA : ↥(chartAlgFin p (ΓM M H) hj) →+* κ := φ.comp (Ideal.Quotient.mk 𝔮.asIdeal)
  have htoκ : φA.comp (algebraMap (R p) ↥(chartAlgFin p (ΓM M H) hj)) = toκ := ringHom_ext_charP p _ _
  let xκ : Spec (CommRingCat.of κ) ⟶ X p (ΓM M H) hj := Spec.map (CommRingCat.ofHom φA) ≫ ιFin p (ΓM M H) hj
  have hx : xκ ≫ toBase p (ΓM M H) hj = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom toκ) := by
    simp only [xκ, Category.assoc, Category.id_comp]
    rw [AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp, htoκ]
  refine ⟨(pullback.lift xκ (𝟙 _) hx).base (IsLocalRing.closedPoint κ), ?_⟩
  rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  simp only [xκ, Scheme.Hom.comp_apply]
  congr 1
  apply PrimeSpectrum.ext
  change Ideal.comap φA (IsLocalRing.maximalIdeal κ) = 𝔮.asIdeal
  rw [IsLocalRing.maximalIdeal_eq_bot (R := κ), ← RingHom.ker_eq_comap_bot]
  simp only [φA]
  rw [RingHom.ker_comp_of_injective _ φ.injective, Ideal.mk_ker]

end Pt

end GeomSmoothH

end

set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (v : ↥(chartAlgFin p (ΓM M H) hj))
    (hdict : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
      (y : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) (𝔮 : PrimeSpectrum ↥(chartAlgFin p (ΓM M H) hj)),
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base y = (ιFin p (ΓM M H) hj).base 𝔮 →
      v ∉ 𝔮.asIdeal → y ∈ Set.range (𝔛.comp A hA ρ hρ 0).base ∧ y ∉ Set.range (𝔛.comp A hA ρ hρ 1).base)
    (I : Ideal ↥(chartAlgFin p (ΓM M H) hj)) [Module.Finite (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ I)]
    (hIv : I ⊔ Ideal.span {v} = ⊤)
    (𝔮 : PrimeSpectrum ↥(chartAlgFin p (ΓM M H) hj)) (h𝔮 : I ≤ 𝔮.asIdeal) :
    (ιFin p (ΓM M H) hj).base 𝔮 ∈ (𝔛.smoothLocus : Set ↥(X p (ΓM M H) hj)) := by
  classical

  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p :=
    ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, Fact.out⟩
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  haveI : CharP (IsLocalRing.ResidueField ↥A) p := GeomSmoothH.charP_residueField p A hA
  let ρ := GeomSmoothH.rho p A hA
  have hρ := GeomSmoothH.rho_spec p A hA

  obtain ⟨Mx, hMx, hle⟩ := Ideal.exists_le_maximal 𝔮.asIdeal 𝔮.isPrime.ne_top
  let 𝔮₀ : PrimeSpectrum ↥(chartAlgFin p (ΓM M H) hj) := ⟨Mx, hMx.isPrime⟩
  haveI : 𝔮₀.asIdeal.IsMaximal := hMx
  have hv0 : v ∉ 𝔮₀.asIdeal := fun hv =>
    hMx.ne_top (top_le_iff.1 (hIv ▸ sup_le (h𝔮.trans hle) ((Ideal.span_singleton_le_iff_mem _).2 hv)))

  obtain ⟨y, hy⟩ := GeomSmoothH.exists_fibre_point p M H hj I 𝔮₀ (h𝔮.trans hle) ((IsLocalRing.residue ↥A).comp ρ)
  obtain ⟨hy0, hy1⟩ := hdict A hA ρ hρ y 𝔮₀ hy hv0
  have h0 : (ιFin p (ΓM M H) hj).base 𝔮₀ ∈ (𝔛.smoothLocus : Set ↥(X p (ΓM M H) hj)) := by
    rw [← hy]
    exact (ModularCurve.XHDRModelAtP.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter p M H hpM hpM2 hj 𝔛 A hA ρ hρ y).2
      (fun h => hy1 h.2)

  have hspec : 𝔮 ⤳ 𝔮₀ := (PrimeSpectrum.le_iff_specializes 𝔮 𝔮₀).1 hle
  exact (hspec.map (ιFin p (ΓM M H) hj).continuous).mem_open 𝔛.smoothLocus.isOpen h0

end S_ModularCurve_XHDRModelAtP_iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top (solution)
