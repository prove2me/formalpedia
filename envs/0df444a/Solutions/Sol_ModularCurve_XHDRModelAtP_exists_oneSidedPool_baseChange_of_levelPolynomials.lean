-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_oneSidedPool_baseChange_of_levelPolynomials
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/70cfbc04-d126-5362-88ba-685ea8683372

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
import Theorems.Thm_ModularCurve_XHDRModelAtP_iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top
import Theorems.Thm_ModularCurve_XHDRModelAtP_mem_connectedComponentIn_baseChange_of_fst_eq_iotaFin
import Theorems.Thm_ModularCurve_XHDRModelAtP_iotaFin_ne_w_iotaFin_of_span_singleton_sup_span_singleton_theta_eq_top
import Theorems.Thm_ModularCurve_XHDRModelAtP_range_epsInf_inter_range_iotaFin_eq_empty_and_range_epsZero_inter_range_iotaFin_eq_empty
import Theorems.Thm_Algebra_Etale_exists_faithfullyFlat_forall_nonempty_algEquiv_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_oneSidedPool_baseChange_of_levelPolynomials
p2m_attr_erase "instance" "GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_oneSidedPool_baseChange_of_levelPolynomials.ModularCurve ModularCurve.XHDRLevel"

p2m_open_scoped "MatrixGroups Polynomial AlgebraicGeometry.Polynomial"
open TensorProduct

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "XHDRModelAtP qExpFunctionFieldC jqModC XHDRModelAtP.iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top XHDRModelAtP.mem_connectedComponentIn_baseChange_of_fst_eq_iotaFin XHDRModelAtP.iotaFin_ne_w_iotaFin_of_span_singleton_sup_span_singleton_theta_eq_top XHDRModelAtP.range_epsInf_inter_range_iotaFin_eq_empty_and_range_epsZero_inter_range_iotaFin_eq_empty"
namespace XHDRModelAtP
p2m_export "ModularCurve.XHDRModelAtP" "w smoothLocus εzero isProper mk εinf w_over comp iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top mem_connectedComponentIn_baseChange_of_fst_eq_iotaFin iotaFin_ne_w_iotaFin_of_span_singleton_sup_span_singleton_theta_eq_top range_epsInf_inter_range_iotaFin_eq_empty_and_range_epsZero_inter_range_iotaFin_eq_empty"
p2m_open "ModularCurve.XHDRModelAtP ModularCurve"

namespace NearGeomAux

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj) (f : R p)

scoped instance instCommRingChart : CommRing ↥(chartAlgFin p (ΓM M H) hj) := Subalgebra.toCommRing (chartAlgFin p (ΓM M H) hj)

section Chart

variable (I : Ideal ↥(chartAlgFin p (ΓM M H) hj))

def ζ : Spec (CommRingCat.of (↥(chartAlgFin p (ΓM M H) hj) ⧸ I)) ⟶ X p (ΓM M H) hj :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ ιFin p (ΓM M H) hj

theorem ζ_toBase : ζ I ≫ toBase p (ΓM M H) hj = Spec.map (CommRingCat.ofHom (algebraMap (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ I))) := by
  unfold ζ; rw [Category.assoc]
  erw [AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem range_ζ : Set.range (ζ I).base =
    (ιFin p (ΓM M H) hj).base '' (PrimeSpectrum.zeroLocus (I : Set ↥(chartAlgFin p (ΓM M H) hj))) := by
  unfold ζ
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  congr 1
  change Set.range (PrimeSpectrum.comap (R := ↥(chartAlgFin p (ΓM M H) hj)) (S := ↥(chartAlgFin p (ΓM M H) hj) ⧸ I) (Ideal.Quotient.mk I)) = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]

theorem range_ζ_subset_range_ιFin : Set.range (ζ I).base ⊆ Set.range (ιFin p (ΓM M H) hj).base := by
  rw [range_ζ]; exact Set.image_subset_range _ _

theorem exists_eq_ιFin_of_mem_range_ζ {x : ↥(X p (ΓM M H) hj)} (hx : x ∈ Set.range (ζ I).base) :
    ∃ 𝔮 : PrimeSpectrum ↥(chartAlgFin p (ΓM M H) hj), I ≤ 𝔮.asIdeal ∧ x = (ιFin p (ΓM M H) hj).base 𝔮 := by
  rw [range_ζ] at hx
  obtain ⟨𝔮, h𝔮, rfl⟩ := hx
  exact ⟨𝔮, fun a ha => h𝔮 ha, rfl⟩

theorem disjoint_range_ζ {I J : Ideal ↥(chartAlgFin p (ΓM M H) hj)} (h : I ⊔ J = ⊤) : Disjoint (Set.range (ζ I).base) (Set.range (ζ J).base) := by
  rw [Set.disjoint_iff]
  rintro x ⟨hxI, hxJ⟩
  obtain ⟨𝔮, hI, rfl⟩ := exists_eq_ιFin_of_mem_range_ζ I hxI
  obtain ⟨𝔮', hJ, he⟩ := exists_eq_ιFin_of_mem_range_ζ J hxJ
  have hinj := (ιFin p (ΓM M H) hj).isOpenEmbedding.injective he
  subst hinj
  exact 𝔮.isPrime.ne_top (top_le_iff.1 (h ▸ sup_le hI hJ))

include 𝔛 in

theorem isClosedImmersion_ζ [Module.Finite (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ I)] : IsClosedImmersion (ζ I) := by
  haveI :=
    @IsClosedImmersion.spec_of_surjective (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj)) (CommRingCat.of (↥(chartAlgFin p (ΓM M H) hj) ⧸ I))
      (CommRingCat.ofHom (Ideal.Quotient.mk I)) (Ideal.Quotient.mk_surjective (I := I))
  haveI : IsPreimmersion (ζ I) := by unfold ζ; infer_instance
  haveI := 𝔛.isProper
  haveI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ I)))) := by
    rw [IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := R p) (B := ↥(chartAlgFin p (ΓM M H) hj) ⧸ I)).mpr inferInstance
  haveI : UniversallyClosed (ζ I ≫ toBase p (ΓM M H) hj) := by rw [ζ_toBase]; infer_instance
  haveI : UniversallyClosed (ζ I) := .of_comp_of_isSeparated _ (toBase p (ΓM M H) hj)
  exact .of_isPreimmersion _ (ζ I).isClosedMap.isClosed_range

end Chart

section Generic

variable (S T M : Type) [CommRing S] [CommRing T] [Algebra S T] [CommRing M] [Algebra S M]

abbrev BC : Type := TensorProduct S T M

abbrev commRing_bc : CommRing (BC S T M) := inferInstance

abbrev algebra_bc : Algebra T (BC S T M) := inferInstance

theorem finite_bc [Module.Finite S M] : Module.Finite T (BC S T M) := inferInstance

theorem etale_bc [Algebra.Etale S M] : Algebra.Etale T (BC S T M) := inferInstance

theorem rankAtStalk_bc [Module.Free S M] [Module.Finite S M] [Nontrivial S] (n : ℕ) (hn : Module.finrank S M = n) :
    Module.rankAtStalk (R := T) (BC S T M) = n := by
  rw [Module.rankAtStalk_eq_finrank_of_free]
  funext p
  haveI : Nontrivial T := by
    by_contra hT
    rw [not_nontrivial_iff_subsingleton] at hT
    exact p.isPrime.ne_top (Subsingleton.elim _ _)
  change Module.finrank T (BC S T M) = n
  rw [Module.finrank_baseChange, hn]

end Generic

section BaseChangeL

variable (I : Ideal ↥(chartAlgFin p (ΓM M H) hj))

theorem ζ_toBase' : specMap (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ I) = ζ I ≫ toBase p (ΓM M H) hj := (ζ_toBase I).symm

def zL : Spec (CommRingCat.of (BC (R p) (Localization.Away f) (↥(chartAlgFin p (ΓM M H) hj) ⧸ I))) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f)) :=
  (pullbackSpecIso (R p) (Localization.Away f) (↥(chartAlgFin p (ΓM M H) hj) ⧸ I)).inv ≫
    (pullbackSymmetry _ _).hom ≫
    pullback.map (specMap (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ I)) (specMap (R p) (Localization.Away f)) (toBase p (ΓM M H) hj)
      (specMap (R p) (Localization.Away f)) (ζ I) (𝟙 _) (𝟙 _)
      ((Category.comp_id _).trans (ζ_toBase' I)) ((Category.comp_id _).trans (Category.id_comp _).symm)

theorem zL_snd : zL f I ≫ baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f) =
    specMap (Localization.Away f) (BC (R p) (Localization.Away f) (↥(chartAlgFin p (ΓM M H) hj) ⧸ I)) := by
  unfold zL
  rw [Category.assoc, Category.assoc]
  erw [pullback.lift_snd]
  rw [Category.comp_id, pullbackSymmetry_hom_comp_snd, pullbackSpecIso_inv_fst']

theorem zL_fst : zL f I ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f)) =
    ((pullbackSpecIso (R p) (Localization.Away f) (↥(chartAlgFin p (ΓM M H) hj) ⧸ I)).inv ≫ pullback.snd _ _) ≫ ζ I := by
  unfold zL
  rw [Category.assoc, Category.assoc, Category.assoc]
  erw [pullback.lift_fst]
  rw [pullbackSymmetry_hom_comp_fst_assoc]

theorem fst_mem_range_ζ_of_mem_range_zL {x : ↥(pullback (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f)))}
    (hx : x ∈ Set.range (zL f I).base) :
    (pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))).base x ∈ Set.range (ζ I).base := by
  obtain ⟨t, rfl⟩ := hx
  rw [← Scheme.Hom.comp_apply, zL_fst, Scheme.Hom.comp_apply]
  exact ⟨_, rfl⟩

include 𝔛 in
theorem isClosedImmersion_zL [Module.Finite (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ I)] : IsClosedImmersion (zL f I) := by
  haveI := isClosedImmersion_ζ 𝔛 I
  have h := MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (f := specMap (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ I)) (g := specMap (R p) (Localization.Away f)) (f' := toBase p (ΓM M H) hj)
    (g' := specMap (R p) (Localization.Away f)) (i₁ := ζ I) (i₂ := 𝟙 _)
    inferInstance inferInstance (ζ_toBase' I) (Category.id_comp _).symm
  unfold zL
  infer_instance

end BaseChangeL

section Disjoint

variable (I J : Ideal ↥(chartAlgFin p (ΓM M H) hj))

theorem exists_eq_ιFin_of_mem_range_zL {x : ↥(pullback (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f)))}
    (hx : x ∈ Set.range (zL f I).base) :
    ∃ 𝔮 : PrimeSpectrum ↥(chartAlgFin p (ΓM M H) hj), I ≤ 𝔮.asIdeal ∧
      (pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))).base x = (ιFin p (ΓM M H) hj).base 𝔮 :=
  exists_eq_ιFin_of_mem_range_ζ I (fst_mem_range_ζ_of_mem_range_zL f I hx)

theorem disjoint_range_zL {I J : Ideal ↥(chartAlgFin p (ΓM M H) hj)} (h : I ⊔ J = ⊤) :
    Disjoint (Set.range (zL f I).base) (Set.range (zL f J).base) := by
  rw [Set.disjoint_iff]
  rintro x ⟨hxI, hxJ⟩
  exact Set.disjoint_iff.1 (disjoint_range_ζ h) ⟨fst_mem_range_ζ_of_mem_range_zL f I hxI, fst_mem_range_ζ_of_mem_range_zL f J hxJ⟩

theorem disjoint_range_zL_range_sectionBaseChange (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase p (ΓM M H) hj))
    (hε : Set.range ε.1.base ∩ Set.range (ιFin p (ΓM M H) hj).base = ∅) :
    Disjoint (Set.range (zL f I).base) (Set.range (sectionBaseChange (Localization.Away f) ε).1.base) := by
  rw [Set.disjoint_iff]
  rintro x ⟨hxI, ⟨t, rfl⟩⟩
  have h1 := range_ζ_subset_range_ιFin I (fst_mem_range_ζ_of_mem_range_zL f I hxI)
  have h2 : (pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))).base
      ((sectionBaseChange (Localization.Away f) ε).1.base t) ∈ Set.range ε.1.base := by
    rw [← Scheme.Hom.comp_apply, sectionBaseChange_coe_fst, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have : _ ∈ Set.range ε.1.base ∩ Set.range (ιFin p (ΓM M H) hj).base := ⟨h2, h1⟩
  rw [hε] at this
  exact this

abbrev wL : pullback (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f)) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f)) :=
  curveChange 𝔛.w.hom 𝔛.w_over (specMap (R p) (Localization.Away f))

theorem wL_fst : wL 𝔛 f ≫ pullback.fst _ _ = pullback.fst _ _ ≫ 𝔛.w.hom := by
  unfold wL curveChange; rw [pullback.lift_fst]

theorem disjoint_range_zL_range_zL_wL {I J : Ideal ↥(chartAlgFin p (ΓM M H) hj)}
    (h : ∀ 𝔮 𝔮' : PrimeSpectrum ↥(chartAlgFin p (ΓM M H) hj), I ≤ 𝔮.asIdeal → J ≤ 𝔮'.asIdeal →
      (ιFin p (ΓM M H) hj).base 𝔮 ≠ 𝔛.w.hom.base ((ιFin p (ΓM M H) hj).base 𝔮')) :
    Disjoint (Set.range (zL f I).base) (Set.range (zL f J ≫ wL 𝔛 f).base) := by
  rw [Set.disjoint_iff]
  rintro x ⟨hxI, ⟨t, rfl⟩⟩
  obtain ⟨𝔮, hI, h𝔮⟩ := exists_eq_ιFin_of_mem_range_zL f I hxI
  obtain ⟨𝔮', hJ, h𝔮'⟩ := exists_eq_ιFin_of_mem_range_zL f J (x := (zL f J).base t) ⟨t, rfl⟩
  apply h 𝔮 𝔮' hI hJ
  rw [← h𝔮, ← h𝔮', Scheme.Hom.comp_apply]
  erw [← Scheme.Hom.comp_apply (wL 𝔛 f) (pullback.fst _ _), wL_fst, Scheme.Hom.comp_apply]

end Disjoint

section Data

abbrev lev (v : ↥(chartAlgFin p (ΓM M H) hj)) (P : ℤ[X]) : Ideal ↥(chartAlgFin p (ΓM M H) hj) :=
  Ideal.span {Polynomial.aeval v P}

theorem theta_aeval (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (v : ↥(chartAlgFin p (ΓM M H) hj)) (P : ℤ[X]) :
    theta (Polynomial.aeval v P) = Polynomial.aeval (theta v) P :=
  (Polynomial.aeval_algHom_apply (theta.toAlgHom.toRingHom.toIntAlgHom) v P).symm

theorem not_mem_of_sup_span_singleton_eq_top {I : Ideal ↥(chartAlgFin p (ΓM M H) hj)} {v : ↥(chartAlgFin p (ΓM M H) hj)}
    (h : I ⊔ Ideal.span {v} = ⊤) (𝔮 : PrimeSpectrum ↥(chartAlgFin p (ΓM M H) hj)) (hI : I ≤ 𝔮.asIdeal) :
    v ∉ 𝔮.asIdeal := fun hv =>
  𝔮.isPrime.ne_top (top_le_iff.1 (h ▸ sup_le hI ((Ideal.span_singleton_le_iff_mem _).2 hv)))

variable (I : Ideal ↥(chartAlgFin p (ΓM M H) hj))

abbrev BL : Type := BC (R p) (Localization.Away f) (↥(chartAlgFin p (ΓM M H) hj) ⧸ I)

end Data

section Family
variable (v : ↥(chartAlgFin p (ΓM M H) hj)) {N₁ : ℕ} (g : Fin N₁ → ℤ[X])

abbrev famB (i : Fin N₁) : Type := BL f (lev v (g i))

end Family

section Clauses

variable (hpM2 : ¬ p ^ 2 ∣ M) (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
  (v : ↥(chartAlgFin p (ΓM M H) hj))

include 𝔛 hpM2 hHp

theorem range_zL_subset_preimage_smoothLocus
    (hdict : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
      (y : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) (𝔮 : PrimeSpectrum ↥(chartAlgFin p (ΓM M H) hj)),
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base y = (ιFin p (ΓM M H) hj).base 𝔮 →
      v ∉ 𝔮.asIdeal → y ∈ Set.range (𝔛.comp A hA ρ hρ 0).base ∧ y ∉ Set.range (𝔛.comp A hA ρ hρ 1).base)
    (I : Ideal ↥(chartAlgFin p (ΓM M H) hj)) [Module.Finite (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ I)] (hIv : I ⊔ Ideal.span {v} = ⊤) :
    Set.range (zL f I).base ⊆
      ((pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f)) ⁻¹ᵁ 𝔛.smoothLocus : (pullback (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))).Opens) : Set ↥(pullback (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f)))) := by
  intro x hx
  obtain ⟨𝔮, hI, hq⟩ := exists_eq_ιFin_of_mem_range_zL f I hx
  show (pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))).base x ∈ (𝔛.smoothLocus : Set ↥(X p (ΓM M H) hj))
  rw [hq]
  exact ModularCurve.XHDRModelAtP.iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top p M H hpM hpM2 hHp hj 𝔛 v hdict I hIv 𝔮 hI

theorem preimage_range_zL_subset_connectedComponentIn
    (hdict : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
      (y : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) (𝔮 : PrimeSpectrum ↥(chartAlgFin p (ΓM M H) hj)),
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base y = (ιFin p (ΓM M H) hj).base 𝔮 →
      v ∉ 𝔮.asIdeal → y ∈ Set.range (𝔛.comp A hA ρ hρ 0).base ∧ y ∉ Set.range (𝔛.comp A hA ρ hρ 1).base)
    (I : Ideal ↥(chartAlgFin p (ΓM M H) hj)) [Module.Finite (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ I)] (hIv : I ⊔ Ideal.span {v} = ⊤)
    (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f))) :
    (pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s).base ⁻¹' Set.range (zL f I).base ⊆
      connectedComponentIn
        (((pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
            (pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R p) (toBase p (ΓM M H) hj) (Localization.Away f)) s))
        (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k)) := by
  intro y hy
  obtain ⟨𝔮, hI, hq⟩ := exists_eq_ιFin_of_mem_range_zL f I hy
  exact ModularCurve.XHDRModelAtP.mem_connectedComponentIn_baseChange_of_fst_eq_iotaFin p M H hpM hpM2 hHp hj 𝔛 f v hdict k s y 𝔮
    (not_mem_of_sup_span_singleton_eq_top hIv 𝔮 hI)
    (ModularCurve.XHDRModelAtP.iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top p M H hpM hpM2 hHp hj 𝔛 v hdict I hIv 𝔮 hI)
    (by rw [Scheme.Hom.comp_apply]; exact hq)

theorem disjoint_range_zL_range_zL_wL_of_levelPolynomials
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (hwchart : ιFin p (ΓM M H) hj ≫ 𝔛.w.hom = Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ ιFin p (ΓM M H) hj)
    {N₁ : ℕ} (g : Fin N₁ → ℤ[X])
    (hcopw : ∀ i j, Ideal.span {Polynomial.aeval v (g i)} ⊔ Ideal.span {Polynomial.aeval (theta v) (g j)} = (⊤ : Ideal ↥(chartAlgFin p (ΓM M H) hj)))
    (i j : Fin N₁) :
    Disjoint (Set.range (zL f (lev v (g i))).base) (Set.range (zL f (lev v (g j)) ≫ wL 𝔛 f).base) := by
  refine disjoint_range_zL_range_zL_wL 𝔛 f (fun 𝔮 𝔮' hI hJ => ?_)
  have hab : Ideal.span {Polynomial.aeval v (g j)} ⊔ Ideal.span {theta (Polynomial.aeval v (g i))} = ⊤ := by
    rw [theta_aeval]; exact hcopw j i
  exact ModularCurve.XHDRModelAtP.iotaFin_ne_w_iotaFin_of_span_singleton_sup_span_singleton_theta_eq_top p M H hpM hpM2 hHp hj 𝔛
    theta hwchart _ _ hab 𝔮 𝔮' ((Ideal.span_singleton_le_iff_mem _).1 hI) ((Ideal.span_singleton_le_iff_mem _).1 hJ)

end Clauses

end NearGeomAux
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_oneSidedPool_baseChange_of_levelPolynomials.ModularCurve.XHDRModelAtP.NearGeomAux"

end ModularCurve.XHDRModelAtP
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_oneSidedPool_baseChange_of_levelPolynomials.ModularCurve.XHDRModelAtP.NearGeomAux P2MW.S_ModularCurve_XHDRModelAtP_exists_oneSidedPool_baseChange_of_levelPolynomials.ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_oneSidedPool_baseChange_of_levelPolynomials.ModularCurve.XHDRModelAtP"
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_oneSidedPool_baseChange_of_levelPolynomials.ModularCurve.XHDRModelAtP.NearGeomAux P2MW.S_ModularCurve_XHDRModelAtP_exists_oneSidedPool_baseChange_of_levelPolynomials.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_oneSidedPool_baseChange_of_levelPolynomials.ModularCurve.XHDRModelAtP.NearGeomAux P2MW.S_ModularCurve_XHDRModelAtP_exists_oneSidedPool_baseChange_of_levelPolynomials.ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_oneSidedPool_baseChange_of_levelPolynomials.ModularCurve.XHDRModelAtP"

open _root_.ModularCurve.XHDRModelAtP _root_.P2MW.S_ModularCurve_XHDRModelAtP_exists_oneSidedPool_baseChange_of_levelPolynomials.ModularCurve.XHDRModelAtP ModularCurve.XHDRModelAtP.NearGeomAux in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (hwchart : ιFin p (ΓM M H) hj ≫ 𝔛.w.hom = Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ ιFin p (ΓM M H) hj)
    (hwfin : 𝔛.w.hom ⁻¹ᵁ (ιFin p (ΓM M H) hj).opensRange = (ιFin p (ΓM M H) hj).opensRange)
    (f : R p)
    (v : ↥(chartAlgFin p (ΓM M H) hj))

    (hdict : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
      (y : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) (𝔮 : PrimeSpectrum ↥(chartAlgFin p (ΓM M H) hj)),
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base y = (ιFin p (ΓM M H) hj).base 𝔮 →
      v ∉ 𝔮.asIdeal → y ∈ Set.range (𝔛.comp A hA ρ hρ 0).base ∧ y ∉ Set.range (𝔛.comp A hA ρ hρ 1).base)
    (b N₁ : ℕ) (g : Fin N₁ → ℤ[X]) (rk : Fin N₁ → ℕ)
    (hmonic : ∀ i, (g i).Monic)
    (hfin : ∀ i, Module.Finite (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v (g i)})) (het : ∀ i, Algebra.Etale (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v (g i)}))
    (hfree : ∀ i, Module.Free (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v (g i)})) (hrk : ∀ i, Module.finrank (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v (g i)}) = rk i)
    (hrk1 : ∀ i, 1 ≤ rk i) (hrkb : ∀ i, rk i ≤ b)
    (hcop : Pairwise fun i j => Ideal.span {Polynomial.aeval v (g i)} ⊔ Ideal.span {Polynomial.aeval v (g j)} = (⊤ : Ideal ↥(chartAlgFin p (ΓM M H) hj)))
    (hcopw : ∀ i j, Ideal.span {Polynomial.aeval v (g i)} ⊔ Ideal.span {Polynomial.aeval (theta v) (g j)} = (⊤ : Ideal ↥(chartAlgFin p (ΓM M H) hj)))
    (hcopv : ∀ i, Ideal.span {Polynomial.aeval v (g i)} ⊔ Ideal.span {v} = (⊤ : Ideal ↥(chartAlgFin p (ΓM M H) hj))) :
    ∃ (R' : Type) (_ : CommRing R') (_ : Algebra (R p) R') (_ : Algebra (Localization.Away f) R')
      (_ : IsScalarTower (R p) (Localization.Away f) R')
      (_ : Module.Finite (Localization.Away f) R') (_ : Algebra.Etale (Localization.Away f) R')
      (_ : Module.FaithfullyFlat (Localization.Away f) R')
      (B : Fin N₁ → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra (Localization.Away f) (B i))
      (_ : ∀ i, Module.Finite (Localization.Away f) (B i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B i))
      (deg : Fin N₁ → ℕ) (_ : ∀ i, 1 ≤ deg i) (_ : ∀ i, deg i ≤ b)
      (φ : ∀ i, TensorProduct (Localization.Away f) R' (B i) ≃ₐ[R'] (Fin (deg i) → R'))
      (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) (Localization.Away f)))
      (_ : ∀ i, IsClosedImmersion (z i)),
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
      (∀ i, Disjoint (Set.range (z i).base) (Set.range (sectionBaseChange (Localization.Away f) 𝔛.εinf).1.base)) ∧
      (∀ i, Disjoint (Set.range (z i).base) (Set.range (sectionBaseChange (Localization.Away f) 𝔛.εzero).1.base)) ∧
      (∀ i j, Disjoint (Set.range (z i).base)
      (Set.range (z j ≫ curveChange 𝔛.w.hom 𝔛.w_over (specMap (R p) (Localization.Away f))).base)) := by
  classical
  haveI : ∀ i, Module.Finite (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ lev v (g i)) := hfin
  haveI : ∀ i, Algebra.Etale (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ lev v (g i)) := het
  haveI : ∀ i, Module.Free (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ lev v (g i)) := hfree
  obtain ⟨R', _, _, hR'fin, hR'et, hR'ff, hφ⟩ :=
    @Algebra.Etale.exists_faithfullyFlat_forall_nonempty_algEquiv_pi (Localization.Away f) _ (Fin N₁) _ (famB f v g)
      (fun i => commRing_bc (R p) (Localization.Away f) (↥(chartAlgFin p (ΓM M H) hj) ⧸ lev v (g i)))
      (fun i => algebra_bc (R p) (Localization.Away f) (↥(chartAlgFin p (ΓM M H) hj) ⧸ lev v (g i)))
      (fun i => finite_bc (R p) (Localization.Away f) (↥(chartAlgFin p (ΓM M H) hj) ⧸ lev v (g i)))
      (fun i => etale_bc (R p) (Localization.Away f) (↥(chartAlgFin p (ΓM M H) hj) ⧸ lev v (g i)))
      rk (fun i => rankAtStalk_bc (R p) (Localization.Away f) (↥(chartAlgFin p (ΓM M H) hj) ⧸ lev v (g i)) (rk i) (hrk i))
  letI : Algebra (R p) R' := ((algebraMap (Localization.Away f) R').comp (algebraMap (R p) (Localization.Away f))).toAlgebra
  haveI : IsScalarTower (R p) (Localization.Away f) R' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hN6 := ModularCurve.XHDRModelAtP.range_epsInf_inter_range_iotaFin_eq_empty_and_range_epsZero_inter_range_iotaFin_eq_empty p M H hpM hpM2 hHp hj 𝔛 hwfin
  refine ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, hR'fin, hR'et, hR'ff,
    famB f v g, fun i => commRing_bc (R p) (Localization.Away f) (↥(chartAlgFin p (ΓM M H) hj) ⧸ lev v (g i)),
    fun i => algebra_bc (R p) (Localization.Away f) (↥(chartAlgFin p (ΓM M H) hj) ⧸ lev v (g i)),
    fun i => finite_bc (R p) (Localization.Away f) (↥(chartAlgFin p (ΓM M H) hj) ⧸ lev v (g i)),
    fun i => etale_bc (R p) (Localization.Away f) (↥(chartAlgFin p (ΓM M H) hj) ⧸ lev v (g i)), rk, hrk1, hrkb,
    fun i => (hφ i).some, fun i => zL f (lev v (g i)), fun i => isClosedImmersion_zL 𝔛 f (lev v (g i)),
    fun i => zL_snd f (lev v (g i)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro i
    exact range_zL_subset_preimage_smoothLocus 𝔛 f hpM2 hHp v hdict (lev v (g i)) (hcopv i)
  ·
    intro i j hij
    exact disjoint_range_zL f (hcop hij)
  ·
    intro k _ _ s i
    exact preimage_range_zL_subset_connectedComponentIn 𝔛 f hpM2 hHp v hdict (lev v (g i)) (hcopv i) k s
  ·
    intro i
    exact disjoint_range_zL_range_sectionBaseChange f (lev v (g i)) 𝔛.εinf hN6.1
  ·
    intro i
    exact disjoint_range_zL_range_sectionBaseChange f (lev v (g i)) 𝔛.εzero hN6.2
  ·
    intro i j
    exact disjoint_range_zL_range_zL_wL_of_levelPolynomials 𝔛 f hpM2 hHp v theta hwchart g hcopw i j

end S_ModularCurve_XHDRModelAtP_exists_oneSidedPool_baseChange_of_levelPolynomials
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_oneSidedPool_baseChange_of_levelPolynomials (solution)
