-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.range_comp_bcMap_eq_closure_and_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/fdfe73a6-1c66-5b81-9be1-c6c74a2eee37

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import Theorems.Thm_ModularCurve_XHDRModelAtP_finite_crossings
import Theorems.Thm_ModularCurve_XHDRModelAtP_xiInf_ne_xiZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_range_comp_bcMap_eq_closure_and_isClosed
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply"
p2m_attr_erase "simp" "ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.mulAdele_apply"
p2m_attr_erase "simp" "AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

noncomputable section

namespace ECL_FibN
open ModularCurve ModularCurve.XHDRLevel

theorem isIntegral_fibreN {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) :=
  letI := (𝔛.Mfib A hA ρ hρ).isIntegral
  IsIntegral.of_isIso (𝔛.efib A hA ρ hρ)

theorem efib_genericPoint_eq {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))] :
    letI := (𝔛.Mfib A hA ρ hρ).isIntegral
    (𝔛.efib A hA ρ hρ).base (genericPoint (𝔛.Mfib A hA ρ hρ).C) =
      genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) := by
  letI := (𝔛.Mfib A hA ρ hρ).isIntegral
  refine IsGenericPoint.eq (S := ⊤) ?_ (genericPoint_spec _)
  rw [isGenericPoint_iff_specializes]
  intro y
  simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
  exact 𝔛.efib_genericPoint_specializes A hA ρ hρ y

end ECL_FibN

namespace ECL_Range

private theorem surjective_fst_of_mem_range {C Z : Scheme} [IrreducibleSpace C] (i₁ i₂ : C ⟶ Z) [IsClosedImmersion i₂]
    (h : i₁.base (genericPoint C) ∈ Set.range ⇑i₂.base) :
    Function.Surjective ⇑(pullback.fst i₁ i₂).base := by
  have hsub : Set.range ⇑i₁.base ⊆ Set.range ⇑i₂.base := by
    have h1 : Set.range ⇑i₁.base = ⇑i₁.base '' closure {genericPoint C} := by
      rw [genericPoint_closure, Set.image_univ]
    rw [h1]
    refine (image_closure_subset_closure_image i₁.base.hom.continuous).trans ?_
    rw [Set.image_singleton]
    exact closure_minimal (Set.singleton_subset_iff.mpr h) i₂.isClosedEmbedding.isClosed_range
  intro c
  obtain ⟨c', hc'⟩ := hsub ⟨c, rfl⟩
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i₁) (g := i₂) c c' hc'.symm
  exact ⟨z, hz⟩

private theorem surjective_snd_of_mem_range {C Z : Scheme} [IrreducibleSpace C] (i₁ i₂ : C ⟶ Z) [IsClosedImmersion i₁]
    (h : i₂.base (genericPoint C) ∈ Set.range ⇑i₁.base) :
    Function.Surjective ⇑(pullback.snd i₁ i₂).base := by
  have hsub : Set.range ⇑i₂.base ⊆ Set.range ⇑i₁.base := by
    have h1 : Set.range ⇑i₂.base = ⇑i₂.base '' closure {genericPoint C} := by
      rw [genericPoint_closure, Set.image_univ]
    rw [h1]
    refine (image_closure_subset_closure_image i₂.base.hom.continuous).trans ?_
    rw [Set.image_singleton]
    exact closure_minimal (Set.singleton_subset_iff.mpr h) i₁.isClosedEmbedding.isClosed_range
  intro c
  obtain ⟨c', hc'⟩ := hsub ⟨c, rfl⟩
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := i₁) (g := i₂) c' c hc'
  exact ⟨z, hz⟩

section Engine
variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
  (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

private theorem not_surjective_of_crossing
    (f : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)) → ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) :
    ¬ Function.Surjective f := by
  intro hf
  haveI := ECL_FibN.isIntegral_fibreN 𝔛 A hA ρ hρ
  haveI : SmoothOfRelativeDimension 1
      (pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ 𝔛.smooth0
  haveI : Infinite ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) := by
    have h := AlgebraicCurve.infinite_setOf_isClosed_singleton
      (pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))
    exact Set.infinite_univ_iff.mp (h.mono (Set.subset_univ _))
  haveI : Infinite ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)) := Infinite.of_surjective f hf
  haveI : Finite ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)) := 𝔛.finite_crossings A hA ρ hρ
  exact not_finite ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))

private theorem comp0_genericPoint_notMem_range_comp1 [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))] :
    (𝔛.comp A hA ρ hρ 0).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) ∉ Set.range ⇑(𝔛.comp A hA ρ hρ 1).base := fun h =>
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 1
  not_surjective_of_crossing 𝔛 A hA ρ hρ _ (surjective_fst_of_mem_range _ _ h)

private theorem comp1_genericPoint_notMem_range_comp0 [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))] :
    (𝔛.comp A hA ρ hρ 1).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) ∉ Set.range ⇑(𝔛.comp A hA ρ hρ 0).base := fun h =>
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 0
  not_surjective_of_crossing 𝔛 A hA ρ hρ _ (surjective_snd_of_mem_range _ _ h)

theorem eq_of_specializes_comp0_genericPoint [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))]
    (z : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (hz : z ⤳ (𝔛.comp A hA ρ hρ 0).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))) :
    z = (𝔛.comp A hA ρ hρ 0).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) := by
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 0
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 1
  rcases 𝔛.comp_jointly_surjective A hA ρ hρ z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have hc : c ⤳ genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) :=
      (𝔛.comp A hA ρ hρ 0).isClosedEmbedding.isInducing.specializes_iff.mp hz
    rw [(hc.antisymm (genericPoint_specializes c)).eq]
  · exact absurd (hz.mem_closed (𝔛.comp A hA ρ hρ 1).isClosedEmbedding.isClosed_range ⟨c, rfl⟩)
      (comp0_genericPoint_notMem_range_comp1 𝔛 A hA ρ hρ)

theorem eq_of_specializes_comp1_genericPoint [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))]
    (z : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (hz : z ⤳ (𝔛.comp A hA ρ hρ 1).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))) :
    z = (𝔛.comp A hA ρ hρ 1).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) := by
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 0
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 1
  rcases 𝔛.comp_jointly_surjective A hA ρ hρ z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact absurd (hz.mem_closed (𝔛.comp A hA ρ hρ 0).isClosedEmbedding.isClosed_range ⟨c, rfl⟩)
      (comp1_genericPoint_notMem_range_comp0 𝔛 A hA ρ hρ)
  · have hc : c ⤳ genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) :=
      (𝔛.comp A hA ρ hρ 1).isClosedEmbedding.isInducing.specializes_iff.mp hz
    rw [(hc.antisymm (genericPoint_specializes c)).eq]

end Engine

section Local
variable {p : ℕ} (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

def fibreMapOfComp {A B : Type} [CommRing A] [CommRing B] (τA : R p →+* A) (τB : R p →+* B)
    (φ : A →+* B) (h : φ.comp τA = τB) : fibre (Γ := Γ) (hj := hj) τB ⟶ fibre (Γ := Γ) (hj := hj) τA :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom φ)) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h])

@[reassoc]
theorem fibreMapOfComp_fst {A B : Type} [CommRing A] [CommRing B] (τA : R p →+* A) (τB : R p →+* B)
    (φ : A →+* B) (h : φ.comp τA = τB) :
    fibreMapOfComp Γ hj τA τB φ h ≫ pullback.fst _ _ = pullback.fst _ _ := by
  rw [fibreMapOfComp, pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc]
theorem fibreMapOfComp_snd {A B : Type} [CommRing A] [CommRing B] (τA : R p →+* A) (τB : R p →+* B)
    (φ : A →+* B) (h : φ.comp τA = τB) :
    fibreMapOfComp Γ hj τA τB φ h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φ) :=
  pullback.lift_snd _ _ _

theorem bcMap_eq_fibreMapOfComp {O : Type} [CommRing O] (ρO : R p →+* O) {κ : Type} [CommRing κ] (toκ : O →+* κ)
    {toκ' : R p →+* κ} (hto : toκ.comp ρO = toκ') :
    bcMap Γ hj ρO toκ hto = fibreMapOfComp Γ hj ρO toκ' toκ hto := by
  apply pullback.hom_ext
  · rw [fibreMapOfComp_fst, bcMap_fst]
  · rw [fibreMapOfComp_snd, bcMap_snd]

theorem fibreMapOfComp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (τA : R p →+* A) (τB : R p →+* B) (τC : R p →+* C)
    (φ : A →+* B) (hφ : φ.comp τA = τB) (ψ : B →+* C) (hψ : ψ.comp τB = τC)
    (χ : A →+* C) (hχ : χ.comp τA = τC) (e : ψ.comp φ = χ) :
    fibreMapOfComp Γ hj τB τC ψ hψ ≫ fibreMapOfComp Γ hj τA τB φ hφ =
      fibreMapOfComp Γ hj τA τC χ hχ := by
  subst e
  apply pullback.hom_ext
  · simp only [Category.assoc, fibreMapOfComp_fst]
  · simp only [Category.assoc, fibreMapOfComp_snd, fibreMapOfComp_snd_assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem isPullback_fibreMapOfComp {A B : Type} [CommRing A] [CommRing B] (τA : R p →+* A) (τB : R p →+* B)
    (φ : A →+* B) (h : φ.comp τA = τB) :
    IsPullback (fibreMapOfComp Γ hj τA τB φ h)
      (pullback.snd (toBase p Γ hj) (Spec.map (CommRingCat.ofHom τB)))
      (pullback.snd (toBase p Γ hj) (Spec.map (CommRingCat.ofHom τA)))
      (Spec.map (CommRingCat.ofHom φ)) := by
  have hρι : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom τA) = Spec.map (CommRingCat.ofHom τB) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
  have key : IsPullback (fibreMapOfComp Γ hj τA τB φ h ≫ pullback.fst (toBase p Γ hj) _)
      (pullback.snd (toBase p Γ hj) (Spec.map (CommRingCat.ofHom τB))) (toBase p Γ hj)
      (Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom τA)) := by
    rw [fibreMapOfComp_fst, hρι]
    exact IsPullback.of_hasPullback _ _
  exact IsPullback.of_right key (fibreMapOfComp_snd Γ hj τA τB φ h) (IsPullback.of_hasPullback _ _)

theorem isClosedImmersion_fibreMapOfComp {A B : Type} [CommRing A] [CommRing B] (τA : R p →+* A)
    (τB : R p →+* B) (φ : A →+* B) (h : φ.comp τA = τB) (hφ : Function.Surjective φ) :
    IsClosedImmersion (fibreMapOfComp Γ hj τA τB φ h) := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) := IsClosedImmersion.spec_of_surjective _ hφ
  exact MorphismProperty.of_isPullback (isPullback_fibreMapOfComp Γ hj τA τB φ h).flip inferInstance

theorem flat_fibreMapOfComp {A B : Type} [Field A] [Field B] (τA : R p →+* A)
    (τB : R p →+* B) (φ : A →+* B) (h : φ.comp τA = τB) :
    Flat (fibreMapOfComp Γ hj τA τB φ h) := by
  haveI : Flat (Spec.map (CommRingCat.ofHom φ)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := φ.toAlgebra
    show RingHom.Flat (algebraMap A B)
    rw [RingHom.Flat]
    convert (inferInstance : Module.Flat A B)
  exact MorphismProperty.of_isPullback (isPullback_fibreMapOfComp Γ hj τA τB φ h).flip inferInstance

theorem surjective_fibreMapOfComp {A B : Type} [Field A] [Field B] (τA : R p →+* A)
    (τB : R p →+* B) (φ : A →+* B) (h : φ.comp τA = τB) :
    Surjective (fibreMapOfComp Γ hj τA τB φ h) := by
  haveI : Surjective (Spec.map (CommRingCat.ofHom φ)) := ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
  exact MorphismProperty.of_isPullback (isPullback_fibreMapOfComp Γ hj τA τB φ h).flip inferInstance

variable {O : Type} [CommRing O] [IsLocalRing O] (ρO : R p →+* O)
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  {κ : Type} [Field κ] [CharP κ p] (toκ : O →+* κ) {toκ' : R p →+* κ} (hto : toκ.comp ρO = toκ')

include hϖ in

theorem toκ_maximalIdeal [Fact p.Prime] (a : O) (ha : a ∈ IsLocalRing.maximalIdeal O) : toκ a = 0 := by
  rw [hϖ, Ideal.mem_span_singleton] at ha
  obtain ⟨r, rfl⟩ := ha
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

def ι [Fact p.Prime] : IsLocalRing.ResidueField O →+* κ :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) toκ (toκ_maximalIdeal hϖ toκ)

include hto in
theorem ι_comp [Fact p.Prime] : (ι hϖ toκ).comp ((IsLocalRing.residue O).comp ρO) = toκ' := by
  subst hto; exact RingHom.ext fun _ => rfl

theorem bcMap_eq_comp [Fact p.Prime] :
    bcMap Γ hj ρO toκ hto =
      fibreMapOfComp Γ hj ((IsLocalRing.residue O).comp ρO) toκ' (ι hϖ toκ) (ι_comp ρO hϖ toκ hto) ≫
        bcMap Γ hj ρO (IsLocalRing.residue O) rfl := by
  subst hto
  rw [bcMap_eq_fibreMapOfComp, bcMap_eq_fibreMapOfComp,
    fibreMapOfComp_comp (χ := toκ) (hχ := rfl) (e := RingHom.ext fun _ => rfl)]

include hϖ in

theorem exists_bcMap_residue_eq (y : ↥(XO Γ hj ρO))
    (hy : y ∉ (XO.toBase Γ hj ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) :
    ∃ y₀, (bcMap Γ hj ρO (IsLocalRing.residue O) rfl).base y₀ = y := by
  set s := (XO.toBase Γ hj ρO).base y with hs
  have hps : ((p : ℕ) : O) ∈ s.asIdeal := by
    by_contra h
    exact hy h
  have hsm : s = IsLocalRing.closedPoint O := by
    apply PrimeSpectrum.ext
    have hle : IsLocalRing.maximalIdeal O ≤ s.asIdeal := by
      rw [hϖ, Ideal.span_singleton_le_iff_mem]
      exact hps
    exact ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le s.isPrime.ne_top hle).symm
  have hpt : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))).base
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) = s := by
    rw [hsm]
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue O)
  rw [bcMap_eq_fibreMapOfComp]
  obtain ⟨y₀, hy₀, -⟩ := Scheme.exists_preimage_of_isPullback
    (isPullback_fibreMapOfComp Γ hj ρO ((IsLocalRing.residue O).comp ρO) (IsLocalRing.residue O) rfl) y
    (IsLocalRing.closedPoint _) (by rw [hpt])
  exact ⟨y₀, hy₀⟩

end Local

section Main
variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
  (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
  {O : Type} [CommRing O] [IsLocalRing O] (ρO : R p →+* O)
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  (toκ : O →+* IsLocalRing.ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)

theorem bcMap_apply_notMem (z : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) :
    (bcMap (ΓM M H) hj ρO toκ htoκ).base z ∉ (XO.toBase (ΓM M H) hj ρO) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := by
  intro h
  have hcomm : bcMap (ΓM M H) hj ρO toκ htoκ ≫ XO.toBase (ΓM M H) hj ρO = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ) :=
    bcMap_snd _ _ _ _ _
  have h' : (bcMap (ΓM M H) hj ρO toκ htoκ ≫ XO.toBase (ΓM M H) hj ρO).base z ∈
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := h
  rw [hcomm] at h'
  change PrimeSpectrum.comap toκ ((pullback.snd (toBase p (ΓM M H) hj)
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base z) ∈ PrimeSpectrum.basicOpen ((p : ℕ) : O) at h'
  rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_natCast,
    CharP.cast_eq_zero] at h'
  exact h' (Ideal.zero_mem _)

include hϖ in

theorem exists_bcMap_eq (y : ↥(XO (ΓM M H) hj ρO))
    (hy : y ∉ (XO.toBase (ΓM M H) hj ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) :
    ∃ z, (bcMap (ΓM M H) hj ρO toκ htoκ).base z = y := by
  obtain ⟨y₀, rfl⟩ := exists_bcMap_residue_eq (ΓM M H) hj ρO hϖ y hy
  haveI := surjective_fibreMapOfComp (ΓM M H) hj ((IsLocalRing.residue O).comp ρO) ((IsLocalRing.residue ↥A).comp ρ) (ι hϖ toκ) (ι_comp ρO hϖ toκ htoκ)
  obtain ⟨z, rfl⟩ := (fibreMapOfComp (ΓM M H) hj ((IsLocalRing.residue O).comp ρO) ((IsLocalRing.residue ↥A).comp ρ) (ι hϖ toκ) (ι_comp ρO hϖ toκ htoκ)).surjective y₀
  refine ⟨z, ?_⟩
  rw [bcMap_eq_comp (ΓM M H) hj ρO hϖ toκ htoκ, Scheme.Hom.comp_apply]

include hϖ in

theorem eq_of_specializes_aux [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))]
    (i : fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (hi : ∀ z, z ⤳ i.base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) → z = i.base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))))
    (y : ↥(XO (ΓM M H) hj ρO))
    (hy : y ∉ (XO.toBase (ΓM M H) hj ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))
    (h : y ⤳ (i ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))) :
    y = (i ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) := by
  set η := genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
  set g := fibreMapOfComp (ΓM M H) hj ((IsLocalRing.residue O).comp ρO) ((IsLocalRing.residue ↥A).comp ρ) (ι hϖ toκ) (ι_comp ρO hϖ toκ htoκ) with hg
  set j := bcMap (ΓM M H) hj ρO (IsLocalRing.residue O) rfl with hjj
  haveI : IsClosedImmersion j := by
    rw [hjj, bcMap_eq_fibreMapOfComp]
    exact isClosedImmersion_fibreMapOfComp _ _ _ _ _ rfl Ideal.Quotient.mk_surjective
  haveI : Flat g := flat_fibreMapOfComp _ _ _ _ _ _
  have hξ : (i ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base η = j.base (g.base (i.base η)) := by
    rw [bcMap_eq_comp (ΓM M H) hj ρO hϖ toκ htoκ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  rw [hξ] at h ⊢
  obtain ⟨y₀, rfl⟩ := exists_bcMap_residue_eq (ΓM M H) hj ρO hϖ y hy
  have h₀ : y₀ ⤳ g.base (i.base η) := j.isClosedEmbedding.isInducing.specializes_iff.mp h
  obtain ⟨z, hz, hgz⟩ := Flat.generalizingMap g h₀
  rw [← hgz, hi z hz]

omit [IsLocalRing O] in

theorem range_subset_closure_singleton [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))]
    (i : fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) :
    Set.range ⇑(i ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base ⊆
      closure {(i ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))} := by
  rintro _ ⟨c, rfl⟩
  exact specializes_iff_mem_closure.mp ((genericPoint_specializes c).map (Scheme.Hom.continuous _))

include hϖ in

theorem specializes_g_of_specializes (w z : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (h : (bcMap (ΓM M H) hj ρO toκ htoκ).base w ⤳ (bcMap (ΓM M H) hj ρO toκ htoκ).base z) :
    (fibreMapOfComp (ΓM M H) hj ((IsLocalRing.residue O).comp ρO) ((IsLocalRing.residue ↥A).comp ρ) (ι hϖ toκ) (ι_comp ρO hϖ toκ htoκ)).base w ⤳
      (fibreMapOfComp (ΓM M H) hj ((IsLocalRing.residue O).comp ρO) ((IsLocalRing.residue ↥A).comp ρ) (ι hϖ toκ) (ι_comp ρO hϖ toκ htoκ)).base z := by
  haveI : IsClosedImmersion (bcMap (ΓM M H) hj ρO (IsLocalRing.residue O) rfl) := by
    rw [bcMap_eq_fibreMapOfComp]
    exact isClosedImmersion_fibreMapOfComp _ _ _ _ _ rfl Ideal.Quotient.mk_surjective
  rw [bcMap_eq_comp (ΓM M H) hj ρO hϖ toκ htoκ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h
  exact ((bcMap (ΓM M H) hj ρO (IsLocalRing.residue O) rfl).isClosedEmbedding.isInducing.specializes_iff).mp h

include hϖ in

theorem mem_range_of_specializes [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))]
    (a b : fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    [IsClosedImmersion a]
    (hcov : ∀ z : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)), z ∈ Set.range a.base ∨ z ∈ Set.range b.base)
    (ha : ∀ z, z ⤳ a.base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) → z = a.base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))))
    (hne : (a ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) ≠ (b ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))))
    (z : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (hz : (a ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) ⤳ (bcMap (ΓM M H) hj ρO toκ htoκ).base z) :
    z ∈ Set.range ⇑a.base := by
  set η := genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
  set g := fibreMapOfComp (ΓM M H) hj ((IsLocalRing.residue O).comp ρO) ((IsLocalRing.residue ↥A).comp ρ) (ι hϖ toκ) (ι_comp ρO hϖ toκ htoκ) with hg
  haveI : Flat g := flat_fibreMapOfComp _ _ _ _ _ _
  have hz' : g.base (a.base η) ⤳ g.base z := by
    refine specializes_g_of_specializes (A := A) (ρ := ρ) (ρO := ρO) (hϖ := hϖ) (toκ := toκ) (htoκ := htoκ) _ _ ?_
    rw [← Scheme.Hom.comp_apply]; exact hz
  obtain ⟨z₁, hz₁, hgz₁⟩ := Flat.generalizingMap g hz'
  rcases hcov z₁ with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact hz₁.mem_closed a.isClosedEmbedding.isClosed_range ⟨c, hc⟩
  · exfalso
    apply hne
    symm
    refine eq_of_specializes_aux (A := A) (ρ := ρ) (ρO := ρO) (hϖ := hϖ) (toκ := toκ) (htoκ := htoκ) a ha _
      (bcMap_apply_notMem (A := A) (ρ := ρ) (ρO := ρO) (toκ := toκ) (htoκ := htoκ) _) ?_
    have h1 : (b ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base η ⤳ (bcMap (ΓM M H) hj ρO toκ htoκ).base z₁ := by
      rw [← hc, Scheme.Hom.comp_apply]
      exact ((genericPoint_specializes c).map (Scheme.Hom.continuous b)).map (Scheme.Hom.continuous _)
    have h2 : (bcMap (ΓM M H) hj ρO toκ htoκ).base z₁ = (a ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base η := by
      rw [Scheme.Hom.comp_apply, bcMap_eq_comp (ΓM M H) hj ρO hϖ toκ htoκ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ← hg, hgz₁]
    rw [← h2]
    exact h1

include hϖ in

theorem range_eq_closure [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))]
    (a b : fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    [IsClosedImmersion a]
    (hcov : ∀ z : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)), z ∈ Set.range a.base ∨ z ∈ Set.range b.base)
    (ha : ∀ z, z ⤳ a.base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) → z = a.base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))))
    (hne : (a ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) ≠ (b ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))) :
    Set.range ⇑(a ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base = closure {(a ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))} := by
  apply le_antisymm (range_subset_closure_singleton (A := A) (ρ := ρ) (ρO := ρO) (toκ := toκ) (htoκ := htoκ) a)
  intro y hy
  have hspec : (a ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) ⤳ y := specializes_iff_mem_closure.mpr hy
  have hyV : y ∉ (XO.toBase (ΓM M H) hj ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) :=
    fun hyD => by
      have := hspec.mem_open (TopologicalSpace.Opens.isOpen _) hyD
      rw [Scheme.Hom.comp_apply] at this
      exact bcMap_apply_notMem (A := A) (ρ := ρ) (ρO := ρO) (toκ := toκ) (htoκ := htoκ) _ this
  obtain ⟨z, rfl⟩ := exists_bcMap_eq (A := A) (ρ := ρ) (ρO := ρO) (hϖ := hϖ) (toκ := toκ) (htoκ := htoκ) y hyV
  obtain ⟨c, rfl⟩ := mem_range_of_specializes (A := A) (ρ := ρ) (ρO := ρO) (hϖ := hϖ) (toκ := toκ) (htoκ := htoκ) a b hcov ha hne z hspec
  exact ⟨c, (Scheme.Hom.comp_apply _ _ _)⟩

end Main

end ECL_Range

end

open ECL_Range in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsLocalRing O] (ρO : R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* IsLocalRing.ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)
    (i : Fin 2) :
    letI := (𝔛.Mfib A hA ρ hρ).isIntegral
    Set.range ⇑(𝔛.comp A hA ρ hρ i ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base =
        closure {(𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base (genericPoint (𝔛.Mfib A hA ρ hρ).C)} ∧
      IsClosed (Set.range ⇑(𝔛.comp A hA ρ hρ i ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base) := by
  haveI := (𝔛.Mfib A hA ρ hρ).isIntegral
  haveI := ECL_FibN.isIntegral_fibreN 𝔛 A hA ρ hρ
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 0
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 1
  have hne0 := ModularCurve.XHDRModelAtP.xiInf_ne_xiZero p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ
  have hξ : ∀ i : Fin 2, (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base (genericPoint (𝔛.Mfib A hA ρ hρ).C) =
      (𝔛.comp A hA ρ hρ i ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) := by
    intro i
    rw [Scheme.Hom.comp_apply, ECL_FibN.efib_genericPoint_eq 𝔛 A hA ρ hρ]
  have hne : (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) ≠ (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) := by
    rw [← hξ 0, ← hξ 1]; exact hne0
  show Set.range _ = closure {(𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base _} ∧ _
  rw [hξ i]
  suffices h : Set.range ⇑(𝔛.comp A hA ρ hρ i ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base =
      closure {(𝔛.comp A hA ρ hρ i ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base (genericPoint ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))} from
    ⟨h, h ▸ isClosed_closure⟩
  fin_cases i
  · exact ECL_Range.range_eq_closure (A := A) (ρ := ρ) (ρO := ρO) (hϖ := hϖ) (toκ := toκ) (htoκ := htoκ) (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)
      (𝔛.comp_jointly_surjective A hA ρ hρ) (ECL_Range.eq_of_specializes_comp0_genericPoint 𝔛 A hA ρ hρ) hne
  · exact ECL_Range.range_eq_closure (A := A) (ρ := ρ) (ρO := ρO) (hϖ := hϖ) (toκ := toκ) (htoκ := htoκ) (𝔛.comp A hA ρ hρ 1) (𝔛.comp A hA ρ hρ 0)
      (fun z => (𝔛.comp_jointly_surjective A hA ρ hρ z).symm) (ECL_Range.eq_of_specializes_comp1_genericPoint 𝔛 A hA ρ hρ) hne.symm

end S_ModularCurve_XHDRModelAtP_range_comp_bcMap_eq_closure_and_isClosed
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_range_comp_bcMap_eq_closure_and_isClosed (solution)
