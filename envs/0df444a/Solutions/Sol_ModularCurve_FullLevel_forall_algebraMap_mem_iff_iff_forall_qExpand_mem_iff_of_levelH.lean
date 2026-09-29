-- Prove2me | solution 1 for ModularCurve.FullLevel.forall_algebraMap_mem_iff_iff_forall_qExpand_mem_iff_of_levelH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/4bf9495e-7f20-5820-8118-fade9502c7f1

import Theorems.Thm_ModularCurve_valuationSubring_unique_laurentBaseChange_gamma0_of_not_dvd
import Theorems.Thm_ModularCurve_forall_aeval_mem_iff_forall_aeval_qExpand_mem_of_valuationSubring
import Theorems.Thm_ModularCurve_FullLevel_qExpand_mem_laurentBaseChange_xHFunctionField_levelH_of_mem_gamma0
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_forall_algebraMap_mem_iff_iff_forall_qExpand_mem_iff_of_levelH
p2m_attr_erase "instance" "GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms"
p2m_attr_erase "instance" "ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero"
p2m_attr_erase "simp" "TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply"
p2m_attr_erase "simp" "CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq"
p2m_attr_erase "simp" "ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

open scoped MatrixGroups

namespace FloorSwapAux

theorem unit_iff {F : Type} [Field F] (W : ValuationSubring F) (x : F) (hx : x ∈ W) :
    IsUnit (⟨x, hx⟩ : ↥W) ↔ x ≠ 0 ∧ x⁻¹ ∈ W := by
  constructor
  · intro hu
    obtain ⟨c, hc⟩ := hu.exists_right_inv
    have h3 : x * (c : F) = 1 := by
      have := congrArg (fun z : ↥W => (z : F)) hc
      simpa using this
    refine ⟨fun h0 => by simp [h0] at h3, ?_⟩
    rw [← eq_inv_of_mul_eq_one_right h3]; exact c.2
  · rintro ⟨hx0, hinv⟩
    exact isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

theorem mem_nonunits_iff' {F : Type} [Field F] (W : ValuationSubring F) (x : F) :
    x ∈ W.nonunits ↔ x ∈ W ∧ (x ≠ 0 → x⁻¹ ∉ W) := by
  constructor
  · intro h
    have hx : x ∈ W := W.nonunits_subset h
    refine ⟨hx, fun hx0 hinv => ?_⟩
    have hm : (⟨x, hx⟩ : ↥W) ∈ maximalIdeal ↥W := (W.coe_mem_nonunits_iff).mp h
    exact (IsLocalRing.mem_maximalIdeal _).mp hm ((unit_iff W x hx).mpr ⟨hx0, hinv⟩)
  · rintro ⟨hx, h⟩
    have : (⟨x, hx⟩ : ↥W) ∈ maximalIdeal ↥W := by
      rw [IsLocalRing.mem_maximalIdeal]
      intro hu
      obtain ⟨hx0, hinv⟩ := (unit_iff W x hx).mp hu
      exact h hx0 hinv
    exact (W.coe_mem_nonunits_iff).mpr this

theorem comap_mem_nonunits_iff {F F' : Type} [Field F] [Field F'] (φ : F →+* F') (W : ValuationSubring F') (x : F) :
    x ∈ (W.comap φ).nonunits ↔ φ x ∈ W.nonunits := by
  rw [mem_nonunits_iff', mem_nonunits_iff', ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀,
    map_ne_zero_iff φ φ.injective]

end FloorSwapAux

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (hle : K₀ ≤ K)

    (hsharp : ∀ x : LaurentSeries L,
      x ∈ ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) →
        ModularCurve.qExpand L q x ∈ K)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))

    (O₀ : ValuationSubring ↥K₀)
    (hO₀ : ∀ f : ↥K₀, f ∈ O₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (B : ValuationSubring ↥K) :
    letI : Algebra ↥K₀ ↥K := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    (∀ x : ↥K₀, algebraMap ↥K₀ ↥K x ∈ B ↔ x ∈ O₀) ↔
      ∀ (w : ↥K),
        (∃ x : LaurentSeries L,
            x ∈ ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) ∧
              ((w : ↥K) : LaurentSeries L) = ModularCurve.qExpand L q x) →
        (w ∈ B ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
          (w : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
            = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) := by
  classical
  letI algK : Algebra ↥K₀ ↥K := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have algK_coe : ∀ x : ↥K₀, ((algebraMap ↥K₀ ↥K x : ↥K) : LaurentSeries L) = (x : LaurentSeries L) := fun x => rfl

  letI algAK₀ : Algebra A ↥K₀ := ((algebraMap L ↥K₀).comp (algebraMap A L)).toAlgebra
  haveI istK₀ : IsScalarTower A L ↥K₀ := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  letI algAK : Algebra A ↥K := ((algebraMap L ↥K).comp (algebraMap A L)).toAlgebra
  haveI istK : IsScalarTower A L ↥K := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  have algAK₀_apply : ∀ a : A, algebraMap A ↥K₀ a = algebraMap L ↥K₀ (algebraMap A L a) := fun a => rfl
  have algAK_apply : ∀ a : A, algebraMap A ↥K a = algebraMap L ↥K (algebraMap A L a) := fun a => rfl

  have hjq : ModularCurve.jq ∈ ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M') := by
    have h := ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ M'
    rw [ModularCurve.modularFunctionFieldFullC_rat] at h
    exact h (ModularCurve.jq_mem_full M')
  have hj₀mem : ModularCurve.coeffEmb L ModularCurve.jq ∈ K₀ := by
    rw [hK₀]; exact ModularCurve.coeffEmb_mem_laurentBaseChange L hjq
  set j₀ : ↥K₀ := ⟨ModularCurve.coeffEmb L ModularCurve.jq, hj₀mem⟩ with hj₀def
  have hj₀ : ((j₀ : ↥K₀) : LaurentSeries L) = ModularCurve.coeffEmb L ModularCurve.jq := rfl
  set jK : ↥K := algebraMap ↥K₀ ↥K j₀ with hjKdef
  have hjK : ((jK : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L ModularCurve.jq := rfl
  have hjq0 : ModularCurve.coeffEmb L ModularCurve.jq ≠ 0 := by
    intro h; exact ModularCurve.jq_ne_zero ((ModularCurve.coeffEmb L).injective (by rw [h, map_zero]))
  haveI : Fact (j₀ ≠ 0) := ⟨fun h => hjq0 (by rw [← hj₀, h]; rfl)⟩
  haveI : Fact (jK ≠ 0) := ⟨fun h => hjq0 (by rw [← hjK, h]; rfl)⟩

  have hθmem : ∀ x : ↥K₀, ModularCurve.qExpand L q (x : LaurentSeries L) ∈ K := fun x => hsharp x (hK₀ ▸ x.2)
  have hcoeC : ∀ c : L, ((algebraMap L ↥K₀ c : ↥K₀) : LaurentSeries L) = HahnSeries.C c := by
    intro c
    show HahnSeries.ofPowerSeries ℤ L (PowerSeries.C c) = HahnSeries.C c
    exact HahnSeries.ofPowerSeries_C c
  have hcoeCK : ∀ c : L, ((algebraMap L ↥K c : ↥K) : LaurentSeries L) = HahnSeries.C c := by
    intro c
    show HahnSeries.ofPowerSeries ℤ L (PowerSeries.C c) = HahnSeries.C c
    exact HahnSeries.ofPowerSeries_C c
  let θ : ↥K₀ →ₐ[L] ↥K :=
    { toFun := fun x => ⟨ModularCurve.qExpand L q (x : LaurentSeries L), hθmem x⟩
      map_one' := Subtype.ext (by show ModularCurve.qExpand L q ((1 : ↥K₀) : LaurentSeries L) = 1; simp)
      map_mul' := fun a b => Subtype.ext (by
        show ModularCurve.qExpand L q ((a * b : ↥K₀) : LaurentSeries L) = _ ; simp)
      map_zero' := Subtype.ext (by show ModularCurve.qExpand L q ((0 : ↥K₀) : LaurentSeries L) = 0; simp)
      map_add' := fun a b => Subtype.ext (by
        show ModularCurve.qExpand L q ((a + b : ↥K₀) : LaurentSeries L) = _ ; simp)
      commutes' := fun c => Subtype.ext (by
        show ModularCurve.qExpand L q ((algebraMap L ↥K₀ c : ↥K₀) : LaurentSeries L) = ((algebraMap L ↥K c : ↥K) : LaurentSeries L)
        rw [hcoeC, hcoeCK, ModularCurve.qExpand_C]) }
  have hθcoe : ∀ x : ↥K₀, ((θ x : ↥K) : LaurentSeries L) = ModularCurve.qExpand L q (x : LaurentSeries L) := fun x => rfl
  have hθimg : ∀ x : ↥K₀, ∃ x' : LaurentSeries L,
      x' ∈ ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) ∧
        ((θ x : ↥K) : LaurentSeries L) = ModularCurve.qExpand L q x' :=
    fun x => ⟨x, hK₀ ▸ x.2, rfl⟩
  set j' : ↥K := θ j₀ with hj'def
  have hj' : ((j' : ↥K) : LaurentSeries L) = ModularCurve.qExpand L q ((jK : ↥K) : LaurentSeries L) := rfl

  obtain ⟨G₀, hG₀mem, hG₀A, hG₀m, hG₀P, -⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC (CongruenceSubgroup.Gamma0 M') L K₀ hK₀ A j₀ hj₀
  have hG₀eq : G₀ = O₀ := by ext f; rw [hG₀mem f, hO₀ f]
  obtain ⟨GK, hGKmem, hGKA, hGKm, hGKP, -⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
      (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) L K hK A jK hjK
  have hGKeq : GK = W₀ := by ext f; rw [hGKmem f, hW₀ f]
  subst hG₀eq hGKeq

  have hPO : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j₀ (P.map (algebraMap A L)) ∈ G₀ ∧ (Polynomial.aeval j₀ (P.map (algebraMap A L)))⁻¹ ∈ G₀ := by
    intro P hP; rw [Polynomial.aeval_map_algebraMap]; exact hG₀P P hP
  have hPW : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval jK (P.map (algebraMap A L)) ∈ GK ∧ (Polynomial.aeval jK (P.map (algebraMap A L)))⁻¹ ∈ GK := by
    intro P hP; rw [Polynomial.aeval_map_algebraMap]; exact hGKP P hP
  have hAW : ∀ a : A, algebraMap L ↥K (algebraMap A L a) ∈ GK := fun a => hGKA a
  have hmW : ∀ a ∈ maximalIdeal A, algebraMap L ↥K (algebraMap A L a) ∈ GK.nonunits := fun a ha => hGKm a ha

  have hPW' := (ModularCurve.forall_aeval_mem_iff_forall_aeval_qExpand_mem_of_valuationSubring q L K A hAq jK hjK j' hj' GK
    hAW hmW).mp hPW

  have haeθ : ∀ P : Polynomial L, Polynomial.aeval j' P = θ (Polynomial.aeval j₀ P) := fun P =>
    (Polynomial.aeval_algHom_apply θ j₀ P)
  have haeι : ∀ P : Polynomial L, Polynomial.aeval jK P = algebraMap ↥K₀ ↥K (Polynomial.aeval j₀ P) := fun P =>
    (Polynomial.aeval_algHom_apply (IntermediateField.inclusion hle) j₀ P)
  constructor
  ·
    intro hB w ⟨x, hx, hw⟩
    have hxK₀ : x ∈ K₀ := by rw [hK₀]; exact hx
    set x₀ : ↥K₀ := ⟨x, hxK₀⟩ with hx₀def
    have hwθ : w = θ x₀ := Subtype.ext hw
    rw [hwθ, ← hGKmem]

    have hBeq : B.comap θ.toRingHom = GK.comap θ.toRingHom := by

      have hBA : ∀ a : A, algebraMap L ↥K (algebraMap A L a) ∈ B := by
        intro a
        have := (hB (algebraMap L ↥K₀ (algebraMap A L a))).mpr (hG₀A a)
        rwa [show algebraMap ↥K₀ ↥K (algebraMap L ↥K₀ (algebraMap A L a)) = algebraMap L ↥K (algebraMap A L a) from
          (IntermediateField.inclusion hle).commutes _] at this
      have hBcomapι : B.comap (algebraMap ↥K₀ ↥K) = G₀ := by ext x; rw [ValuationSubring.mem_comap]; exact hB x
      have hBm : ∀ a ∈ maximalIdeal A, algebraMap L ↥K (algebraMap A L a) ∈ B.nonunits := by
        intro a ha
        have h1 : algebraMap L ↥K₀ (algebraMap A L a) ∈ (B.comap (algebraMap ↥K₀ ↥K)).nonunits := by
          rw [hBcomapι]; exact hG₀m a ha
        rw [FloorSwapAux.comap_mem_nonunits_iff] at h1
        rwa [show algebraMap ↥K₀ ↥K (algebraMap L ↥K₀ (algebraMap A L a)) = algebraMap L ↥K (algebraMap A L a) from
          (IntermediateField.inclusion hle).commutes _] at h1
      have hPB : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
          Polynomial.aeval jK (P.map (algebraMap A L)) ∈ B ∧ (Polynomial.aeval jK (P.map (algebraMap A L)))⁻¹ ∈ B := by
        intro P hP
        obtain ⟨h1, h2⟩ := hPO P hP
        rw [haeι, ← map_inv₀]
        exact ⟨(hB _).mpr h1, (hB _).mpr h2⟩
      have hPB' := (ModularCurve.forall_aeval_mem_iff_forall_aeval_qExpand_mem_of_valuationSubring q L K A hAq jK hjK j' hj' B
        hBA hBm).mp hPB

      have BR : ∀ V : ValuationSubring ↥K, (∀ a : A, algebraMap L ↥K (algebraMap A L a) ∈ V) →
          (∀ a ∈ maximalIdeal A, algebraMap L ↥K (algebraMap A L a) ∈ V.nonunits) →
          (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
            Polynomial.aeval j' (P.map (algebraMap A L)) ∈ V ∧ (Polynomial.aeval j' (P.map (algebraMap A L)))⁻¹ ∈ V) →
          ((∀ a : A, algebraMap L ↥K₀ (algebraMap A L a) ∈ V.comap θ.toRingHom) ∧
           (∀ a ∈ maximalIdeal A, algebraMap L ↥K₀ (algebraMap A L a) ∈ (V.comap θ.toRingHom).nonunits) ∧
           (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
             Polynomial.aeval j₀ (P.map (algebraMap A L)) ∈ V.comap θ.toRingHom ∧
               (Polynomial.aeval j₀ (P.map (algebraMap A L)))⁻¹ ∈ V.comap θ.toRingHom)) := by
        intro V hVA hVm hVP
        refine ⟨fun a => ?_, fun a ha => ?_, fun P hP => ?_⟩
        · rw [ValuationSubring.mem_comap]
          show θ (algebraMap L ↥K₀ (algebraMap A L a)) ∈ V
          rw [θ.commutes]; exact hVA a
        · rw [FloorSwapAux.comap_mem_nonunits_iff]
          show θ (algebraMap L ↥K₀ (algebraMap A L a)) ∈ V.nonunits
          rw [θ.commutes]; exact hVm a ha
        · obtain ⟨h1, h2⟩ := hVP P hP
          rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap]
          show θ (Polynomial.aeval j₀ (P.map (algebraMap A L))) ∈ V ∧ θ (Polynomial.aeval j₀ (P.map (algebraMap A L)))⁻¹ ∈ V
          rw [map_inv₀, ← haeθ]; exact ⟨h1, h2⟩
      exact ModularCurve.valuationSubring_unique_laurentBaseChange_gamma0_of_not_dvd q M' hqM' L K₀ hK₀ A hAq j₀ hj₀
        (B.comap θ.toRingHom) (GK.comap θ.toRingHom) (BR B hBA hBm hPB') (BR GK hAW hmW hPW')
    have := congrArg (fun V : ValuationSubring ↥K₀ => x₀ ∈ V) hBeq
    simp only [ValuationSubring.mem_comap] at this
    exact Iff.of_eq this
  ·
    intro hR

    have hRθ : ∀ x : ↥K₀, θ x ∈ B ↔ θ x ∈ GK := by
      intro x; rw [hGKmem]; exact hR (θ x) (hθimg x)
    have hBA : ∀ a : A, algebraMap L ↥K (algebraMap A L a) ∈ B := by
      intro a; rw [← θ.commutes]; exact (hRθ _).mpr (by rw [θ.commutes]; exact hAW a)
    have hBm : ∀ a ∈ maximalIdeal A, algebraMap L ↥K (algebraMap A L a) ∈ B.nonunits := by
      intro a ha
      rw [FloorSwapAux.mem_nonunits_iff']
      refine ⟨hBA a, fun h0 hinv => ?_⟩
      have hW := (FloorSwapAux.mem_nonunits_iff' GK _).mp (hmW a ha)
      apply hW.2 h0
      have : (algebraMap L ↥K (algebraMap A L a))⁻¹ = θ ((algebraMap L ↥K₀ (algebraMap A L a))⁻¹) := by
        rw [map_inv₀, θ.commutes]
      rw [this] at hinv ⊢
      exact (hRθ _).mp hinv
    have hPB' : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j' (P.map (algebraMap A L)) ∈ B ∧ (Polynomial.aeval j' (P.map (algebraMap A L)))⁻¹ ∈ B := by
      intro P hP
      obtain ⟨h1, h2⟩ := hPW' P hP
      rw [haeθ] at h1 h2 ⊢
      rw [← map_inv₀] at h2 ⊢
      exact ⟨(hRθ _).mpr h1, (hRθ _).mpr h2⟩
    have hPB := (ModularCurve.forall_aeval_mem_iff_forall_aeval_qExpand_mem_of_valuationSubring q L K A hAq jK hjK j' hj' B
      hBA hBm).mpr hPB'

    have hBeq : B.comap (algebraMap ↥K₀ ↥K) = G₀ := by
      refine ModularCurve.valuationSubring_unique_laurentBaseChange_gamma0_of_not_dvd q M' hqM' L K₀ hK₀ A hAq j₀ hj₀
        (B.comap (algebraMap ↥K₀ ↥K)) G₀ ⟨fun a => ?_, fun a ha => ?_, fun P hP => ?_⟩ ⟨fun a => hG₀A a, hG₀m, hPO⟩
      · rw [ValuationSubring.mem_comap,
          show algebraMap ↥K₀ ↥K (algebraMap L ↥K₀ (algebraMap A L a)) = algebraMap L ↥K (algebraMap A L a) from
            (IntermediateField.inclusion hle).commutes _]
        exact hBA a
      · rw [FloorSwapAux.comap_mem_nonunits_iff,
          show algebraMap ↥K₀ ↥K (algebraMap L ↥K₀ (algebraMap A L a)) = algebraMap L ↥K (algebraMap A L a) from
            (IntermediateField.inclusion hle).commutes _]
        exact hBm a ha
      · obtain ⟨h1, h2⟩ := hPB P hP
        rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀, ← haeι]
        exact ⟨h1, h2⟩
    intro x
    have := congrArg (fun V : ValuationSubring ↥K₀ => x ∈ V) hBeq
    simp only [ValuationSubring.mem_comap] at this
    exact Iff.of_eq this

end S_ModularCurve_FullLevel_forall_algebraMap_mem_iff_iff_forall_qExpand_mem_iff_of_levelH
end P2MW
export P2MW.S_ModularCurve_FullLevel_forall_algebraMap_mem_iff_iff_forall_qExpand_mem_iff_of_levelH (solution)
