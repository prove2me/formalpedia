-- Prove2me | solution 1 for ModularCurve.genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/1fc5b203-5e7c-5578-90f0-fa3b07b8aee3

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_genusFF_qExpFunctionFieldC_eq_of_ringHom
import Theorems.Thm_ModularCurve_genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd
import Theorems.Thm_ModularCurve_finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one
import Theorems.Thm_ValuationSubring_krullDimLE_one_of_isAlgebraic_rat
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.HeckeData.V_isScalarTower"
p2m_attr_erase "instance" "CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "instance" "WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add"
p2m_attr_erase "simp" "ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP"
p2m_attr_erase "simp" "ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped MatrixGroups
p2m_open "IntermediateField AlgebraicCurve~genus ModularCurve P2MW.S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd.ModularCurve IsLocalRing"

namespace ModularCurve
p2m_export "ModularCurve" "translation_mem_GammaH Gamma1_le_GammaH xHFunctionFieldC xHFunctionFieldBar qExpFunctionFieldC intFormRatiosC_subset coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC map_jqModC exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC genusFF_qExpFunctionFieldC_eq_of_ringHom genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField jqModC_mem_intFormRatiosC transcendental_jqModC"
namespace IgusaGenusXH
p2m_open "ModularCurve"

local notation "ℚ̄" => AlgebraicClosure ℚ

section Residue

variable {ℓ : ℕ} [Fact ℓ.Prime] (A : ValuationSubring ℚ̄)

theorem charP_residueField (hA : A.LiesOverPrime ℓ) : CharP (ResidueField A) ℓ := by
  have hmem : ((ℓ : A) : ℚ̄) ∈ A.nonunits := by
    have : ((ℓ : A) : ℚ̄) = (ℓ : ℚ̄) := by simp
    rw [this]; exact hA
  have hmax : (ℓ : A) ∈ maximalIdeal A := (ValuationSubring.coe_mem_nonunits_iff).mp hmem
  have h0 : (ℓ : ResidueField A) = 0 := by
    rw [← map_natCast (residue A), residue_eq_zero_iff]
    exact hmax
  exact (CharP.charP_iff_prime_eq_zero Fact.out).mpr h0

theorem isAlgebraic_residueField [CharP (ResidueField A) ℓ] :
    letI : Algebra (ZMod ℓ) (ResidueField A) := ZMod.algebra _ ℓ
    Algebra.IsAlgebraic (ZMod ℓ) (ResidueField A) := by
  letI : Algebra (ZMod ℓ) (ResidueField A) := ZMod.algebra _ ℓ
  refine ⟨fun z => ?_⟩
  obtain ⟨x, rfl⟩ := residue_surjective z

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
  have halgQ : IsAlgebraic ℚ (x : ℚ̄) := Algebra.IsAlgebraic.isAlgebraic _
  have halgZ : IsAlgebraic ℤ (x : ℚ̄) := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℚ̄).mpr halgQ
  obtain ⟨P, hP0, hPx⟩ := halgZ

  set Q : Polynomial ℤ := P.primPart with hQ
  have hQprim : Q.IsPrimitive := P.isPrimitive_primPart
  have hcont : (P.content : ℚ̄) ≠ 0 := by
    have : P.content ≠ 0 := fun h => hP0 (Polynomial.content_eq_zero_iff.mp h)
    exact_mod_cast this
  have hQx : Polynomial.aeval (x : ℚ̄) Q = 0 := by
    have h1 : Polynomial.aeval (x : ℚ̄) P =
        (P.content : ℚ̄) * Polynomial.aeval (x : ℚ̄) Q := by
      conv_lhs => rw [P.eq_C_content_mul_primPart]
      rw [map_mul, Polynomial.aeval_C]
      congr 1
    rw [hPx] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hcont

  have hQxA : Polynomial.eval₂ (Int.castRingHom A) x Q = 0 := by
    apply Subtype.val_injective
    change A.subtype (Polynomial.eval₂ (Int.castRingHom A) x Q) = ((0 : A) : ℚ̄)
    rw [Polynomial.hom_eval₂, ZeroMemClass.coe_zero]
    have : (A.subtype).comp (Int.castRingHom A) = algebraMap ℤ ℚ̄ := RingHom.ext_int _ _
    rw [this]
    exact hQx

  have hQbar : Polynomial.aeval (residue A x) (Q.map (Int.castRingHom (ZMod ℓ))) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have : (algebraMap (ZMod ℓ) (ResidueField A)).comp (Int.castRingHom (ZMod ℓ)) =
        (residue A).comp (Int.castRingHom A) := RingHom.ext_int _ _
    rw [this, ← Polynomial.hom_eval₂, hQxA, map_zero]

  have hQbar0 : Q.map (Int.castRingHom (ZMod ℓ)) ≠ 0 := by
    intro h0
    have hdvd : ∀ n, (ℓ : ℤ) ∣ Q.coeff n := by
      intro n
      have h1 : (Q.map (Int.castRingHom (ZMod ℓ))).coeff n = 0 := by rw [h0, Polynomial.coeff_zero]
      rw [Polynomial.coeff_map, Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
      exact h1
    have hC : Polynomial.C (ℓ : ℤ) ∣ Q := (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hdvd
    have hunit : IsUnit (ℓ : ℤ) := hQprim _ hC
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hunit
    exact (Fact.out : ℓ.Prime).one_lt.ne' hunit
  exact ⟨_, hQbar0, hQbar⟩

theorem exists_ringHom_residueField [CharP (ResidueField A) ℓ]
    (k : Type*) [Field k] [IsAlgClosed k] [CharP k ℓ] :
    Nonempty (ResidueField A →+* k) := by
  letI : Algebra (ZMod ℓ) (ResidueField A) := ZMod.algebra _ ℓ
  letI : Algebra (ZMod ℓ) k := ZMod.algebra _ ℓ
  haveI : Algebra.IsAlgebraic (ZMod ℓ) (ResidueField A) := isAlgebraic_residueField A
  exact ⟨(IsAlgClosed.lift (R := ZMod ℓ) (S := ResidueField A) (M := k)).toRingHom⟩

end Residue

section DeuringLE

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime]

local notation "Γ" => CohCarrier.GammaH M H
local notation "FF" => laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)

scoped instance finiteIndex_gammaH : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

theorem coeffMap_jqModC_mem (A : ValuationSubring ℚ̄) :
    coeffMap A.subtype (jqModC A) ∈ FF := by
  have h1 : coeffMap A.subtype (jqModC A) = coeffEmb ℚ̄ (jqModC ℚ) := by
    change (jqModC A).map A.subtype = (jqModC ℚ).map (algebraMap ℚ ℚ̄)
    rw [map_jqModC, map_jqModC]
  rw [h1]
  exact coeffEmb_mem_laurentBaseChange ℚ̄
    (intFormRatiosC_subset ℚ Γ (jqModC_mem_intFormRatiosC ℚ Γ))

set_option maxHeartbeats 3200000 in

theorem genusFF_residueField_le (hℓM : ¬ ℓ ∣ M) (A : ValuationSubring ℚ̄) (hA : A.LiesOverPrime ℓ) :
    genusFF (ResidueField A) (qExpFunctionFieldC (ResidueField A) Γ) ≤
      genusFF ℚ̄ FF := by
  have hT : ModularGroup.T ∈ Γ := translation_mem_GammaH M H

  obtain ⟨R, -, hRres⟩ :=
    exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC ℚ̄ A Γ hT

  have hjF : coeffMap A.subtype (jqModC A) ∈ FF := coeffMap_jqModC_mem M H A
  set y : FF := ⟨coeffMap A.subtype (jqModC A), hjF⟩ with hydef
  have hycoe : (y : LaurentSeries ℚ̄) = jqModC ℚ̄ := by
    change (jqModC A).map A.subtype = jqModC ℚ̄
    exact map_jqModC _
  obtain ⟨hO, hres⟩ := hRres (jqModC A) hjF
  set xb : qExpFunctionFieldC (ResidueField A) Γ := R.residue ⟨y, hO⟩ with hxbdef
  have hxbcoe : (xb : LaurentSeries (ResidueField A)) = jqModC (ResidueField A) := by
    rw [hxbdef, hres]
    exact map_jqModC _

  have htrL : Transcendental ℚ̄ y := by
    have h := transcendental_jqModC ℚ̄
    rw [← hycoe] at h
    exact (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective FF (LaurentSeries ℚ̄))).mp h
  have htr : Transcendental (ResidueField A) xb := by
    have h := transcendental_jqModC (ResidueField A)
    rw [← hxbcoe] at h
    exact (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (qExpFunctionFieldC (ResidueField A) Γ)
        (LaurentSeries (ResidueField A)))).mp h

  obtain ⟨x₁, hx₁, -, hfin₁, hle₁⟩ :=
    exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField ℚ̄ A Γ hT
  have hx₁xb : x₁ = xb := Subtype.ext (hx₁.trans hxbcoe.symm)
  subst hx₁xb
  have hle : Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({xb} : Set (qExpFunctionFieldC (ResidueField A) Γ))) (qExpFunctionFieldC (ResidueField A) Γ) ≤
      Module.finrank (IntermediateField.adjoin ℚ̄ ({y} : Set FF)) FF := hle₁ y hycoe

  have hge : Module.finrank (IntermediateField.adjoin ℚ̄ ({y} : Set FF)) FF ≤
      Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({xb} : Set (qExpFunctionFieldC (ResidueField A) Γ))) (qExpFunctionFieldC (ResidueField A) Γ) :=
    finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd M H hℓM A hA xb y hxbcoe hycoe
  have heq := le_antisymm hle hge

  haveI := hfin₁
  have hpos : 0 < Module.finrank (IntermediateField.adjoin (ResidueField A)
      ({xb} : Set (qExpFunctionFieldC (ResidueField A) Γ))) (qExpFunctionFieldC (ResidueField A) Γ) :=
    Module.finrank_pos
  have hfd : FiniteDimensional (IntermediateField.adjoin ℚ̄ ({y} : Set FF)) FF :=
    Module.finite_of_finrank_pos (by omega)

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
  haveI : Ring.KrullDimLE 1 A := ValuationSubring.krullDimLE_one_of_isAlgebraic_rat A

  have key := RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one
    (L := ℚ̄) A (F := FF) (ι := Unit) (fun _ => qExpFunctionFieldC (ResidueField A) Γ)
    (fun _ => R) (fun _ _ _ => Subsingleton.elim _ _) (y : FF) (fun _ => hO) htrL hfd
    (fun _ => htr) (by rw [Fintype.sum_unique]; exact heq)
  rwa [Fintype.sum_unique] at key

end DeuringLE

section Main

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime]

set_option maxHeartbeats 3200000 in
theorem main (hℓM : ¬ ℓ ∣ M) (k : Type*) [Field k] [IsAlgClosed k] [CharP k ℓ] :
    genusFF k (xHFunctionFieldC k M H) = genusFF ℚ̄ (xHFunctionFieldBar M H) := by

  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨ℓ, Fact.out⟩
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : CharP (ResidueField A) ℓ := charP_residueField A hA
  obtain ⟨φ⟩ := exists_ringHom_residueField A k
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := translation_mem_GammaH M H

  have hfg : ∃ x : qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH M H),
      Transcendental (ResidueField A) x ∧
      FiniteDimensional (IntermediateField.adjoin (ResidueField A)
        ({x} : Set (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH M H))))
        (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH M H)) := by
    obtain ⟨x, -, htr, hfin, -⟩ :=
      exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField ℚ̄ A
        (CohCarrier.GammaH M H) hT
    exact ⟨x, htr, hfin⟩

  have htrans : genusFF k (qExpFunctionFieldC k (CohCarrier.GammaH M H)) =
      genusFF (ResidueField A) (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH M H)) :=
    genusFF_qExpFunctionFieldC_eq_of_ringHom φ (CohCarrier.GammaH M H) hfg

  have hle := genusFF_residueField_le M H hℓM A hA

  have hge : genusFF ℚ̄ (xHFunctionFieldBar M H) ≤
      genusFF k (qExpFunctionFieldC k (CohCarrier.GammaH M H)) :=
    genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd M H hℓM k
  change genusFF k (qExpFunctionFieldC k (CohCarrier.GammaH M H)) =
    genusFF ℚ̄ (laurentBaseChange ℚ̄ (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
  change genusFF ℚ̄ (laurentBaseChange ℚ̄ (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ≤ _ at hge
  exact le_antisymm (htrans.le.trans hle) hge

end Main

end ModularCurve.IgusaGenusXH
p2m_reactivate "P2MW.S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd.ModularCurve P2MW.S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd.ModularCurve.IgusaGenusXH"
p2m_reactivate "P2MW.S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd.ModularCurve P2MW.S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd.ModularCurve.IgusaGenusXH"

p2m_open "AlgebraicCurve~genus" in open  _root_.ModularCurve _root_.P2MW.S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd.ModularCurve in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (k : Type*) [Field k] [IsAlgClosed k] [CharP k ℓ] :
    genusFF k (ModularCurve.xHFunctionFieldC k M H) =
      genusFF (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) :=
  ModularCurve.IgusaGenusXH.main M H hℓM k

end S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd (solution)
