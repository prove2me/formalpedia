-- Prove2me | solution 1 for ModularCurve.eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/a7a71525-98d8-5c4d-b610-c569eb747ff4

import Mathlib
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_ModularCurve_XH
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_exists_constantReduction_pic0Map_eq_reductionQExpModL
import Theorems.Thm_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd
import Theorems.Thm_ModularCurve_exists_transcendental_finrank_adjoin_eq_xHFunctionFieldC_of_not_dvd
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one
import Theorems.Thm_ValuationSubring_krullDimLE_one_of_isAlgebraic_rat
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ValuationSubring_charP_residueField_of_liesOverPrime
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂"
p2m_attr_erase "simp" "PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec"
p2m_attr_erase "simp" "CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "ReductionInputsQExpModL reductionQExpModL qExpFunctionFieldC laurentBaseChange translation_mem_GammaH Gamma1_le_GammaH JH exists_constantReduction_pic0Map_eq_reductionQExpModL genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd exists_transcendental_finrank_adjoin_eq_xHFunctionFieldC_of_not_dvd JOneES.exists_transcendental_finiteDimensional_laurentBaseChange"
namespace GammaHTorsionInjective
p2m_open "ModularCurve"

p2m_open "AlgebraicCurve~genus ModularCurve P2MW.S_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero.ModularCurve IsLocalRing"

section Kummer

theorem natCast_ne_zero_of_dvd {k : Type*} [NonAssocSemiring k] {m q : ℕ}
    (hm : (m : k) ≠ 0) (hq : q ∣ m) : (q : k) ≠ 0 := by
  obtain ⟨c, rfl⟩ := hq
  intro h
  apply hm
  rw [Nat.cast_mul, h, zero_mul]

theorem ne_zero_of_natCast_ne_zero {k : Type*} [NonAssocSemiring k] {m : ℕ}
    (hm : (m : k) ≠ 0) : m ≠ 0 := by
  rintro rfl
  exact hm Nat.cast_zero

theorem eq_zero_of_forall_prime {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (φ : G →+ H) (m : ℕ) (hm : m ≠ 0)
    (h : ∀ q : ℕ, q.Prime → q ∣ m → ∀ x : G, q • x = 0 → φ x = 0 → x = 0)
    (x : G) (hmx : m • x = 0) (hx : φ x = 0) : x = 0 := by
  induction m using Nat.strong_induction_on generalizing x with
  | _ m ih =>
    rcases eq_or_ne m 1 with rfl | hm1
    · simpa using hmx
    obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm1
    obtain ⟨m', rfl⟩ := hqm
    have hm' : m' ≠ 0 := by rintro rfl; simp at hm
    have hy : m' • x = 0 := by
      refine h q hq (dvd_mul_right q m') (m' • x) ?_ ?_
      · rw [smul_smul]; exact hmx
      · rw [map_nsmul, hx, nsmul_zero]
    have hlt : m' < q * m' := lt_mul_left (Nat.pos_of_ne_zero hm') hq.one_lt
    exact ih m' hlt hm' (fun q' hq' hq'm => h q' hq' (Dvd.dvd.mul_left hq'm q)) x hy hx

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem nsmul_divisor_apply (m : ℕ) (D : Divisor L F) (P : Place L F) :
    (m • D) P = (m : ℤ) * D P := by
  simp [Finsupp.smul_apply]

theorem smul_const_ne_zero (R : ConstantReduction A F Fbar) {f : F} {c : L}
    (hc : c • f ∈ R.integers) (hres : R.residue ⟨c • f, hc⟩ ≠ 0) : c ≠ 0 := by
  rintro rfl
  apply hres
  have : (⟨(0 : L) • f, hc⟩ : R.integers) = 0 := Subtype.ext (by simp)
  rw [this, map_zero]

theorem mk_eq_zero_of_mem_principal (D : Divisor.degZero (K := L) (F := F))
    (hD : (D : Divisor L F) ∈ Divisor.principal (K := L) (F := F)) : Pic0.mk D = 0 := by
  refine (QuotientAddGroup.eq_zero_iff D).mpr ?_
  rwa [AddSubgroup.mem_addSubgroupOf]

theorem exists_kummerDatum (R : ConstantReduction A F Fbar) (z : Pic0 L F) (m : ℕ)
    (hmz : m • z = 0) (hz : R.pic0Map z = 0) :
    ∃ D : Divisor.degZero (K := L) (F := F), Pic0.mk D = z ∧
      ∃ f : R.integers, R.residue f ≠ 0 ∧ (∀ P, (m : ℤ) * (D : Divisor L F) P = P.ord (f : F)) ∧
      ∃ g : Fbar, g ≠ 0 ∧ (∀ Q : Place (ResidueField A) Fbar,
        Finsupp.mapDomain R.placeMap (D : Divisor L F) Q = Q.ord g) ∧
      ∀ Q : Place (ResidueField A) Fbar, Q.ord (R.residue f) = (m : ℤ) * Q.ord g := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective z
  have hmD : ((m • D : Divisor.degZero (K := L) (F := F)) : Divisor L F) ∈
      Divisor.principal (K := L) (F := F) := by
    have h1 : Pic0.mk (m • D) = 0 := by
      change QuotientAddGroup.mk (m • D) = (0 : Pic0 L F)
      rw [QuotientAddGroup.mk_nsmul]
      exact hmz
    have h2 := (QuotientAddGroup.eq_zero_iff (m • D)).mp h1
    rwa [AddSubgroup.mem_addSubgroupOf] at h2
  obtain ⟨f₀, hf₀, hDf₀⟩ := hmD
  obtain ⟨c, hc, hres⟩ := R.exists_smul_mem f₀ hf₀
  have hc0 : c ≠ 0 := smul_const_ne_zero R hc hres
  have hdivf : ∀ P, (m : ℤ) * (D : Divisor L F) P = P.ord (c • f₀) := fun P => by
    rw [ConstantReduction.ord_smul P hc0, ← hDf₀ P, AddSubgroupClass.coe_nsmul, nsmul_divisor_apply]
  have hrD : (R.degZeroMap D : Divisor (ResidueField A) Fbar) ∈
      Divisor.principal (K := ResidueField A) (F := Fbar) := by
    have h1 : Pic0.mk (R.degZeroMap D) = 0 := by rw [← ConstantReduction.pic0Map_mk]; exact hz
    have h2 := (QuotientAddGroup.eq_zero_iff (R.degZeroMap D)).mp h1
    rwa [AddSubgroup.mem_addSubgroupOf] at h2
  obtain ⟨g, hg, hDg⟩ := hrD
  refine ⟨D, rfl, ⟨c • f₀, hc⟩, hres, hdivf, g, hg, fun Q => by rw [← hDg Q]; rfl, fun Q => ?_⟩
  have key := R.mapDomain_placeMap ⟨c • f₀, hc⟩ hres ((m • D : Divisor.degZero (K := L) (F := F)) :
      Divisor L F) (fun P => by rw [AddSubgroupClass.coe_nsmul, nsmul_divisor_apply, hdivf P]) Q
  rw [← key, AddSubgroupClass.coe_nsmul, Finsupp.mapDomain_smul, nsmul_divisor_apply, ← hDg Q]
  rfl

theorem ord_residue_mul_inv_pow_eq_zero (R : ConstantReduction A F Fbar) {f : R.integers}
    (hf : R.residue f ≠ 0) {g : Fbar} (hg : g ≠ 0) (m : ℕ)
    (h : ∀ Q : Place (ResidueField A) Fbar, Q.ord (R.residue f) = (m : ℤ) * Q.ord g)
    (Q : Place (ResidueField A) Fbar) : Q.ord (R.residue f * (g ^ m)⁻¹) = 0 := by
  rw [Q.ord_mul hf (inv_ne_zero (pow_ne_zero _ hg)), Q.ord_inv, h Q, ← zpow_natCast,
    Q.ord_zpow]
  ring

theorem mem_principal_of_pow_eq {q : ℕ} (hq : q ≠ 0) {D : Divisor L F} {f h : F} (hf : f ≠ 0)
    (hhf : h ^ q = f) (hD : ∀ P, (q : ℤ) * D P = P.ord f) :
    D ∈ Divisor.principal (K := L) (F := F) := by
  have hh : h ≠ 0 := by
    rintro rfl
    rw [zero_pow hq] at hhf
    exact hf hhf.symm
  refine ⟨h, hh, fun P => ?_⟩
  have h1 : (q : ℤ) * D P = (q : ℤ) * P.ord h := by
    rw [hD P, ← hhf, ← zpow_natCast, P.ord_zpow]
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hq) h1

theorem prime_case [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) [Ring.KrullDimLE 1 A]
    (F : Type*) [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar) (hR : R.IsGood)
    (hreg : ∃ x : R.integers, Transcendental (ResidueField A) (R.residue x) ∧
      0 < Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar ∧
      Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
        Module.finrank
          (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (q : ℕ) [hqp : Fact q.Prime] (hqk : (q : ResidueField A) ≠ 0)
    (z : Pic0 L F) (hqz : q • z = 0) (hz : R.pic0Map z = 0) : z = 0 := by
  classical
  have hq0 : q ≠ 0 := hqp.out.ne_zero
  have hqpos : 0 < q := hqp.out.pos

  obtain ⟨D, hDz, f, hfres, hdivf, g, hg0, -, hordfg⟩ := exists_kummerDatum R z q hqz hz
  subst hDz
  have hf0 : (f : F) ≠ 0 := by
    intro h
    apply hfres
    rw [show f = 0 from Subtype.ext h, map_zero]

  obtain ⟨xO, hxt, hxpos, hxeq⟩ := hreg
  haveI : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A) ({R.residue xO} : Set Fbar)) Fbar :=
    Module.finite_of_finrank_pos hxpos
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A

  set u : Fbar := R.residue f * (g ^ q)⁻¹ with hu
  have hu_ord : ∀ Q' : Place (ResidueField A) Fbar, Q'.ord u = 0 :=
    ord_residue_mul_inv_pow_eq_zero R hfres hg0 q hordfg
  obtain ⟨cbar, hcbar⟩ :=
    Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed (R.residue xO) hxt hu_ord
  obtain ⟨ebar, hebar⟩ := IsAlgClosed.exists_pow_nat_eq cbar hqpos
  set w : Fbar := algebraMap (ResidueField A) Fbar ebar * g with hw
  have hwq : w ^ q = R.residue f := by
    rw [hw, mul_pow, ← map_pow, hebar, hcbar, hu, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hg0), mul_one]
  have hw0 : w ≠ 0 := by
    intro h0
    apply hfres
    rw [← hwq, h0, zero_pow hq0]

  have hdvd : ∀ P : Place L F, (q : ℤ) ∣ P.ord (f : F) := fun P => ⟨_, (hdivf P).symm⟩
  have hgood : genusFF (ResidueField A) Fbar = genusFF L F := (R.isGood_iff).mp hR
  obtain ⟨h, hh⟩ := RegularProlongation.exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one
    A hF R.toRegularProlongation hgood ⟨xO, hxt, hxpos, hxeq⟩ hqk f hdvd w hw0 hwq
  exact mk_eq_zero_of_mem_principal D (mem_principal_of_pow_eq hq0 hf0 hh hdivf)

theorem of_finrank_eq [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) [Ring.KrullDimLE 1 A]
    (F : Type*) [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar) (hR : R.IsGood)
    (hreg : ∃ x : R.integers, Transcendental (ResidueField A) (R.residue x) ∧
      0 < Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar ∧
      Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
        Module.finrank
          (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (m : ℕ) (hm : (m : ResidueField A) ≠ 0)
    (z : Pic0 L F) (hmz : m • z = 0) (hz : R.pic0Map z = 0) : z = 0 := by
  refine eq_zero_of_forall_prime R.pic0Map m (ne_zero_of_natCast_ne_zero hm)
    (fun q hq hqm z' hqz hz' => ?_) z hmz hz
  haveI : Fact q.Prime := ⟨hq⟩
  exact prime_case A F hF Fbar R hR hreg q (natCast_ne_zero_of_dvd hm hqm) z' hqz hz'

end Kummer

theorem natCast_residueField_ne_zero {L : Type*} [Field L] (A : ValuationSubring L) {ℓ : ℕ} [Fact ℓ.Prime]
    (hA : A.LiesOverPrime ℓ) {m : ℕ} (hm : ¬ ℓ ∣ m) : (m : IsLocalRing.ResidueField A) ≠ 0 := by
  intro h0
  have hℓ : ((ℓ : A) : L) ∈ A.nonunits := by first | exact hA | simpa [ValuationSubring.LiesOverPrime] using hA
  rw [ValuationSubring.coe_mem_nonunits_iff] at hℓ
  have hmA : (m : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]; exact h0
  have hcop : IsCoprime (ℓ : A) (m : A) :=
    Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hm)
  obtain ⟨u, v, huv⟩ := hcop
  apply (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  rw [Ideal.eq_top_iff_one, ← huv]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hℓ) (Ideal.mul_mem_left _ _ hmA)

section Modular

open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem main (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (h : ModularCurve.ReductionInputsQExpModL A (CohCarrier.GammaH M H))
    (m : ℕ) (hm : ¬ ℓ ∣ m) (z : ModularCurve.JH M H) (hmz : m • z = 0)
    (hz : ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H) z = 0) :
    z = 0 := by

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
  haveI : Ring.KrullDimLE 1 A := ValuationSubring.krullDimLE_one_of_isAlgebraic_rat A

  haveI : IsAlgClosed (IsLocalRing.ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : CharP (IsLocalRing.ResidueField A) ℓ := ValuationSubring.charP_residueField_of_liesOverPrime ℓ A hA

  haveI : (CohCarrier.GammaH M H).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := ModularCurve.translation_mem_GammaH M H

  obtain ⟨R, -, hRpic, hRres⟩ :=
    ModularCurve.exists_constantReduction_pic0Map_eq_reductionQExpModL (CohCarrier.GammaH M H) hT A h

  have hF := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) (CohCarrier.GammaH M H) hT

  have hgood : R.IsGood := by
    rw [ConstantReduction.isGood_iff]
    exact ModularCurve.genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd M H hℓM
      (IsLocalRing.ResidueField A)

  obtain ⟨y, hy, hyk, htr, hpos, heq⟩ :=
    ModularCurve.exists_transcendental_finrank_adjoin_eq_xHFunctionFieldC_of_not_dvd M H hℓM A hA
  obtain ⟨hO, hres⟩ := hRres y hy hyk
  have hreg : ∃ x : R.integers, Transcendental (ResidueField A) (R.residue x) ∧
      0 < Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} :
          Set (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H))))
          (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H)) ∧
      Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({(x : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))} :
            Set (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))))
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) =
        Module.finrank
          (IntermediateField.adjoin (ResidueField A) ({R.residue x} :
            Set (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H))))
          (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H)) := by
    refine ⟨⟨_, hO⟩, ?_, ?_, ?_⟩
    · rw [hres]; exact htr
    · rw [hres]; exact hpos
    · rw [hres]; exact heq

  have hz' : R.pic0Map z = 0 := by rw [hRpic]; exact hz
  exact of_finrank_eq A _ hF _ R hgood hreg m (natCast_residueField_ne_zero A hA hm) z hmz hz'

end Modular

end ModularCurve.GammaHTorsionInjective

theorem solution (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (h : ModularCurve.ReductionInputsQExpModL A (CohCarrier.GammaH M H))
    (m : ℕ) (hm : ¬ ℓ ∣ m) (z : ModularCurve.JH M H) (hmz : m • z = 0)
    (hz : ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H) z = 0) :
    z = 0 :=
  ModularCurve.GammaHTorsionInjective.main M H hℓM A hA h m hm z hmz hz

end

end S_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero
end P2MW
export P2MW.S_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero (solution)
