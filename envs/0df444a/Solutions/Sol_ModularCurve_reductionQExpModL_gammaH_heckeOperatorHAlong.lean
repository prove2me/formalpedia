-- Prove2me | solution 1 for ModularCurve.reductionQExpModL_gammaH_heckeOperatorHAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/2d2461fa-ed64-5ced-9678-bc6e65aa7982

import Mathlib
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_ModularCurve_QExpFrobeniusModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd
import Theorems.Thm_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental
import Theorems.Thm_ModularCurve_qExpand_norm_heckeBetaHBar
import Theorems.Thm_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_reductionQExpModL_gammaH_heckeOperatorHAlong
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆"
p2m_attr_erase "simp" "ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun"
p2m_attr_erase "simp" "KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.abelJacobiDiv_single"
p2m_attr_erase "simp" "AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "AlgebraicCurve ModularCurve~coeffMap_injective HahnSeries"

namespace ESGammaHSol

local notation "Qb" => AlgebraicClosure ℚ

section Along

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem pullbackAlong_apply_eq_ord [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) {f : F} {D : Divisor K F} (hD : ∀ v, D v = v.ord f)
    (w : Place K F') : Divisor.pullbackAlong φ hφ D w = w.ord (φ f) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact Divisor.pullback_apply_eq_ord hD w

theorem pushforwardAlong_apply_eq_ord (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hfin : FiniteAlong K φ) (hN : NormFormulaAlong K φ hfin) {g : F'} (hg : g ≠ 0)
    {D : Divisor K F'} (hD : ∀ w, D w = w.ord g) (v : Place K F) :
    Divisor.pushforwardAlong φ hφ D v = v.ord (letI := algebraAlong φ; Algebra.norm F g) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : Module.Finite F F' := hfin
  exact hN g hg D hD v

end Along

section Engine

variable {L F : Type*} [Field L] [Field F] [Algebra L F]
variable {k Fb : Type*} [Field k] [Field Fb] [Algebra k Fb]

theorem int_eq_zero_of_forall_dvd {a : ℤ} (h : ∀ n : ℕ, n ≠ 0 → (n : ℤ) ∣ a) : a = 0 :=
  Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (h (a.natAbs + 1) (Nat.succ_ne_zero _))
    (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)

theorem eq_of_agree (S : Set (Divisor L F))
    (hgen : Divisor.principal (K := L) (F := F) ≤ AddSubgroup.closure S)
    (Φ Ψ : Divisor L F →+ Divisor k Fb) (hagree : ∀ D ∈ S, Φ D = Ψ D)
    (hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 L F, ∃ y : Pic0 L F, n • y = x)
    {D : Divisor L F} (hD : D ∈ Divisor.degZero (K := L) (F := F)) : Φ D = Ψ D := by
  classical
  set δ : Divisor L F →+ Divisor k Fb := Φ - Ψ with hδ
  have hδapp : ∀ E, δ E = Φ E - Ψ E := fun E => rfl

  have hδprin : ∀ E ∈ Divisor.principal (K := L) (F := F), δ E = 0 := by
    intro E hE
    have hE' := hgen hE
    clear hE
    induction hE' using AddSubgroup.closure_induction with
    | mem E hE => rw [hδapp, hagree E hE, sub_self]
    | zero => exact map_zero δ
    | add E E' _ _ hE hE' => rw [map_add, hE, hE', add_zero]
    | neg E _ hE => rw [map_neg, hE, neg_zero]

  have hδD : δ D = 0 := by
    ext Q
    rw [Finsupp.zero_apply]
    refine int_eq_zero_of_forall_dvd fun n hn => ?_
    obtain ⟨y, hy⟩ := hdiv n hn (Pic0.mk ⟨D, hD⟩)
    obtain ⟨E, rfl⟩ := Pic0.mk_surjective y
    have hmem : ((⟨D, hD⟩ : Divisor.degZero (K := L) (F := F)) - n • E :
        Divisor.degZero (K := L) (F := F)) ∈
          (Divisor.principal (K := L) (F := F)).addSubgroupOf (Divisor.degZero (K := L) (F := F)) := by
      rw [← QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.mk_nsmul]
      exact hy.symm
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroupClass.coe_sub, AddSubgroupClass.coe_nsmul] at hmem
    have h0 := hδprin _ hmem
    rw [map_sub, map_nsmul, sub_eq_zero] at h0
    refine ⟨δ (E : Divisor L F) Q, ?_⟩
    rw [h0, Finsupp.smul_apply, nsmul_eq_mul]
  rw [hδapp] at hδD
  exact sub_eq_zero.mp hδD

end Engine

section Series

variable {R S : Type*} [CommRing R] [CommRing S]

theorem coeffMap_qTwist (f : R →+* S) (c : Rˣ) (x : LaurentSeries R) :
    coeffMap f (qTwist c x) = qTwist (Units.map (f : R →* S) c) (coeffMap f x) := by
  ext n
  rw [coeffMap_coeff, qTwist_coeff, qTwist_coeff, coeffMap_coeff, map_mul, ← map_zpow, Units.coe_map]
  rfl

theorem coeffMap_qExpand' (f : R →+* S) (n : ℕ) [NeZero n] (x : LaurentSeries R) :
    coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

def unexpand (ℓ : ℕ) [NeZero ℓ] (P : LaurentSeries R) : LaurentSeries R where
  coeff k := P.coeff ((ℓ : ℤ) * k)
  isPWO_support' := by
    have hℓ : (0 : ℤ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
    refine (P.isPWO_support.image_of_monotone (f := fun n : ℤ => n / (ℓ : ℤ))
      (fun a b h => Int.ediv_le_ediv hℓ h)).mono ?_
    intro k hk
    refine ⟨(ℓ : ℤ) * k, hk, ?_⟩
    show (ℓ : ℤ) * k / (ℓ : ℤ) = k
    exact Int.mul_ediv_cancel_left k hℓ.ne'

theorem unexpand_coeff (ℓ : ℕ) [NeZero ℓ] (P : LaurentSeries R) (k : ℤ) :
    (unexpand ℓ P).coeff k = P.coeff ((ℓ : ℤ) * k) := rfl

theorem qExpand_unexpand (ℓ : ℕ) [NeZero ℓ] (P : LaurentSeries R)
    (hP : ∀ n : ℤ, ¬ (ℓ : ℤ) ∣ n → P.coeff n = 0) : qExpand R ℓ (unexpand ℓ P) = P := by
  ext n
  by_cases h : (ℓ : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := h
    rw [qExpand_coeff_mul, unexpand_coeff]
  · rw [qExpand_coeff_of_not_dvd ℓ _ h, hP n h]

theorem coeffMap_injective {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (coeffMap f : LaurentSeries R → LaurentSeries S) := by
  intro x y h
  ext n
  have := congrArg (fun s : LaurentSeries S => s.coeff n) h
  simp only [coeffMap_coeff] at this
  exact hf this

end Series

section RootsOfUnity

variable {ℓ : ℕ} [Fact ℓ.Prime] (A : ValuationSubring Qb)

theorem zeta_mem {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) : ζ ∈ A := by
  have hprime : ℓ.Prime := Fact.out
  rcases A.mem_or_inv_mem ζ with h | h
  · exact h
  · have h2 : (ζ⁻¹) ^ (ℓ - 1) = ζ := by
      rw [inv_pow]
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ, Nat.sub_add_cancel hprime.one_le, hζ.pow_eq_one]
    rw [← h2]
    exact pow_mem h _

def zetaUnit {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) : Aˣ :=
  Units.ofPowEqOne (⟨ζ, zeta_mem A hζ⟩ : A) ℓ
    (Subtype.ext (by
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      exact hζ.pow_eq_one)) (NeZero.ne ℓ)

def zu {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) : Qbˣ := Units.mk0 ζ (hζ.ne_zero (NeZero.ne ℓ))

theorem map_subtype_zetaUnit {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) :
    Units.map (A.subtype : A →* Qb) (zetaUnit A hζ) = zu hζ :=
  Units.ext rfl

theorem isPrimitiveRoot_zu {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) : IsPrimitiveRoot (zu hζ) ℓ :=
  IsPrimitiveRoot.coe_units_iff.mp hζ

theorem map_residue_zetaUnit [CharP (IsLocalRing.ResidueField A) ℓ]
    {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) :
    Units.map (IsLocalRing.residue A : A →* IsLocalRing.ResidueField A) (zetaUnit A hζ) = 1 := by
  have hzℓ : (Units.map (IsLocalRing.residue A : A →* IsLocalRing.ResidueField A)
      (zetaUnit A hζ)) ^ ℓ = 1 := by
    rw [← map_pow, zetaUnit, Units.pow_ofPowEqOne, map_one]
  apply Units.ext
  have h0 : ((Units.map (IsLocalRing.residue A : A →* IsLocalRing.ResidueField A)
      (zetaUnit A hζ) : IsLocalRing.ResidueField A) - 1) ^ ℓ = 0 := by
    rw [sub_pow_char, ← Units.val_pow_eq_pow_val, hzℓ, Units.val_one, one_pow, sub_self]
  rw [Units.val_one]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (NeZero.ne ℓ)).mp h0)

end RootsOfUnity

section CharL

variable {k : Type*} [Field k] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ]

omit [Fact ℓ.Prime] [CharP k ℓ] in

theorem coeffMap_intSeriesC (g : k →+* k) (p : PowerSeries ℤ) : coeffMap g (intSeriesC k p) = intSeriesC k p := by
  ext n
  rw [coeffMap_coeff]
  rcases lt_or_ge n 0 with hn | hn
  · rw [intSeriesC, ofPowerSeries_coeff_of_neg _ hn, map_zero]
  · lift n to ℕ using hn with n
    rw [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, eq_intCast, map_intCast]

omit [Fact ℓ.Prime] [CharP k ℓ] in

theorem coeffMap_mem (g : k →+* k) {x : LaurentSeries k} (hx : x ∈ qExpFunctionFieldC k Γ) :
    coeffMap g x ∈ qExpFunctionFieldC k Γ := by
  have hx' : x ∈ (qExpFunctionFieldC k Γ).toSubfield := hx
  rw [qExpFunctionFieldC, IntermediateField.adjoin_toSubfield] at hx'
  have key : (Subfield.closure (Set.range (algebraMap k (LaurentSeries k)) ∪ intFormRatiosC k Γ)).map
      (coeffMap g) ≤ (qExpFunctionFieldC k Γ).toSubfield := by
    rw [RingHom.map_field_closure, Subfield.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with ⟨c, rfl⟩ | ⟨w, f, g', pf, pg, hf, hg, hg0, rfl⟩
    · rw [coeffMap_algebraMap]
      exact (qExpFunctionFieldC k Γ).algebraMap_mem _
    · change coeffMap g (intSeriesC k pf / intSeriesC k pg) ∈ qExpFunctionFieldC k Γ
      rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]
      exact div_mem_qExpFunctionFieldC f g' hf hg hg0
  exact key ⟨x, hx', rfl⟩

theorem norm_frobenius_eq (hrank : finrankAlong k (qExpFrobeniusModL k Γ ℓ) = ℓ)
    {f g : qExpFunctionFieldC k Γ} (hg : qExpFrobeniusModL k Γ ℓ g = f ^ ℓ) :
    (letI := algebraAlong (qExpFrobeniusModL k Γ ℓ);
      Algebra.norm (qExpFunctionFieldC k Γ) f) = g := by
  letI := algebraAlong (qExpFrobeniusModL k Γ ℓ)
  haveI : CharP (qExpFunctionFieldC k Γ) ℓ :=
    charP_of_injective_algebraMap (algebraMap k (qExpFunctionFieldC k Γ)).injective ℓ
  have hpow : (Algebra.norm (qExpFunctionFieldC k Γ) f) ^ ℓ = g ^ ℓ := by
    have h3 : Algebra.norm (qExpFunctionFieldC k Γ)
        (algebraMap (qExpFunctionFieldC k Γ) (qExpFunctionFieldC k Γ) g) =
          g ^ finrankAlong k (qExpFrobeniusModL k Γ ℓ) :=
      Algebra.norm_algebraMap g
    calc (Algebra.norm (qExpFunctionFieldC k Γ) f) ^ ℓ
        = Algebra.norm (qExpFunctionFieldC k Γ) (f ^ ℓ) := (map_pow (Algebra.norm (qExpFunctionFieldC k Γ)) f ℓ).symm
      _ = Algebra.norm (qExpFunctionFieldC k Γ)
            (algebraMap (qExpFunctionFieldC k Γ) (qExpFunctionFieldC k Γ) g) := by
          rw [show algebraMap (qExpFunctionFieldC k Γ) (qExpFunctionFieldC k Γ) g =
            qExpFrobeniusModL k Γ ℓ g from rfl, hg]
      _ = g ^ finrankAlong k (qExpFrobeniusModL k Γ ℓ) := h3
      _ = g ^ ℓ := by rw [hrank]
  exact frobenius_inj (qExpFunctionFieldC k Γ) ℓ hpow

theorem coe_eq_coeffMap_frobenius_of_eq_pow {f g : qExpFunctionFieldC k Γ}
    (hg : qExpFrobeniusModL k Γ ℓ g = f ^ ℓ) :
    (g : LaurentSeries k) = coeffMap (frobenius k ℓ) (f : LaurentSeries k) := by
  haveI := charP_laurentSeriesC k ℓ
  apply qExpand_injective ℓ
  have h := congrArg (fun z : qExpFunctionFieldC k Γ => (z : LaurentSeries k)) hg
  simp only [coe_qExpFrobeniusModL] at h
  rw [h, show ((f ^ ℓ : qExpFunctionFieldC k Γ) : LaurentSeries k) = (f : LaurentSeries k) ^ ℓ from rfl,
    pow_char_eq_coeffMap_frobenius_qExpand ℓ (f : LaurentSeries k), coeffMap_qExpand']

end CharL

section Agree

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ} [Fact ℓ.Prime]
variable {A : ValuationSubring Qb} [CharP (IsLocalRing.ResidueField A) ℓ]

local notation "kA" => IsLocalRing.ResidueField A
local notation "ΓH" => CohCarrier.GammaH M H
local notation "KK" => xHFunctionFieldBar M H
local notation "FF" => qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H)

variable (A M H) in

def genSet (d : (ZMod M)ˣ) : Set (Divisor Qb KK) :=
  {D | ∃ (y u : LaurentSeries A) (hy : coeffMap A.subtype y ∈ KK),
      coeffMap A.subtype u = ((diamondAutHBar M H d ⟨coeffMap A.subtype y, hy⟩ : KK) : LaurentSeries Qb) ∧
      coeffMap (IsLocalRing.residue A) y ∈ xHFunctionFieldC kA M H ∧
      coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
      coeffMap (IsLocalRing.residue A) u ∈ xHFunctionFieldC kA M H ∧
      coeffMap (IsLocalRing.residue A) u ≠ 0 ∧
      ∀ P, D P = P.ord (⟨coeffMap A.subtype y, hy⟩ : KK)}

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem agree_on_generator (hℓM : ¬ ℓ ∣ M) (hin : HeckeDiamondInputsHAll M H)
    {r : Place Qb (laurentBaseChange Qb (qExpFunctionFieldC ℚ ΓH)) → Place kA FF}
    (hr : IsPlaceReductionQExpModL A ΓH r)
    (hα : HeckeAlphaHBarIntegral Qb M H ℓ) (hβ : HeckeBetaHBarIntegral Qb M H ℓ)
    [HasPrincipalDivisors Qb (laurentBaseChange Qb (xHTopFunctionFieldC ℚ M H (M * ℓ)))]
    (hfin : FiniteAlong Qb (heckeAlphaHBar Qb M H ℓ)) (hN : NormFormulaAlong Qb (heckeAlphaHBar Qb M H ℓ) hfin)
    [HasPrincipalDivisors kA FF]
    (hfin' : FiniteAlong kA (qExpFrobeniusModL kA ΓH ℓ))
    (hN' : NormFormulaAlong kA (qExpFrobeniusModL kA ΓH ℓ) hfin')
    (hrank : finrankAlong kA (qExpFrobeniusModL kA ΓH ℓ) = ℓ)
    {D : Divisor Qb KK}
    (hD : D ∈ genSet M H A (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM))) :
    Finsupp.mapDomain r (heckeDivHBar hα hβ D) =
      qExpFrobeniusDivPushforwardModL kA ΓH ℓ
          (Finsupp.mapDomain r
            (SemilinearAut.ofAlgAut (diamondAutHBar M H
              (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM))) • D)) +
        qExpFrobeniusDivPullbackModL kA ΓH ℓ (Finsupp.mapDomain r D) := by
  classical
  obtain ⟨y, u, hy, hu, hyk, hy0, huk, hu0, hDy⟩ := hD
  set d : (ZMod M)ˣ := ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM) with hd
  set σ : KK ≃ₐ[Qb] KK := diamondAutHBar M H d with hσ

  set f : KK := ⟨coeffMap A.subtype y, hy⟩ with hf_def
  have hyk' : coeffMap (IsLocalRing.residue A) y ∈ FF := hyk
  have huk' : coeffMap (IsLocalRing.residue A) u ∈ FF := huk
  set fbar : FF := ⟨coeffMap (IsLocalRing.residue A) y, hyk'⟩ with hfbar_def
  set ubar : FF := ⟨coeffMap (IsLocalRing.residue A) u, huk'⟩ with hubar_def
  have hfbar : fbar ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  have hubar : ubar ≠ 0 := fun h => hu0 (congrArg Subtype.val h)
  have hAinj : Function.Injective (A.subtype) := fun a b hab => Subtype.ext hab
  have hy0' : y ≠ 0 := by
    rintro rfl
    exact hy0 (map_zero _)
  have hf : f ≠ 0 := by
    intro h
    apply hy0'
    have h' : coeffMap A.subtype y = 0 := congrArg Subtype.val h
    exact coeffMap_injective hAinj (by rw [h', map_zero])
  have hβf : heckeBetaHBar Qb M H ℓ f ≠ 0 := (map_ne_zero _).mpr hf

  have hu_mem : coeffMap A.subtype u ∈ KK := by rw [hu]; exact SetLike.coe_mem _
  have hσf : σ f = ⟨coeffMap A.subtype u, hu_mem⟩ := Subtype.ext hu.symm

  have hpull : ∀ w, Divisor.pullbackAlong (heckeBetaHBar Qb M H ℓ) hβ D w = w.ord (heckeBetaHBar Qb M H ℓ f) :=
    fun w => pullbackAlong_apply_eq_ord (heckeBetaHBar Qb M H ℓ) hβ hDy w
  have hT : ∀ v, heckeDivHBar hα hβ D v =
      v.ord (letI := algebraAlong (heckeAlphaHBar Qb M H ℓ);
        Algebra.norm KK (heckeBetaHBar Qb M H ℓ f)) := by
    intro v
    rw [heckeDivHBar, Divisor.correspondence_apply]
    exact pushforwardAlong_apply_eq_ord (heckeAlphaHBar Qb M H ℓ) hα hfin hN hβf hpull v

  haveI : NeZero ((ℓ : ℕ) : Qb) := NeZero.charZero
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Qb ℓ
  have hnorm := ModularCurve.qExpand_norm_heckeBetaHBar M H hℓM hin (zu hζ) (isPrimitiveRoot_zu hζ) f
  rw [← hσ, hσf] at hnorm

  set P : LaurentSeries A :=
    (∏ j ∈ Finset.range ℓ, qTwist (zetaUnit A hζ ^ j) u) * qExpand A ℓ (qExpand A ℓ y) with hP
  have hPQ : coeffMap A.subtype P
      = (∏ j ∈ Finset.range ℓ, qTwist (zu hζ ^ j) (coeffMap A.subtype u))
        * qExpand Qb ℓ (qExpand Qb ℓ (coeffMap A.subtype y)) := by
    rw [hP, map_mul, map_prod, coeffMap_qExpand', coeffMap_qExpand']
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [coeffMap_qTwist, map_pow, map_subtype_zetaUnit]
  have hPQ' := hPQ.trans hnorm.symm

  have hPsupp : ∀ n : ℤ, ¬ (ℓ : ℤ) ∣ n → P.coeff n = 0 := by
    intro n hn
    have h := congrArg (fun s : LaurentSeries Qb => s.coeff n) hPQ'
    simp only [coeffMap_coeff, qExpand_coeff_of_not_dvd ℓ _ hn] at h
    exact (map_eq_zero_iff A.subtype hAinj).mp h
  set y' : LaurentSeries A := unexpand ℓ P with hy'
  have hy'1 : coeffMap A.subtype y' = ((letI := algebraAlong (heckeAlphaHBar Qb M H ℓ);
        Algebra.norm KK (heckeBetaHBar Qb M H ℓ f) : KK) : LaurentSeries Qb) := by
    apply qExpand_injective ℓ
    rw [← coeffMap_qExpand' A.subtype ℓ (unexpand ℓ P), qExpand_unexpand ℓ P hPsupp]
    exact hPQ'
  have hy'2 : coeffMap (IsLocalRing.residue A) y' =
      coeffMap (frobenius kA ℓ) (coeffMap (IsLocalRing.residue A) u) *
        qExpand kA ℓ (coeffMap (IsLocalRing.residue A) y) := by
    apply qExpand_injective ℓ
    rw [← coeffMap_qExpand' (IsLocalRing.residue A) ℓ (unexpand ℓ P), qExpand_unexpand ℓ P hPsupp,
      hP, map_mul, map_prod, coeffMap_qExpand', coeffMap_qExpand',
      Finset.prod_eq_pow_card (b := coeffMap (IsLocalRing.residue A) u), Finset.card_range,
      map_mul, ← coeffMap_qExpand' (frobenius kA ℓ) ℓ, ← pow_char_eq_coeffMap_frobenius_qExpand ℓ]
    intro j _
    rw [coeffMap_qTwist, map_pow, map_residue_zetaUnit, one_pow, qTwist_one_apply]

  have hy'mem : coeffMap A.subtype y' ∈ KK := by rw [hy'1]; exact SetLike.coe_mem _
  have hT' : ∀ v, heckeDivHBar hα hβ D v = v.ord (⟨coeffMap A.subtype y', hy'mem⟩ : KK) := by
    intro v
    rw [hT v]
    congr 1
    exact Subtype.ext hy'1.symm

  obtain ⟨g, hg⟩ := exists_qExpFrobeniusModL_eq_pow kA ΓH ℓ ubar
  have hgcoe : (g : LaurentSeries kA) = coeffMap (frobenius kA ℓ) (coeffMap (IsLocalRing.residue A) u) :=
    coe_eq_coeffMap_frobenius_of_eq_pow hg
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hg
    exact pow_ne_zero ℓ hubar hg.symm
  have hFr0 : qExpFrobeniusModL kA ΓH ℓ fbar ≠ 0 := (map_ne_zero _).mpr hfbar
  have hprod : coeffMap (IsLocalRing.residue A) y' = ((g * qExpFrobeniusModL kA ΓH ℓ fbar : FF) : LaurentSeries kA) := by
    rw [hy'2, ← hgcoe]
    rfl
  have hy'k : coeffMap (IsLocalRing.residue A) y' ∈ FF := by
    rw [hprod]; exact SetLike.coe_mem _
  have hy'ne : coeffMap (IsLocalRing.residue A) y' ≠ 0 := by
    rw [hprod]
    exact fun h => (mul_ne_zero hg0 hFr0) (Subtype.ext h)
  have hy'eq : (⟨coeffMap (IsLocalRing.residue A) y', hy'k⟩ : FF) = g * qExpFrobeniusModL kA ΓH ℓ fbar :=
    Subtype.ext hprod

  have hup : ∀ Q, Finsupp.mapDomain r (heckeDivHBar hα hβ D) Q =
      Q.ord g + Q.ord (qExpFrobeniusModL kA ΓH ℓ fbar) := by
    intro Q
    rw [hr.2 y' hy'mem hy'k hy'ne (heckeDivHBar hα hβ D) hT' Q, hy'eq, Q.ord_mul hg0 hFr0]
  have hdown : ∀ Q, Finsupp.mapDomain r D Q = Q.ord fbar := hr.2 y hy hyk' hy0 D hDy
  have hσD : ∀ w, (SemilinearAut.ofAlgAut σ • D) w = w.ord (⟨coeffMap A.subtype u, hu_mem⟩ : KK) := by
    intro w
    rw [SemilinearAut.divisor_smul_apply, hDy, ← hσf]
    have h := SemilinearAut.ord_smul (SemilinearAut.ofAlgAut σ) ((SemilinearAut.ofAlgAut σ)⁻¹ • w) f
    rw [smul_inv_smul, SemilinearAut.ofAlgAut_smul] at h
    exact h.symm
  have hσdown : ∀ Q, Finsupp.mapDomain r (SemilinearAut.ofAlgAut σ • D) Q = Q.ord ubar :=
    hr.2 u hu_mem huk' hu0 _ hσD

  have hpush' : ∀ Q, qExpFrobeniusDivPushforwardModL kA ΓH ℓ
      (Finsupp.mapDomain r (SemilinearAut.ofAlgAut σ • D)) Q = Q.ord g := by
    intro Q
    have h1 := pushforwardAlong_apply_eq_ord (qExpFrobeniusModL kA ΓH ℓ) (qExpFrobeniusModL_isIntegral kA ΓH ℓ)
      hfin' hN' hubar hσdown Q
    have h2 := norm_frobenius_eq (k := kA) (Γ := ΓH) hrank hg
    rw [h2] at h1
    exact h1
  have hpull' : ∀ Q, qExpFrobeniusDivPullbackModL kA ΓH ℓ (Finsupp.mapDomain r D) Q =
      Q.ord (qExpFrobeniusModL kA ΓH ℓ fbar) := fun Q =>
    pullbackAlong_apply_eq_ord (qExpFrobeniusModL kA ΓH ℓ) (qExpFrobeniusModL_isIntegral kA ΓH ℓ) hdown Q

  ext Q
  rw [hup Q, Finsupp.add_apply, hpush' Q, hpull' Q]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem divisor_identity (hℓM : ¬ ℓ ∣ M) (hin : HeckeDiamondInputsHAll M H)
    {r : Place Qb (laurentBaseChange Qb (qExpFunctionFieldC ℚ ΓH)) → Place kA FF}
    (hr : IsPlaceReductionQExpModL A ΓH r)
    (hα : HeckeAlphaHBarIntegral Qb M H ℓ) (hβ : HeckeBetaHBarIntegral Qb M H ℓ)
    [HasPrincipalDivisors Qb (laurentBaseChange Qb (xHTopFunctionFieldC ℚ M H (M * ℓ)))]
    (hfin : FiniteAlong Qb (heckeAlphaHBar Qb M H ℓ)) (hN : NormFormulaAlong Qb (heckeAlphaHBar Qb M H ℓ) hfin)
    [HasPrincipalDivisors kA FF]
    (hfin' : FiniteAlong kA (qExpFrobeniusModL kA ΓH ℓ))
    (hN' : NormFormulaAlong kA (qExpFrobeniusModL kA ΓH ℓ) hfin')
    (hrank : finrankAlong kA (qExpFrobeniusModL kA ΓH ℓ) = ℓ)
    (hgen : Divisor.principal (K := Qb) (F := KK) ≤
      AddSubgroup.closure (genSet M H A (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM))))
    (hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 Qb KK, ∃ y : Pic0 Qb KK, n • y = x)
    {D : Divisor Qb KK} (hD0 : D ∈ Divisor.degZero (K := Qb) (F := KK)) :
    Finsupp.mapDomain r (heckeDivHBar hα hβ D) =
      qExpFrobeniusDivPushforwardModL kA ΓH ℓ
          (Finsupp.mapDomain r
            (SemilinearAut.ofAlgAut (diamondAutHBar M H
              (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM))) • D)) +
        qExpFrobeniusDivPullbackModL kA ΓH ℓ (Finsupp.mapDomain r D) := by
  set g := SemilinearAut.ofAlgAut (K := Qb) (F := KK)
    (diamondAutHBar M H (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM))) with hg_def
  let mr : Divisor Qb KK →+ Divisor kA FF := Finsupp.mapDomain.addMonoidHom r
  let Φ : Divisor Qb KK →+ Divisor kA FF := mr.comp (heckeDivHBar hα hβ)
  let Ψ : Divisor Qb KK →+ Divisor kA FF :=
    (qExpFrobeniusDivPushforwardModL kA ΓH ℓ).comp (mr.comp (DistribSMul.toAddMonoidHom (Divisor Qb KK) g)) +
      (qExpFrobeniusDivPullbackModL kA ΓH ℓ).comp mr
  have hΦ : ∀ E, Φ E = Finsupp.mapDomain r (heckeDivHBar hα hβ E) := fun E => rfl
  have hΨ : ∀ E, Ψ E = qExpFrobeniusDivPushforwardModL kA ΓH ℓ (Finsupp.mapDomain r (g • E)) +
      qExpFrobeniusDivPullbackModL kA ΓH ℓ (Finsupp.mapDomain r E) := fun E => rfl
  have key := eq_of_agree (genSet M H A (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM)))
    hgen Φ Ψ (fun E hE => by
      rw [hΦ, hΨ]
      exact agree_on_generator hℓM hin hr hα hβ hfin hN hfin' hN' hrank hE)
    hdiv hD0
  rw [hΦ, hΨ] at key
  exact key

end Agree

section Upstairs

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

scoped instance : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

theorem exists_transcendental_bar :
    ∃ x : xHFunctionFieldBar M H, Transcendental Qb x ∧
      FiniteDimensional (IntermediateField.adjoin Qb ({x} : Set (xHFunctionFieldBar M H))) (xHFunctionFieldBar M H) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange Qb (CohCarrier.GammaH M H)
    (translation_mem_GammaH M H)

theorem jH_divisible (n : ℕ) (hn : n ≠ 0) (x : Pic0 Qb (xHFunctionFieldBar M H)) :
    ∃ y : Pic0 Qb (xHFunctionFieldBar M H), n • y = x := by
  obtain ⟨t, htr, hfd⟩ := exists_transcendental_bar M H
  haveI : IsCurveOver Qb (xHFunctionFieldBar M H) :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfd
  exact AlgebraicCurve.Pic0.exists_nsmul_eq Qb (xHFunctionFieldBar M H) ⟨t, htr, hfd⟩ n hn x

end Upstairs

end ESGammaHSol
p2m_reactivate "P2MW.S_ModularCurve_reductionQExpModL_gammaH_heckeOperatorHAlong.ESGammaHSol"

open ESGammaHSol in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (IsLocalRing.ResidueField A) ℓ]
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (h : ModularCurve.ReductionInputsQExpModL A (CohCarrier.GammaH M H))
    (z : ModularCurve.JH M H) :
    ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H)
        (ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ z) =
      ModularCurve.qExpFrobeniusPushforwardModL (IsLocalRing.ResidueField A)
          (CohCarrier.GammaH M H) ℓ
          (ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H)
            (ModularCurve.diamondHBar M H
              (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM)) z))
        + ModularCurve.qExpFrobeniusPullbackModL (IsLocalRing.ResidueField A)
            (CohCarrier.GammaH M H) ℓ
            (ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H) z) := by

  obtain ⟨h0, hα, hβ, hP, hfin, hFI, hN⟩ := hin.heckeInputsHAlong ℓ Fact.out
  haveI := hP
  haveI : IsAlgClosed (IsLocalRing.ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  have hF : ∃ x : qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H),
      Transcendental (IsLocalRing.ResidueField A) x ∧
        FiniteDimensional (IntermediateField.adjoin (IsLocalRing.ResidueField A)
          ({x} : Set (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H))))
          (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H)) :=
    (ModularCurve.exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd M H hℓM A hA).1
  obtain ⟨⟨hPk, hfin', hFI', hN'⟩, hrank⟩ :=
    ModularCurve.qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental (IsLocalRing.ResidueField A)
      (ℓ := ℓ) (CohCarrier.GammaH M H) hF
  haveI := hPk

  obtain ⟨D, rfl⟩ := Pic0.mk_surjective z
  rw [heckeOperatorHAlong_eq h0 hα hβ hFI hfin hN, heckePic0HBar, Pic0.correspondence_mk,
    diamondHBar_apply, SemilinearAut.pic0_smul_mk]
  have hred : ∀ D' : Divisor.degZero (K := AlgebraicClosure ℚ) (F := xHFunctionFieldBar M H),
      reductionQExpModL A (CohCarrier.GammaH M H) (Pic0.mk D') =
        Pic0.mk (laurentReductionDegZero (placeReductionQExpModL h)
          (isPlaceReductionQExpModL_placeReductionQExpModL h).1 D') :=
    fun D' => reductionQExpModL_mk h D'
  erw [hred, hred, hred]
  rw [qExpFrobeniusPushforwardModL_mk hfin' hFI' hN', qExpFrobeniusPullbackModL_mk hfin' hFI' hN',
    ← Pic0.mk_add]
  refine congrArg Pic0.mk (Subtype.ext ?_)

  exact divisor_identity hℓM hin (isPlaceReductionQExpModL_placeReductionQExpModL h) hα hβ hfin hN hfin' hN'
    hrank (ModularCurve.principal_le_closure_divisor_laurentIntegral_diamondAutHBar M H hℓM A hA hin _)
    (jH_divisible M H) D.2

end
end S_ModularCurve_reductionQExpModL_gammaH_heckeOperatorHAlong
end P2MW
export P2MW.S_ModularCurve_reductionQExpModL_gammaH_heckeOperatorHAlong (solution)
