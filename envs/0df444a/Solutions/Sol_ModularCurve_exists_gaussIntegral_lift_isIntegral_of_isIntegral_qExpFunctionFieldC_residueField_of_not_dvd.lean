-- Prove2me | solution 1 for ModularCurve.exists_gaussIntegral_lift_isIntegral_of_isIntegral_qExpFunctionFieldC_residueField_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/6cec8e6d-1ff1-57e9-bca4-18b825889b91

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
import Theorems.Thm_AlgebraicCurve_RegularProlongation_residue_integralClosure_surjective_of_genusFF_eq
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_monic_coeff_natDegree_le_of_forall_valuationSubring
import Theorems.Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff
import Theorems.Thm_ModularCurve_finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd
import Theorems.Thm_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_CohCarrier_exists_eq_gammaH_of_gamma1_le_of_le_gamma0
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_gaussIntegral_lift_isIntegral_of_isIntegral_qExpFunctionFieldC_residueField_of_not_dvd
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
p2m_attr_erase "simp" "CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply"
p2m_attr_erase "simp" "ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero"
p2m_attr_erase "simp" "compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "ModularCurve AlgebraicCurve~genus"

noncomputable section

namespace LiftingH

section CoeffMap

variable {K K' : Type*} [Field K] [Field K'] (φ : K →+* K')

theorem coeffMap_algebraMap' (c : K) :
    coeffMap φ (algebraMap K (LaurentSeries K) c) = algebraMap K' (LaurentSeries K') (φ c) := by
  rw [algebraMap_laurentSeries_eq_single, coeffMap_single, algebraMap_laurentSeries_eq_single]

theorem eval₂_coeffMap (t y : LaurentSeries K) (P : Polynomial (Polynomial K))
    (hP : Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K)) t) y P = 0) :
    Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K' (LaurentSeries K')) (coeffMap φ t))
      (coeffMap φ y) (P.map (Polynomial.mapRingHom φ)) = 0 := by
  have hcomp : (coeffMap φ).comp (Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K)) t) =
      (Polynomial.eval₂RingHom (algebraMap K' (LaurentSeries K')) (coeffMap φ t)).comp
        (Polynomial.mapRingHom φ) := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp [coeffMap_algebraMap']
    · simp
  have := congrArg (coeffMap φ) hP
  rw [map_zero, Polynomial.hom_eval₂, hcomp] at this
  rwa [Polynomial.eval₂_map]

end CoeffMap

section Adjoin

variable {K : Type*} [Field K] {E : IntermediateField K (LaurentSeries K)}

theorem isIntegral_adjoin_of_eval₂ (g h : E) (P : Polynomial (Polynomial K)) (hP : P.Monic)
    (hev : Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K))
      (g : LaurentSeries K)) (h : LaurentSeries K) P = 0) :
    IsIntegral (Algebra.adjoin K ({g} : Set E)) h := by
  set S := Algebra.adjoin K ({g} : Set E) with hS
  have hmem : ∀ p : Polynomial K, (Polynomial.aeval g p : E) ∈ S := fun p => by
    rw [hS, Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨p, rfl⟩
  let θ : Polynomial K →+* S :=
    (Polynomial.aeval g : Polynomial K →ₐ[K] E).toRingHom.codRestrict S hmem
  refine ⟨P.map θ, hP.map θ, ?_⟩
  rw [Polynomial.eval₂_map]
  apply Subtype.val_injective
  have hval := Polynomial.hom_eval₂ P ((algebraMap S E).comp θ) (E.val : E →+* LaurentSeries K) h
  have hcomp : (E.val : E →+* LaurentSeries K).comp ((algebraMap S E).comp θ) =
      Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K)) (g : LaurentSeries K) := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp [θ]
    · simp [θ]
  rw [hcomp] at hval
  change (E.val : E →+* LaurentSeries K) _ = ((0 : E) : LaurentSeries K)
  rw [hval]
  simpa using hev

end Adjoin

theorem adjoin_simple_inv_eq {K E : Type*} [Field K] [Field E] [Algebra K E] (a : E) :
    IntermediateField.adjoin K ({a⁻¹} : Set E) = IntermediateField.adjoin K {a} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self K a)
  · rw [IntermediateField.adjoin_simple_le_iff]
    rw [← inv_inv a, inv_inv a⁻¹]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self K a⁻¹)

theorem transcendental_inv {R K : Type*} [CommRing R] [Field K] [Algebra R K] {x : K}
    (hx : Transcendental R x) : Transcendental R x⁻¹ := fun h =>
  hx (IsAlgebraic.inv_iff.mp h)

section ValRing

variable {F : Type*} [Field F]

theorem mem_of_monic_of_coeff_mem (V : ValuationSubring F) (Q : Polynomial F) (hQ : Q.Monic)
    (hc : ∀ i, Q.coeff i ∈ V) (g : F) (hg : Q.eval g = 0) : g ∈ V := by
  have hlift : Q ∈ Polynomial.lifts (algebraMap V F) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨Q.coeff n, hc n⟩, rfl⟩
  obtain ⟨Q', hQ'map, -, hQ'monic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hQ
  have hint : IsIntegral V g := ⟨Q', hQ'monic, by rw [← Polynomial.eval_map, hQ'map, hg]⟩
  have hI : V.valuation.Integers V :=
    { hom_inj := Subtype.val_injective
      map_le_one := fun x => V.valuation_le_one x
      exists_of_le_one := fun r hr => ⟨⟨r, (V.valuation_le_one_iff r).mp hr⟩, rfl⟩ }
  have := hI.mem_of_integral hint
  exact (V.valuation_le_one_iff g).mp this

end ValRing

section PoleControl

variable {L F : Type*} [Field L] [Field F] [Algebra L F]

theorem mem_of_isIntegral_adjoin_of_mem (x f : F)
    (hf : IsIntegral (Algebra.adjoin L ({x} : Set F)) f)
    (V : ValuationSubring F) (hVL : ∀ a : L, algebraMap L F a ∈ V) (hxV : x ∈ V) : f ∈ V := by
  obtain ⟨q, hqm, hq0⟩ := hf
  have hSV : Algebra.adjoin L ({x} : Set F) ≤ ⟨V.toSubring.toSubsemiring, hVL⟩ :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hxV)
  refine mem_of_monic_of_coeff_mem V (q.map (algebraMap _ F)) (hqm.map _) (fun i => ?_) f ?_
  · rw [Polynomial.coeff_map]; exact hSV (q.coeff i).2
  · rwa [Polynomial.eval_map]

theorem aeval_mul_inv_pow_mem (V : ValuationSubring F) (hVL : ∀ a : L, algebraMap L F a ∈ V)
    {x : F} (hxinv : x⁻¹ ∈ V) (hx0 : x ≠ 0) (C : Polynomial L) {M : ℕ} (hM : C.natDegree ≤ M) :
    Polynomial.aeval x C * (x⁻¹) ^ M ∈ V := by
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_mul]
  refine sum_mem fun i hi => ?_
  have hi' : i ≤ M := by have := Finset.mem_range.mp hi; omega
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi'
  have : C.coeff i • x ^ i * x⁻¹ ^ (i + d) = algebraMap L F (C.coeff i) * x⁻¹ ^ d := by
    rw [Algebra.smul_def, mul_assoc, pow_add, ← mul_assoc (x ^ i), ← mul_pow,
      mul_inv_cancel₀ hx0, one_pow, one_mul]
  rw [this]
  exact mul_mem (hVL _) (pow_mem hxinv _)

theorem exists_forall_mul_inv_pow_mem (x f : F)
    (hf : IsIntegral (Algebra.adjoin L ({x} : Set F)) f) :
    ∃ m : ℕ, ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → x ∉ V →
      f * (x ^ m)⁻¹ ∈ V := by
  obtain ⟨q, hqm, hq0⟩ := hf
  have hrep : ∀ i, ∃ C : Polynomial L,
      Polynomial.aeval x C = ((q.coeff i : Algebra.adjoin L ({x} : Set F)) : F) := fun i => by
    have hmem : ((q.coeff i : Algebra.adjoin L ({x} : Set F)) : F) ∈
        (Polynomial.aeval x : Polynomial L →ₐ[L] F).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (q.coeff i).2
    obtain ⟨C, hC⟩ := hmem
    exact ⟨C, hC⟩
  choose C hC using hrep
  refine ⟨(Finset.range (q.natDegree + 1)).sup fun i => (C i).natDegree, fun V hVL hxV => ?_⟩
  set n := q.natDegree with hn
  set m := (Finset.range (n + 1)).sup fun i => (C i).natDegree with hm
  have hx0 : x ≠ 0 := by rintro rfl; exact hxV (zero_mem V)
  have hxinv : x⁻¹ ∈ V := (V.mem_or_inv_mem x).resolve_left hxV
  set q₁ := q.map (algebraMap (Algebra.adjoin L ({x} : Set F)) F) with hq₁
  have hq₁m : q₁.Monic := hqm.map _
  have hq₁n : q₁.natDegree = n := hqm.natDegree_map _
  have hroot : Polynomial.eval ((x⁻¹) ^ m * f) (q₁.scaleRoots ((x⁻¹) ^ m)) = 0 := by
    have h0 : Polynomial.eval₂ (RingHom.id F) f q₁ = 0 := by
      rw [hq₁, Polynomial.eval₂_map]; simpa using hq0
    simpa using Polynomial.scaleRoots_eval₂_eq_zero (RingHom.id F) (s := (x⁻¹) ^ m) h0
  have key : (x⁻¹) ^ m * f ∈ V := by
    refine mem_of_monic_of_coeff_mem V _ ((Polynomial.monic_scaleRoots_iff _).mpr hq₁m)
      (fun i => ?_) _ hroot
    rw [Polynomial.coeff_scaleRoots, hq₁n]
    by_cases hi : i < n
    · rw [hq₁, Polynomial.coeff_map, ← pow_mul]
      change ((q.coeff i : Algebra.adjoin L ({x} : Set F)) : F) * _ ∈ V
      rw [← hC i]
      have hdeg : (C i).natDegree ≤ m * (n - i) := by
        calc (C i).natDegree ≤ m :=
              Finset.le_sup (f := fun i => (C i).natDegree) (Finset.mem_range.mpr (by omega))
          _ ≤ m * (n - i) := Nat.le_mul_of_pos_right m (by omega)
      exact aeval_mul_inv_pow_mem V hVL hxinv hx0 (C i) hdeg
    · have hni : n - i = 0 := by omega
      rw [hni, pow_zero, mul_one]
      rcases (Nat.le_of_not_lt hi).lt_or_eq with h | h
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; exact zero_mem V
      · rw [← h, ← hq₁n, hq₁m.coeff_natDegree]; exact one_mem V
  rw [← inv_pow, mul_comm]
  exact key

end PoleControl

section Chart

variable {L : Type*} [Field L] (A : ValuationSubring L)
  {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]

theorem exists_monic_over_A_of_isIntegral_adjoin (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (f : R.integers) (hf : IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) (f : F)) :
    ∃ p : Polynomial (Polynomial A), p.Monic ∧
      p.eval₂ (Polynomial.eval₂RingHom ((algebraMap L F).comp A.subtype) (x : F)) f = 0 := by
  obtain ⟨m, hm⟩ := exists_forall_mul_inv_pow_mem (L := L) (x : F) (f : F) hf
  obtain ⟨p, hpm, -, hp⟩ :=
    R.exists_monic_coeff_natDegree_le_of_forall_valuationSubring A x hx (f : F) m
      (fun V hVL hxV => mem_of_isIntegral_adjoin_of_mem (L := L) (x : F) (f : F) hf V hVL hxV)
      hm
      (fun V hV => by
        rw [R.eq_integers_of_forall_mem_adjoin_iff A x hx hfin hdeg V hV]; exact f.2)
  exact ⟨p, hpm, hp⟩

end Chart

theorem finrank_adjoin_transport {K : Type*} [Field K]
    {E₁ E₂ : IntermediateField K (LaurentSeries K)} (h : E₁ = E₂) (z : LaurentSeries K)
    (hz₁ : z ∈ E₁) (hz₂ : z ∈ E₂) :
    Module.finrank (IntermediateField.adjoin K ({⟨z, hz₁⟩} : Set E₁)) E₁ =
      Module.finrank (IntermediateField.adjoin K ({⟨z, hz₂⟩} : Set E₂)) E₂ := by
  subst h; rfl

theorem eval₂_push {K : Type*} [Field K] (A : ValuationSubring K)
    (E : IntermediateField K (LaurentSeries K)) (t g : E) (p : Polynomial (Polynomial A))
    (h : p.eval₂ (Polynomial.eval₂RingHom ((algebraMap K E).comp A.subtype) t) g = 0) :
    p.eval₂ (Polynomial.eval₂RingHom ((algebraMap K (LaurentSeries K)).comp A.subtype)
      (t : LaurentSeries K)) (g : LaurentSeries K) = 0 := by
  have hval := congrArg (E.val : E →+* LaurentSeries K) h
  rw [map_zero, Polynomial.hom_eval₂] at hval
  have hcomp : (E.val : E →+* LaurentSeries K).comp
      (Polynomial.eval₂RingHom ((algebraMap K E).comp A.subtype) t) =
      Polynomial.eval₂RingHom ((algebraMap K (LaurentSeries K)).comp A.subtype)
        (t : LaurentSeries K) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp
    · simp
  rw [hcomp] at hval
  exact hval

theorem T_mem_gamma1 (M : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
  rw [CongruenceSubgroup.Gamma1_mem]
  simp [ModularGroup.coe_T]

theorem charP_residueField_of_liesOverPrime (A : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) [Fact p.Prime]
    (hA : A.LiesOverPrime p) : CharP (IsLocalRing.ResidueField ↥A) p := by
  rw [← ringChar.eq_iff]
  apply CharP.ringChar_of_prime_eq_zero (Fact.out : p.Prime)
  have h1 : ((p : ℕ) : IsLocalRing.ResidueField ↥A) = IsLocalRing.residue ↥A (p : ↥A) := by simp
  rw [h1, IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
  first | simpa using hA | exact hA

theorem jqModC_ne_zero' (K : Type*) [Field K] : jqModC K ≠ 0 := fun h =>
  transcendental_jqModC K (h ▸ isAlgebraic_zero)

end LiftingH

end

open LiftingH IsLocalRing in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem solution
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    (∀ h : LaurentSeries (ResidueField ↥A), h ∈ qExpFunctionFieldC (ResidueField ↥A) Γ →
      (∃ P : Polynomial (Polynomial (ResidueField ↥A)), P.Monic ∧
        Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A))) (jqModC (ResidueField ↥A)))
          h P = 0) →
      ∃ (f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) (x y : LaurentSeries ↥A),
        coeffMap (residue ↥A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x ∧
        coeffMap (residue ↥A) x = h * coeffMap (residue ↥A) y ∧
        ∃ P : Polynomial (Polynomial ↥A), P.Monic ∧
          Polynomial.eval₂ (Polynomial.eval₂RingHom
            ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
            (jqModC (AlgebraicClosure ℚ))) (f : LaurentSeries (AlgebraicClosure ℚ)) P = 0) ∧
    (∀ h : LaurentSeries (ResidueField ↥A), h ∈ qExpFunctionFieldC (ResidueField ↥A) Γ →
      (∃ P : Polynomial (Polynomial (ResidueField ↥A)), P.Monic ∧
        Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A))) (jqModC (ResidueField ↥A))⁻¹)
          h P = 0) →
      ∃ (f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) (x y : LaurentSeries ↥A),
        coeffMap (residue ↥A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x ∧
        coeffMap (residue ↥A) x = h * coeffMap (residue ↥A) y ∧
        ∃ P : Polynomial (Polynomial ↥A), P.Monic ∧
          Polynomial.eval₂ (Polynomial.eval₂RingHom
            ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
            (jqModC (AlgebraicClosure ℚ))⁻¹) (f : LaurentSeries (AlgebraicClosure ℚ)) P = 0) := by
  classical

  obtain ⟨H, rfl⟩ := CohCarrier.exists_eq_gammaH_of_gamma1_le_of_le_gamma0 M Γ hΓ₁ hΓ₀
  set L := AlgebraicClosure ℚ with hLdef
  set kA := ResidueField ↥A with hkAdef
  haveI : IsAlgClosed kA := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI : PerfectField kA := IsAlgClosed.perfectField kA
  haveI : CharP kA p := charP_residueField_of_liesOverPrime A p hA
  haveI hFI : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le hΓ₁
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := hΓ₁ (T_mem_gamma1 M)

  obtain ⟨R, hRi, hRii, hRiii⟩ :=
    ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq L A
      (CohCarrier.GammaH M H) hT

  have hjQ : jqModC ℚ ∈ qExpFunctionFieldC ℚ (CohCarrier.GammaH M H) :=
    IntermediateField.subset_adjoin _ _ (jqModC_mem_intFormRatiosC ℚ _)
  have hjL : jqModC L ∈ laurentBaseChange L (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := by
    have := coeffEmb_mem_laurentBaseChange L hjQ
    rwa [show coeffEmb L (jqModC ℚ) = jqModC L from coeffMap_jqModC _] at this
  have hyj : coeffMap A.subtype (jqModC ↥A) ∈ laurentBaseChange L (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := by
    rw [coeffMap_jqModC]; exact hjL
  obtain ⟨hxint, hxres⟩ := hRii (jqModC ↥A) hyj
  set x : R.integers := ⟨⟨_, hyj⟩, hxint⟩ with hxdef
  have hxF : ((x : laurentBaseChange L (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries L) = jqModC L :=
    coeffMap_jqModC _
  obtain ⟨xk, hxk, hxk_tr, hxk_fd, hxk_le⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField L A (CohCarrier.GammaH M H) hT
  have hresx : R.residue x = xk := by
    apply Subtype.ext
    change ((R.residue ⟨_, hxint⟩ : qExpFunctionFieldC kA (CohCarrier.GammaH M H)) : LaurentSeries kA) = _
    rw [hxres, coeffMap_jqModC, hxk]

  have hx : Transcendental kA (R.residue x) := by rw [hresx]; exact hxk_tr
  haveI : FiniteDimensional (IntermediateField.adjoin kA ({xk} : Set (qExpFunctionFieldC kA (CohCarrier.GammaH M H))))
      (qExpFunctionFieldC kA (CohCarrier.GammaH M H)) := hxk_fd
  have hfin : 0 < Module.finrank (IntermediateField.adjoin kA
      ({R.residue x} : Set (qExpFunctionFieldC kA (CohCarrier.GammaH M H)))) (qExpFunctionFieldC kA (CohCarrier.GammaH M H)) := by
    rw [hresx]; exact Module.finrank_pos
  have hxeq : (x : laurentBaseChange L (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) = ⟨jqModC L, hjL⟩ := Subtype.ext hxF
  have hdeg : Module.finrank (IntermediateField.adjoin L
      ({(x : laurentBaseChange L (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))} :
        Set (laurentBaseChange L (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))))
        (laurentBaseChange L (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) =
      Module.finrank (IntermediateField.adjoin kA
        ({R.residue x} : Set (qExpFunctionFieldC kA (CohCarrier.GammaH M H)))) (qExpFunctionFieldC kA (CohCarrier.GammaH M H)) := by
    rw [hresx, hxeq]
    exact le_antisymm
      (ModularCurve.finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd M H hpM A hA xk ⟨jqModC L, hjL⟩ hxk rfl)
      (hxk_le ⟨jqModC L, hjL⟩ rfl)
  have hgood : genusFF kA (qExpFunctionFieldC kA (CohCarrier.GammaH M H)) =
      genusFF L (laurentBaseChange L (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) :=
    ModularCurve.genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd M H hpM kA

  haveI : IsCurveOver kA (qExpFunctionFieldC kA (CohCarrier.GammaH M H)) :=
    AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental xk hxk_tr
  haveI : IsCurveOver L (laurentBaseChange L (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := by
    obtain ⟨t, ht, htfd⟩ :=
      ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L (CohCarrier.GammaH M H) hT
    haveI := htfd
    exact AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental t ht
  obtain ⟨E1, E2⟩ := R.residue_integralClosure_surjective_of_genusFF_eq A x hx hfin hdeg hgood

  have hresx0 : R.residue x ≠ 0 := by
    rw [hresx]; exact fun h => jqModC_ne_zero' kA (by rw [← hxk, h]; rfl)
  obtain ⟨ux, hux⟩ := R.isUnit_of_residue_ne_zero hresx0
  set x' : R.integers := ((ux⁻¹ : (R.integers)ˣ) : R.integers) with hx'def
  have hxx' : x * x' = 1 := by rw [← hux]; exact ux.mul_inv
  have hx'F : (x' : laurentBaseChange L (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) =
      (x : laurentBaseChange L (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))⁻¹ := by
    have h : (x : laurentBaseChange L (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) * x' = 1 := by
      have := congrArg (Subtype.val : R.integers → laurentBaseChange L (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) hxx'
      simpa using this
    exact eq_inv_of_mul_eq_one_right h
  have hx'L : ((x' : laurentBaseChange L (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries L) = (jqModC L)⁻¹ := by
    rw [hx'F, ← hxF]; push_cast; rfl
  have hresx' : R.residue x' = (R.residue x)⁻¹ := by
    have h := congrArg R.residue hxx'
    rw [map_mul, map_one] at h
    exact eq_inv_of_mul_eq_one_right h
  have hx2 : Transcendental kA (R.residue x') := by rw [hresx']; exact transcendental_inv hx
  have hfin2 : 0 < Module.finrank (IntermediateField.adjoin kA
      ({R.residue x'} : Set (qExpFunctionFieldC kA (CohCarrier.GammaH M H)))) (qExpFunctionFieldC kA (CohCarrier.GammaH M H)) := by
    rw [hresx', adjoin_simple_inv_eq]; exact hfin
  have hdeg2 : Module.finrank (IntermediateField.adjoin L
      ({(x' : laurentBaseChange L (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))} :
        Set (laurentBaseChange L (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))))
        (laurentBaseChange L (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) =
      Module.finrank (IntermediateField.adjoin kA
        ({R.residue x'} : Set (qExpFunctionFieldC kA (CohCarrier.GammaH M H)))) (qExpFunctionFieldC kA (CohCarrier.GammaH M H)) := by
    rw [hx'F, hresx', adjoin_simple_inv_eq, adjoin_simple_inv_eq]; exact hdeg

  have hread : ∀ (f : R.integers) (h : LaurentSeries kA),
      ((R.residue f : qExpFunctionFieldC kA (CohCarrier.GammaH M H)) : LaurentSeries kA) = h →
      ∃ x₀ y₀ : LaurentSeries ↥A, coeffMap (residue ↥A) y₀ ≠ 0 ∧
        ((f : laurentBaseChange L (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries L) *
            coeffMap A.subtype y₀ = coeffMap A.subtype x₀ ∧
        coeffMap (residue ↥A) x₀ = h * coeffMap (residue ↥A) y₀ := by
    intro f h hfh
    obtain ⟨x₀, y₀, hy₀, hxy⟩ := (hRi f).mp f.2
    refine ⟨x₀, y₀, hy₀, hxy, ?_⟩
    have := hRiii f f.2 x₀ y₀ hy₀ hxy
    rw [← this, ← hfh]
  refine ⟨fun h hh hP => ?_, fun h hh hP => ?_⟩
  ·
    obtain ⟨P, hPm, hPev⟩ := hP
    have hint : IsIntegral (Algebra.adjoin kA ({R.residue x} : Set (qExpFunctionFieldC kA (CohCarrier.GammaH M H))))
        (⟨h, hh⟩ : qExpFunctionFieldC kA (CohCarrier.GammaH M H)) := by
      rw [hresx]
      refine isIntegral_adjoin_of_eval₂ _ _ P hPm ?_
      rw [hxk]; exact hPev
    obtain ⟨f, hfi, hfres⟩ := E1 ⟨h, hh⟩ hint
    obtain ⟨q, hqm, hqev⟩ := exists_monic_over_A_of_isIntegral_adjoin A R x hx hfin hdeg f hfi
    have hqevL := eval₂_push A (laurentBaseChange L (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) _ _ q hqev
    rw [hxF] at hqevL
    obtain ⟨x₀, y₀, hy₀, hxy, hres⟩ := hread f h (by rw [hfres])
    exact ⟨(f : laurentBaseChange L (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))), x₀, y₀, hy₀, hxy, hres, q, hqm, hqevL⟩
  ·
    obtain ⟨P, hPm, hPev⟩ := hP
    have hint : IsIntegral (Algebra.adjoin kA ({(R.residue x)⁻¹} : Set (qExpFunctionFieldC kA (CohCarrier.GammaH M H))))
        (⟨h, hh⟩ : qExpFunctionFieldC kA (CohCarrier.GammaH M H)) := by
      rw [hresx]
      refine isIntegral_adjoin_of_eval₂ _ _ P hPm ?_
      have : ((xk⁻¹ : qExpFunctionFieldC kA (CohCarrier.GammaH M H)) : LaurentSeries kA) = (jqModC kA)⁻¹ := by
        push_cast; rw [hxk]
      rw [this]; exact hPev
    obtain ⟨f, hfi, hfres⟩ := E2 ⟨h, hh⟩ hint
    rw [← hx'F] at hfi
    obtain ⟨q, hqm, hqev⟩ := exists_monic_over_A_of_isIntegral_adjoin A R x' hx2 hfin2 hdeg2 f hfi
    have hqevL := eval₂_push A (laurentBaseChange L (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) _ _ q hqev
    rw [hx'L] at hqevL
    obtain ⟨x₀, y₀, hy₀, hxy, hres⟩ := hread f h (by rw [hfres])
    exact ⟨(f : laurentBaseChange L (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))), x₀, y₀, hy₀, hxy, hres, q, hqm, hqevL⟩

end S_ModularCurve_exists_gaussIntegral_lift_isIntegral_of_isIntegral_qExpFunctionFieldC_residueField_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_exists_gaussIntegral_lift_isIntegral_of_isIntegral_qExpFunctionFieldC_residueField_of_not_dvd (solution)
