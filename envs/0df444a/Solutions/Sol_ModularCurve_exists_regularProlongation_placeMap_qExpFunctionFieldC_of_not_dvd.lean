-- Prove2me | solution 1 for ModularCurve.exists_regularProlongation_placeMap_qExpFunctionFieldC_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/4c342b2b-2a80-5e8b-9863-4aced3127efb

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_XH
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_CohCarrier_exists_eq_gammaH_of_gamma1_le_of_le_gamma0
import Theorems.Thm_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_RegularProlongation_residue_integralClosure_surjective_of_genusFF_eq
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_placeMap_mapDomain_eq_ord_of_residue_integralClosure_surjective
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_regularProlongation_placeMap_qExpFunctionFieldC_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ"
p2m_attr_erase "simp" "ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open scoped MatrixGroups
p2m_open "ModularCurve P2MW.S_ModularCurve_exists_regularProlongation_placeMap_qExpFunctionFieldC_of_not_dvd.ModularCurve AlgebraicCurve~genus IsLocalRing CongruenceSubgroup"

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC intFormRatiosC_subset jq coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC map_jqModC Gamma1_le_GammaH GammaH_mono exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index transcendental_jqModC jqModC_mem_intFormRatiosC index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd"
namespace ProHProof
p2m_open "ModularCurve"

theorem mem_or_neg_mem_of_mem_sup_zpowers_neg_one {M : ℕ} (H : Subgroup (ZMod M)ˣ)
    {d : (ZMod M)ˣ} (hd : d ∈ H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)) : d ∈ H ∨ -d ∈ H := by
  let S : Subgroup (ZMod M)ˣ :=
    { carrier := {x | x = 1 ∨ x = -1}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro a b (rfl | rfl) (rfl | rfl) <;> simp
      inv_mem' := by
        rintro a (rfl | rfl) <;> simp }
  have hS : Subgroup.zpowers (-1 : (ZMod M)ˣ) ≤ S := by
    rw [Subgroup.zpowers_le]
    exact Or.inr rfl
  obtain ⟨h, hh, z, hz, rfl⟩ := Subgroup.mem_sup.mp hd
  rcases hS hz with hz1 | hz1
  · left; rw [hz1, mul_one]; exact hh
  · right; rw [hz1]; simpa using hh

theorem neg_mem_Gamma0 {M : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) : -γ ∈ Gamma0 M := by
  have := Gamma0_mem.mp hγ
  rw [Gamma0_mem]
  simp [Matrix.SpecialLinearGroup.coe_neg, this]

theorem gamma0Units_neg {M : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    CohCarrier.gamma0Units M ⟨-γ, neg_mem_Gamma0 hγ⟩ = -CohCarrier.gamma0Units M ⟨γ, hγ⟩ := by
  ext
  simp [CohCarrier.gamma0Units, Gamma0Map, Matrix.SpecialLinearGroup.coe_neg]

theorem mem_or_neg_mem_gammaH_of_mem_gammaH_sup {M : ℕ} (H : Subgroup (ZMod M)ˣ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ))) :
    γ ∈ CohCarrier.GammaH M H ∨ -γ ∈ CohCarrier.GammaH M H := by
  obtain ⟨hγ0, hd⟩ := CohCarrier.mem_GammaH_iff.mp hγ
  rcases mem_or_neg_mem_of_mem_sup_zpowers_neg_one H hd with h | h
  · exact Or.inl (CohCarrier.mem_GammaH_iff.mpr ⟨hγ0, h⟩)
  · exact Or.inr (CohCarrier.mem_GammaH_iff.mpr ⟨neg_mem_Gamma0 hγ0, by rw [gamma0Units_neg hγ0]; exact h⟩)

theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ Gamma1 M := by
  rw [Gamma1_mem]; simp [ModularGroup.coe_T]

local notation "ℚbar" => AlgebraicClosure ℚ

theorem main (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (A : ValuationSubring ℚbar) (hA : A.LiesOverPrime p) [IsAlgClosed (ResidueField ↥A)] :
    ∃ (R : RegularProlongation A ↥(laurentBaseChange ℚbar (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
          ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H)))
      (r : Place ℚbar ↥(laurentBaseChange ℚbar (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
          → Place (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H))),
      (∀ (y : LaurentSeries ↥A)
          (hy : coeffMap A.subtype y ∈ laurentBaseChange ℚbar (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))),
        ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : ↥(laurentBaseChange ℚbar (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ R.integers,
          ((R.residue ⟨_, hint⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H))) : LaurentSeries (ResidueField ↥A))
            = coeffMap (residue ↥A) y)
      ∧ ∀ f : R.integers, R.residue f ≠ 0 →
          ∀ D : Divisor ℚbar ↥(laurentBaseChange ℚbar (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))),
            (∀ P, D P = P.ord (f : ↥(laurentBaseChange ℚbar (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) →
          ∀ Q, Finsupp.mapDomain r D Q = Q.ord (R.residue f) := by
  set Γ := CohCarrier.GammaH M H with hΓdef
  set κ := ResidueField ↥A with hκ
  haveI : CharP κ p := ValuationSubring.residueField_charP_of_liesOverPrime A (Fact.out : p.Prime) hA
  haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)
  have hT : ModularGroup.T ∈ Γ := Gamma1_le_GammaH M H (T_mem_Gamma1 M)

  obtain ⟨R, -, hspec⟩ := exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC ℚbar A Γ hT

  have hjA : coeffMap A.subtype (jqModC ↥A) = coeffEmb ℚbar (jqModC ℚ) := by
    show (jqModC ↥A).map A.subtype = coeffMap (algebraMap ℚ ℚbar) (jqModC ℚ)
    rw [map_jqModC]
    show jqModC ℚbar = (jqModC ℚ).map (algebraMap ℚ ℚbar)
    rw [map_jqModC]
  have hjmem : jqModC ℚ ∈ qExpFunctionFieldC ℚ Γ := intFormRatiosC_subset ℚ Γ (jqModC_mem_intFormRatiosC ℚ Γ)
  have hy : coeffMap A.subtype (jqModC ↥A) ∈ laurentBaseChange ℚbar (qExpFunctionFieldC ℚ Γ) := by
    rw [hjA]; exact coeffEmb_mem_laurentBaseChange ℚbar hjmem
  obtain ⟨hint, hres⟩ := hspec (jqModC ↥A) hy
  set x : R.integers := ⟨_, hint⟩ with hxdef
  have hresj : ((R.residue x : ↥(qExpFunctionFieldC κ Γ)) : LaurentSeries κ) = jqModC κ := by
    rw [hres]
    show (jqModC ↥A).map (residue ↥A) = jqModC κ
    rw [map_jqModC]
  have hyj : ((x : ↥(laurentBaseChange ℚbar (qExpFunctionFieldC ℚ Γ))) : LaurentSeries ℚbar) = jqModC ℚbar := by
    show coeffMap A.subtype (jqModC ↥A) = jqModC ℚbar
    show (jqModC ↥A).map A.subtype = jqModC ℚbar
    rw [map_jqModC]

  obtain ⟨xb, hxb, htrb, hfdb, hleb⟩ :=
    exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField ℚbar A Γ hT
  have hxres : R.residue x = xb := Subtype.ext (hresj.trans hxb.symm)
  haveI := hfdb
  have htrx : Transcendental κ (R.residue x) := by rw [hxres]; exact htrb

  have htr0 : Transcendental ℚbar (x : ↥(laurentBaseChange ℚbar (qExpFunctionFieldC ℚ Γ))) := by
    intro halg
    apply transcendental_jqModC ℚbar
    have h := halg.algHom (IntermediateField.val (laurentBaseChange ℚbar (qExpFunctionFieldC ℚ Γ)))
    rw [← hyj]
    exact h
  have hyj' : ((x : ↥(laurentBaseChange ℚbar (qExpFunctionFieldC ℚ Γ))) : LaurentSeries ℚbar) = coeffEmb ℚbar jq := by
    rw [hyj]
    show jqModC ℚbar = coeffMap (algebraMap ℚ ℚbar) (jqModC ℚ)
    show jqModC ℚbar = (jqModC ℚ).map (algebraMap ℚ ℚbar)
    rw [map_jqModC]
  haveI : FiniteDimensional ↥(IntermediateField.adjoin ℚbar
      ({(x : ↥(laurentBaseChange ℚbar (qExpFunctionFieldC ℚ Γ)))} : Set ↥(laurentBaseChange ℚbar (qExpFunctionFieldC ℚ Γ))))
      ↥(laurentBaseChange ℚbar (qExpFunctionFieldC ℚ Γ)) :=
    finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange Γ hT ℚbar
      (laurentBaseChange ℚbar (qExpFunctionFieldC ℚ Γ)) rfl _ hyj'

  haveI : IsCurveOver κ ↥(qExpFunctionFieldC κ Γ) := isCurveOver_of_isAlgClosed_of_transcendental xb htrb
  haveI : IsCurveOver ℚbar ↥(laurentBaseChange ℚbar (qExpFunctionFieldC ℚ Γ)) :=
    isCurveOver_of_isAlgClosed_of_transcendental _ htr0

  have hfin : 0 < Module.finrank ↥(IntermediateField.adjoin κ ({R.residue x} : Set ↥(qExpFunctionFieldC κ Γ)))
      ↥(qExpFunctionFieldC κ Γ) := by
    rw [hxres]; exact Module.finrank_pos
  have hneg : ∀ γ ∈ CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)), γ ∈ Γ ∨ -γ ∈ Γ :=
    fun γ hγ => mem_or_neg_mem_gammaH_of_mem_gammaH_sup H hγ
  have hle1 := finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index ℚbar Γ hT
    (CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ))) (GammaH_mono le_sup_left) hneg
    (x : ↥(laurentBaseChange ℚbar (qExpFunctionFieldC ℚ Γ))) hyj
  have hle2 := index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField M H hpM A hA xb hxb
  have hle3 := hleb (x : ↥(laurentBaseChange ℚbar (qExpFunctionFieldC ℚ Γ))) hyj
  have hdeg : Module.finrank ↥(IntermediateField.adjoin ℚbar ({(x : ↥(laurentBaseChange ℚbar (qExpFunctionFieldC ℚ Γ)))} :
        Set ↥(laurentBaseChange ℚbar (qExpFunctionFieldC ℚ Γ)))) ↥(laurentBaseChange ℚbar (qExpFunctionFieldC ℚ Γ)) =
      Module.finrank ↥(IntermediateField.adjoin κ ({R.residue x} : Set ↥(qExpFunctionFieldC κ Γ))) ↥(qExpFunctionFieldC κ Γ) := by
    rw [hxres]
    exact le_antisymm (hle1.trans hle2) hle3

  have hgood : genusFF κ ↥(qExpFunctionFieldC κ Γ) = genusFF ℚbar ↥(laurentBaseChange ℚbar (qExpFunctionFieldC ℚ Γ)) :=
    genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd M H hpM κ

  have hchart := RegularProlongation.residue_integralClosure_surjective_of_genusFF_eq A R x htrx hfin hdeg hgood
  obtain ⟨r, hord⟩ :=
    RegularProlongation.exists_placeMap_mapDomain_eq_ord_of_residue_integralClosure_surjective A R x htrx hfin hdeg hchart
  exact ⟨R, r, hspec, hord⟩

end ModularCurve.ProHProof

p2m_open "AlgebraicCurve~genus" in open _root_.ModularCurve _root_.P2MW.S_ModularCurve_exists_regularProlongation_placeMap_qExpFunctionFieldC_of_not_dvd.ModularCurve IsLocalRing in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [IsAlgClosed (ResidueField ↥A)] :
    ∃ (R : RegularProlongation A ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))
          ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))
      (r : Place (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))
          → Place (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)),
      (∀ (y : LaurentSeries ↥A)
          (hy : coeffMap A.subtype y ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)),
        ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) ∈ R.integers,
          ((R.residue ⟨_, hint⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) : LaurentSeries (ResidueField ↥A))
            = coeffMap (residue ↥A) y)
      ∧ ∀ f : R.integers, R.residue f ≠ 0 →
          ∀ D : Divisor (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)),
            (∀ P, D P = P.ord (f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)))) →
          ∀ Q, Finsupp.mapDomain r D Q = Q.ord (R.residue f) := by
  obtain ⟨H, rfl⟩ := CohCarrier.exists_eq_gammaH_of_gamma1_le_of_le_gamma0 M Γ hΓ₁ hΓ₀
  exact ModularCurve.ProHProof.main M H p hpM A hA

end S_ModularCurve_exists_regularProlongation_placeMap_qExpFunctionFieldC_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_exists_regularProlongation_placeMap_qExpFunctionFieldC_of_not_dvd (solution)
