-- Prove2me | solution 1 for ModularCurve.exists_isPlaceReductionQExpModL_chartCentre_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/120be399-3bdc-52d0-9552-4e9fbe193d0a

import Mathlib
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_XH
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_AlgebraicCurve_RegularProlongation_existsUnique_place_forall_residue_sub_mem_nonunits
import Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_ord_eq_ord_residue_of_residue_integralClosure_surjective
import Theorems.Thm_AlgebraicCurve_RegularProlongation_residue_integralClosure_surjective_of_genusFF_eq
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
import Theorems.Thm_CohCarrier_exists_eq_gammaH_of_gamma1_le_of_le_gamma0
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isPlaceReductionQExpModL_chartCentre_of_not_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP"
p2m_attr_erase "simp" "ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "AlgebraicCurve~genus ModularCurve IsLocalRing"

namespace AgreeR
namespace Deuring

section abstract

variable {ι κ : Type*}

theorem exists_map_of_two_charts (Dom₁ Dom₂ : ι → Prop) (Red₁ Red₂ : ι → κ → Prop)
    (Fin : κ → Prop)
    (hcover : ∀ P, Dom₁ P ∨ Dom₂ P)
    (E₁ : ∀ P, Dom₁ P → ∃! Q, Red₁ P Q) (E₂ : ∀ P, Dom₂ P → ∃! Q, Red₂ P Q)
    (hfin₁ : ∀ P Q, Dom₁ P → Red₁ P Q → Fin Q)
    (hinf₂ : ∀ P Q, ¬ Dom₁ P → Dom₂ P → Red₂ P Q → ¬ Fin Q)
    (hboth : ∀ P Q, Dom₁ P → Dom₂ P → Red₂ P Q → Fin Q) :
    ∃ r : ι → κ, (∀ P Q, Fin Q → (r P = Q ↔ Dom₁ P ∧ Red₁ P Q)) ∧
      (∀ P Q, ¬ Fin Q → (r P = Q ↔ Dom₂ P ∧ Red₂ P Q)) ∧
      (∀ P, Dom₁ P → Red₁ P (r P)) ∧ (∀ P, ¬ Dom₁ P → Red₂ P (r P)) := by
  classical
  let r : ι → κ := fun P =>
    if h : Dom₁ P then (E₁ P h).exists.choose
    else (E₂ P ((hcover P).resolve_left h)).exists.choose
  have hr₁ : ∀ P (h : Dom₁ P), Red₁ P (r P) := fun P h => by
    simp only [r, dif_pos h]
    exact (E₁ P h).exists.choose_spec
  have hr₂ : ∀ P (h : ¬ Dom₁ P), Red₂ P (r P) := fun P h => by
    simp only [r, dif_neg h]
    exact (E₂ P ((hcover P).resolve_left h)).exists.choose_spec
  refine ⟨r, fun P Q hQ => ⟨fun hPQ => ?_, fun ⟨hd, hred⟩ => ?_⟩,
    fun P Q hQ => ⟨fun hPQ => ?_, fun ⟨hd, hred⟩ => ?_⟩, hr₁, hr₂⟩
  · by_cases h : Dom₁ P
    · exact ⟨h, hPQ ▸ hr₁ P h⟩
    · exact absurd hQ (hinf₂ P Q h ((hcover P).resolve_left h) (hPQ ▸ hr₂ P h))
  · exact (E₁ P hd).unique (hr₁ P hd) hred
  · by_cases h : Dom₁ P
    · exact absurd (hfin₁ P _ h (hr₁ P h)) (hPQ ▸ hQ)
    · exact ⟨(hcover P).resolve_left h, hPQ ▸ hr₂ P h⟩
  · by_cases h : Dom₁ P
    · exact absurd (hboth P Q h hd hred) hQ
    · exact (E₂ P ((hcover P).resolve_left h)).unique (hr₂ P h) hred

theorem mapDomain_eq_sum_filter [DecidableEq κ] (r : ι → κ) (D : ι →₀ ℤ) (Q : κ) :
    Finsupp.mapDomain r D Q = ∑ P ∈ D.support with r P = Q, D P := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun P _ => ?_
  simp only [Finsupp.single_apply]

theorem mapDomain_eq_of_chart (r : ι → κ) (D : ι →₀ ℤ) (Q : κ) (Dom : ι → Prop)
    (Red : ι → κ → Prop) (hfib : ∀ P, r P = Q ↔ Dom P ∧ Red P Q) (n : ℤ)
    (hM : ∀ T : Finset ι, (∀ P, P ∈ T ↔ (D P ≠ 0 ∧ Dom P ∧ Red P Q)) → ∑ P ∈ T, D P = n) :
    Finsupp.mapDomain r D Q = n := by
  classical
  rw [mapDomain_eq_sum_filter]
  refine hM _ fun P => ?_
  rw [Finset.mem_filter, Finsupp.mem_support_iff, hfib]

end abstract

section places

variable {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]

theorem valuation_algebraMap_eq_one (P : Place L F) {c : L} (hc : c ≠ 0) :
    P.toValuationSubring.valuation (algebraMap L F c) = 1 := by
  let u : (P.toValuationSubring)ˣ :=
    ⟨algebraMap L P.toValuationSubring c, algebraMap L P.toValuationSubring c⁻¹,
      by rw [← map_mul, mul_inv_cancel₀ hc, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hc, map_one]⟩
  exact P.toValuationSubring.valuation_unit u

theorem const_unique (P : Place L F) {h : F} {c c' : L}
    (hc : h - algebraMap L F c ∈ P.toValuationSubring.nonunits)
    (hc' : h - algebraMap L F c' ∈ P.toValuationSubring.nonunits) : c = c' := by
  by_contra hne
  rw [ValuationSubring.mem_nonunits_iff] at hc hc'
  have hlt : P.toValuationSubring.valuation (algebraMap L F (c' - c)) < 1 := by
    have : algebraMap L F (c' - c) = (h - algebraMap L F c) + -(h - algebraMap L F c') := by
      rw [map_sub]; ring
    rw [this]
    refine Valuation.map_add_lt _ hc ?_
    rwa [Valuation.map_neg]
  rw [valuation_algebraMap_eq_one P (sub_ne_zero.mpr (Ne.symm hne))] at hlt
  exact lt_irrefl _ hlt

theorem inv_sub_inv_mem_nonunits (P : Place L F) {x : F} {c : L} (hc0 : c ≠ 0)
    (hc : x - algebraMap L F c ∈ P.toValuationSubring.nonunits) :
    x⁻¹ - algebraMap L F c⁻¹ ∈ P.toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hc ⊢
  have hvc : P.toValuationSubring.valuation (algebraMap L F c) = 1 :=
    valuation_algebraMap_eq_one P hc0
  have hvx : P.toValuationSubring.valuation x = 1 := by
    have := Valuation.map_add_eq_of_lt_left P.toValuationSubring.valuation
      (x := algebraMap L F c) (y := x - algebraMap L F c) (by rwa [hvc])
    rwa [add_sub_cancel, hvc] at this
  have hx0 : x ≠ 0 := by rintro rfl; rw [map_zero] at hvx; exact zero_ne_one hvx
  have hc0' : algebraMap L F c ≠ 0 := by simpa using hc0
  have heq : x⁻¹ - algebraMap L F c⁻¹ =
      -(x⁻¹ * (algebraMap L F c)⁻¹ * (x - algebraMap L F c)) := by
    rw [map_inv₀]; field_simp; ring
  rw [heq, Valuation.map_neg, map_mul, map_mul, map_inv₀, map_inv₀, hvx, hvc]
  simpa using hc

theorem exists_sub_algebraMap_mem_nonunits [IsAlgClosed L] [IsCurveOver L F] (P : Place L F)
    {h : F} (hh : h ∈ P.toValuationSubring) :
    ∃ c : L, h - algebraMap L F c ∈ P.toValuationSubring.nonunits := by
  haveI : Module.Finite L P.ResidueField := IsCurveOver.finiteResidue P
  haveI : Algebra.IsIntegral L P.ResidueField := Algebra.IsIntegral.of_finite L P.ResidueField
  obtain ⟨c, hc⟩ :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := L) (K := P.ResidueField)).2
      (IsLocalRing.residue P.toValuationSubring ⟨h, hh⟩)
  refine ⟨c, ?_⟩
  have hmem : (⟨h, hh⟩ : P.toValuationSubring) - algebraMap L P.toValuationSubring c ∈
      maximalIdeal P.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hc]
    exact (IsScalarTower.algebraMap_apply L P.toValuationSubring P.ResidueField c).symm
  have := ValuationSubring.coe_mem_nonunits_iff.mpr hmem
  simpa using this

theorem exists_inv_sub_mem_nonunits [IsAlgClosed L] [IsCurveOver L F] (A : ValuationSubring L)
    (P : Place L F) (x : F)
    (hnot : ¬ ∃ a : A, x - algebraMap L F a ∈ P.toValuationSubring.nonunits) :
    ∃ a : A, x⁻¹ - algebraMap L F a ∈ P.toValuationSubring.nonunits := by
  by_cases hxV : x ∈ P.toValuationSubring
  · obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_nonunits P hxV
    have hcA : c ∉ A := fun h => hnot ⟨⟨c, h⟩, hc⟩
    have hc0 : c ≠ 0 := by rintro rfl; exact hcA A.zero_mem
    have hcinv : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
    exact ⟨⟨c⁻¹, hcinv⟩, inv_sub_inv_mem_nonunits P hc0 hc⟩
  · refine ⟨0, ?_⟩
    have hxinv : x⁻¹ ∈ P.toValuationSubring :=
      (P.toValuationSubring.mem_or_inv_mem x).resolve_left hxV
    rw [show ((0 : A) : L) = 0 from rfl, map_zero, sub_zero, ValuationSubring.mem_nonunits_iff]
    rw [← P.toValuationSubring.valuation_le_one_iff, not_le] at hxV
    have hx0 : x ≠ 0 := by rintro rfl; simp at hxV
    rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hxV

theorem inv_const_eq (P : Place L F) {x : F} (hx0 : x ≠ 0) {a a' : L}
    (ha : x - algebraMap L F a ∈ P.toValuationSubring.nonunits)
    (ha' : x⁻¹ - algebraMap L F a' ∈ P.toValuationSubring.nonunits) : a ≠ 0 ∧ a' = a⁻¹ := by
  have hmem : x⁻¹ ∈ P.toValuationSubring := by
    have h1 : x⁻¹ - algebraMap L F a' ∈ P.toValuationSubring :=
      ValuationSubring.nonunits_subset ha'
    have h2 : algebraMap L F a' ∈ P.toValuationSubring := P.algebraMap_mem' a'
    simpa using add_mem h1 h2
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, sub_zero, ValuationSubring.mem_nonunits_iff] at ha
    rw [← P.toValuationSubring.valuation_le_one_iff, map_inv₀] at hmem
    have hvx0 : 0 < P.toValuationSubring.valuation x :=
      zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx0)
    exact absurd hmem (not_le.mpr ((one_lt_inv₀ hvx0).mpr ha))
  exact ⟨ha0, const_unique P ha' (inv_sub_inv_mem_nonunits P ha0 ha)⟩

theorem ord_pos_of_mem_nonunits (P : Place L F) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ P.toValuationSubring.nonunits) : 0 < P.ord f := by
  by_contra hle
  push Not at hle
  have hinv : f⁻¹ ∈ P.toValuationSubring := by
    rw [P.mem_iff_ord_nonneg (inv_ne_zero hf0), P.ord_inv]; omega
  rw [ValuationSubring.mem_nonunits_iff] at hf
  rw [← P.toValuationSubring.valuation_le_one_iff, map_inv₀] at hinv
  have hv0 : 0 < P.toValuationSubring.valuation f :=
    zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hf0)
  exact absurd hf (not_lt.mpr ((inv_le_one₀ hv0).mp hinv))

theorem mem_nonunits_of_ord_pos (P : Place L F) {f : F} (hf0 : f ≠ 0) (h : 0 < P.ord f) :
    f ∈ P.toValuationSubring.nonunits := by
  have hinv : f⁻¹ ∉ P.toValuationSubring := by
    rw [P.mem_iff_ord_nonneg (inv_ne_zero hf0), P.ord_inv]; omega
  rw [← P.toValuationSubring.valuation_le_one_iff, map_inv₀, not_le] at hinv
  rw [ValuationSubring.mem_nonunits_iff]
  have hv0 : 0 < P.toValuationSubring.valuation f :=
    zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hf0)
  exact (one_lt_inv₀ hv0).mp hinv

end places

theorem inv_adjoin_eq {K E : Type*} [Field K] [Field E] [Algebra K E] (y : E) :
    IntermediateField.adjoin K ({y⁻¹} : Set E) = IntermediateField.adjoin K ({y} : Set E) := by
  apply le_antisymm
  · exact IntermediateField.adjoin_simple_le_iff.mpr
      (IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self K y))
  · refine IntermediateField.adjoin_simple_le_iff.mpr ?_
    have := IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self K y⁻¹)
    rwa [inv_inv] at this

section main

variable {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]

def Dom (P : Place L F) (y : F) : Prop :=
  ∃ a : A, y - algebraMap L F a ∈ P.toValuationSubring.nonunits

def Red (R : RegularProlongation A F Fbar) (y : F) (P : Place L F)
    (Q : Place (IsLocalRing.ResidueField A) Fbar) : Prop :=
  ∀ h : R.integers, IsIntegral (Algebra.adjoin L {y}) (h : F) →
    ∀ a : A, (h : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits →
      R.residue h - algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a) ∈
        Q.toValuationSubring.nonunits

variable {A}

theorem isIntegral_self (y : F) : IsIntegral (Algebra.adjoin L {y}) y :=
  isIntegral_algebraMap (x := (⟨y, Algebra.self_mem_adjoin_singleton L y⟩ : Algebra.adjoin L {y}))

theorem residue_mem_of_red (R : RegularProlongation A F Fbar) (y : R.integers) (P : Place L F)
    (Q : Place (IsLocalRing.ResidueField A) Fbar) (hd : Dom A P (y : F)) (hred : Red A R y P Q) :
    R.residue y ∈ Q.toValuationSubring := by
  obtain ⟨a, ha⟩ := hd
  have h1 := ValuationSubring.nonunits_subset (hred y (isIntegral_self (y : F)) a ha)
  have h2 := Q.algebraMap_mem' (IsLocalRing.residue A a)
  simpa using add_mem h1 h2

variable [IsAlgClosed L] [IsCurveOver L F] [IsCurveOver (IsLocalRing.ResidueField A) Fbar]

theorem red_of_red_of_dom_dom (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (xi : R.integers) (hxxi : x * xi = 1)
    (P : Place L F) (Q : Place (IsLocalRing.ResidueField A) Fbar)
    (hd : Dom A P (x : F)) (hd' : Dom A P (xi : F)) (hred : Red A R (x : F) P Q) :
    Red A R (xi : F) P Q := by
  classical
  intro h hh a ha

  have hx0 : R.residue x ≠ 0 := fun e => hx (e ▸ isAlgebraic_zero)
  have hxF0 : (x : F) ≠ 0 := by
    intro e
    exact hx0 (by rw [show x = 0 from Subtype.ext e, map_zero])
  have hxiF : (xi : F) = (x : F)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by exact_mod_cast congrArg Subtype.val hxxi)

  have haO : algebraMap L F a ∈ R.integers := (R.algebraMap_mem_iff a).mpr a.2
  set g : R.integers := h - ⟨algebraMap L F a, haO⟩ with hg_def
  have hgF : (g : F) = (h : F) - algebraMap L F a := rfl
  have hgres : R.residue g =
      R.residue h - algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a) := by
    rw [hg_def, map_sub, R.residue_algebraMap]
  rw [← hgres]
  by_cases hg0 : R.residue g = 0
  · rw [hg0, ValuationSubring.mem_nonunits_iff, map_zero]; exact zero_lt_one
  have hgF0 : (g : F) ≠ 0 := fun e => hg0 (by rw [show g = 0 from Subtype.ext e, map_zero])

  obtain ⟨a₀, ha₀⟩ := hd
  obtain ⟨b₀, hb₀⟩ := hd'
  obtain ⟨ha₀0, hb₀eq⟩ := inv_const_eq P hxF0 ha₀ (hxiF ▸ hb₀)
  have hunit : IsUnit a₀ := by
    refine isUnit_iff_exists_inv.mpr ⟨b₀, Subtype.ext ?_⟩
    show ((a₀ : A) : L) * ((b₀ : A) : L) = 1
    rw [hb₀eq, mul_inv_cancel₀ ha₀0]
  have hres₀ : IsLocalRing.residue A a₀ ≠ 0 := fun h0 =>
    mem_nonunits_iff.mp
      ((IsLocalRing.mem_maximalIdeal _).mp ((IsLocalRing.residue_eq_zero_iff _).mp h0)) hunit

  have hxQ : R.residue x - algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a₀) ∈
      Q.toValuationSubring.nonunits :=
    hred x (isIntegral_self (x : F)) a₀ ha₀
  have hQfin : R.residue x ∈ Q.toValuationSubring := residue_mem_of_red R x P Q ⟨a₀, ha₀⟩ hred

  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (g : F) hgF0
  let T : Finset (Place L F) :=
    D.support.filter (fun P' => Dom A P' (x : F) ∧ Red A R (x : F) P' Q)
  have hT : ∀ P', P' ∈ T ↔ (D P' ≠ 0 ∧ Dom A P' (x : F) ∧ Red A R (x : F) P' Q) := fun P' => by
    simp only [T, Finset.mem_filter, Finsupp.mem_support_iff]
  have hsum := RegularProlongation.sum_ord_eq_ord_residue_of_residue_integralClosure_surjective
      A R x hx hfin hdeg hchart g hg0 Q hQfin D hD T hT

  have hnonneg : ∀ P' ∈ T, 0 ≤ D P' := by
    intro P' hP'
    obtain ⟨-, ⟨a', ha'⟩, hred'⟩ := (hT P').mp hP'
    have hxQ' := hred' x (isIntegral_self (x : F)) a' ha'
    have heq : IsLocalRing.residue A a' = IsLocalRing.residue A a₀ := const_unique Q hxQ' hxQ
    have ha'0 : ((a' : A) : L) ≠ 0 := by
      intro h0
      have : a' = 0 := Subtype.ext h0
      rw [this, map_zero] at heq
      exact hres₀ heq.symm
    have hxiP' : (xi : F) ∈ P'.toValuationSubring := by
      have h1 := ValuationSubring.nonunits_subset (inv_sub_inv_mem_nonunits P' ha'0 ha')
      have h2 := P'.algebraMap_mem' ((a' : A) : L)⁻¹
      rw [hxiF]; simpa using add_mem h1 h2
    have hhP' : (h : F) ∈ P'.toValuationSubring :=
      P'.mem_toValuationSubring_of_isIntegral_adjoin hxiP' hh
    have hgP' : (g : F) ∈ P'.toValuationSubring := by
      rw [hgF]; exact sub_mem hhP' (P'.algebraMap_mem' _)
    rw [hD P']; exact (P'.mem_iff_ord_nonneg hgF0).mp hgP'

  have hgP : 0 < P.ord (g : F) := ord_pos_of_mem_nonunits P hgF0 (by rw [hgF]; exact ha)
  have hPT : P ∈ T := by
    rw [hT]
    exact ⟨by rw [hD P]; exact hgP.ne', ⟨a₀, ha₀⟩, hred⟩
  have hpos : 0 < Q.ord (R.residue g) := by
    rw [← hsum]
    calc (0 : ℤ) < D P := by rw [hD P]; exact hgP
      _ ≤ ∑ P' ∈ T, D P' := Finset.single_le_sum hnonneg hPT
  exact mem_nonunits_of_ord_pos Q hg0 hpos

theorem main (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart :
      (∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h) ∧
      (∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {(R.residue x)⁻¹}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)⁻¹}) (f : F) ∧ R.residue f = h)) :
    ∃ r : Place L F → Place (IsLocalRing.ResidueField A) Fbar,
      (∀ f : R.integers, R.residue f ≠ 0 → ∀ D : Divisor L F, (∀ P, D P = P.ord (f : F)) →
        ∀ Q, Finsupp.mapDomain r D Q = Q.ord (R.residue f)) ∧
      (∀ P, Dom A P (x : F) → Red A R (x : F) P (r P)) ∧
      (∀ P, Dom A P (x : F)⁻¹ → Red A R (x : F)⁻¹ P (r P)) := by
  classical

  have hx0 : R.residue x ≠ 0 := fun h => hx (h ▸ isAlgebraic_zero)
  obtain ⟨ux, hux⟩ := R.isUnit_of_residue_ne_zero hx0
  have hxF0 : (x : F) ≠ 0 := by
    intro h
    exact hx0 (by rw [show x = 0 from Subtype.ext h, map_zero])
  obtain ⟨xi, hxxi⟩ : ∃ xi : R.integers, x * xi = 1 := ⟨(ux⁻¹ : R.integersˣ), hux ▸ ux.mul_inv⟩
  have hxiF : (xi : F) = (x : F)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by exact_mod_cast congrArg Subtype.val hxxi)
  have hxires : R.residue xi = (R.residue x)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by rw [← map_mul, hxxi, map_one])
  have hxiF0 : (xi : F) ≠ 0 := by rw [hxiF]; exact inv_ne_zero hxF0
  have hx' : Transcendental (IsLocalRing.ResidueField A) (R.residue xi) := by
    rw [hxires]; exact fun h => hx (IsAlgebraic.inv_iff.mp h)
  have hadjK : IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue xi} : Set Fbar) =
      IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar) := by
    rw [hxires]; exact inv_adjoin_eq _
  have hadjL : IntermediateField.adjoin L ({(xi : F)} : Set F) =
      IntermediateField.adjoin L ({(x : F)} : Set F) := by
    rw [hxiF]; exact inv_adjoin_eq _
  have hfin' : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue xi} : Set Fbar)) Fbar := by
    rw [hadjK]; exact hfin
  have hdeg' : Module.finrank (IntermediateField.adjoin L ({(xi : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue xi} : Set Fbar))
          Fbar := by
    rw [hadjK, hadjL]; exact hdeg
  have hchart' : ∀ h : Fbar,
      IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue xi}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(xi : F)}) (f : F) ∧ R.residue f = h := by
    rw [hxires, hxiF]; exact hchart.2

  have hcover : ∀ P : Place L F, Dom A P (x : F) ∨ Dom A P (xi : F) := fun P =>
    or_iff_not_imp_left.mpr fun h => by
      rw [hxiF]; exact exists_inv_sub_mem_nonunits A P (x : F) h
  have E₁ : ∀ P : Place L F, Dom A P (x : F) → ∃! Q, Red A R (x : F) P Q := fun P hP =>
    RegularProlongation.existsUnique_place_forall_residue_sub_mem_nonunits
      A R x hx hfin hdeg hchart.1 P hP
  have E₂ : ∀ P : Place L F, Dom A P (xi : F) → ∃! Q, Red A R (xi : F) P Q := fun P hP =>
    RegularProlongation.existsUnique_place_forall_residue_sub_mem_nonunits
      A R xi hx' hfin' hdeg' hchart' P hP
  have hfin₁ : ∀ P Q, Dom A P (x : F) → Red A R (x : F) P Q →
      R.residue x ∈ Q.toValuationSubring := fun P Q hd hred =>
    residue_mem_of_red R x P Q hd hred
  have hinf₂ : ∀ P Q, ¬ Dom A P (x : F) → Dom A P (xi : F) → Red A R (xi : F) P Q →
      R.residue x ∉ Q.toValuationSubring := by
    intro P Q hnd hd hred hfinQ
    obtain ⟨a', ha'⟩ := hd
    have hres := hred xi (isIntegral_self (xi : F)) a' ha'
    by_cases hunit : IsUnit a'
    ·
      obtain ⟨u, hu⟩ := hunit
      apply hnd
      refine ⟨(u⁻¹ : Aˣ), ?_⟩
      have ha'0 : ((a' : A) : L) ≠ 0 := fun h =>
        (hu ▸ u.isUnit).ne_zero (Subtype.ext h)
      have hcoe : (((u⁻¹ : Aˣ) : A) : L) = ((a' : A) : L)⁻¹ := by
        refine eq_inv_of_mul_eq_one_right ?_
        rw [← hu]
        exact_mod_cast congrArg Subtype.val u.mul_inv
      have := inv_sub_inv_mem_nonunits P ha'0 ha'
      rwa [hxiF, inv_inv, ← hcoe] at this
    ·
      have hmax : a' ∈ maximalIdeal A :=
        (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hunit)
      have hzero : IsLocalRing.residue A a' = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmax
      rw [hzero, map_zero, sub_zero, hxires, ValuationSubring.mem_nonunits_iff, map_inv₀] at hres
      rw [← Q.toValuationSubring.valuation_le_one_iff] at hfinQ
      have hv0 : 0 < Q.toValuationSubring.valuation (R.residue x) :=
        zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx0)
      exact absurd hfinQ (not_le.mpr ((inv_lt_one₀ hv0).mp hres))
  have hboth : ∀ P Q, Dom A P (x : F) → Dom A P (xi : F) → Red A R (xi : F) P Q →
      R.residue x ∈ Q.toValuationSubring := by
    intro P Q hd hd' hred
    obtain ⟨a, ha⟩ := hd
    obtain ⟨a', ha'⟩ := hd'
    obtain ⟨ha0, haa'⟩ := inv_const_eq P hxF0 ha (hxiF ▸ ha')
    have hres := hred xi (isIntegral_self (xi : F)) a' ha'

    have hunit : IsUnit a' := by
      refine isUnit_iff_exists_inv.mpr ⟨a, Subtype.ext ?_⟩
      show ((a' : A) : L) * ((a : A) : L) = 1
      rw [haa', inv_mul_cancel₀ ha0]
    have hres0 : IsLocalRing.residue A a' ≠ 0 := fun h0 =>
      mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp ((IsLocalRing.residue_eq_zero_iff _).mp h0))
        hunit
    have hc0 : algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a') ≠ 0 := by
      simpa using hres0
    have hvc : Q.toValuationSubring.valuation
        (algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a')) = 1 :=
      valuation_algebraMap_eq_one Q hres0
    rw [ValuationSubring.mem_nonunits_iff] at hres
    have hvxi : Q.toValuationSubring.valuation (R.residue xi) = 1 := by
      have := Valuation.map_add_eq_of_lt_left Q.toValuationSubring.valuation
        (x := algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a'))
        (y := R.residue xi - algebraMap (IsLocalRing.ResidueField A) Fbar
          (IsLocalRing.residue A a')) (by rwa [hvc])
      rwa [add_sub_cancel, hvc] at this
    rw [← Q.toValuationSubring.valuation_le_one_iff, show R.residue x = (R.residue xi)⁻¹ by
      rw [hxires, inv_inv], map_inv₀, hvxi, inv_one]

  obtain ⟨r, hr₁, hr₂, hred₁, hred₂⟩ := exists_map_of_two_charts
    (fun P : Place L F => Dom A P (x : F)) (fun P : Place L F => Dom A P (xi : F))
    (Red A R (x : F)) (Red A R (xi : F))
    (fun Q : Place (IsLocalRing.ResidueField A) Fbar => R.residue x ∈ Q.toValuationSubring)
    hcover E₁ E₂ hfin₁ hinf₂ hboth
  refine ⟨r, fun f hf D hD Q => ?_, hred₁, fun P hP => ?_⟩
  rotate_left
  ·
    rw [← hxiF] at hP ⊢
    by_cases h : Dom A P (x : F)
    · exact red_of_red_of_dom_dom R x hx hfin hdeg hchart.1 xi hxxi P (r P) h hP (hred₁ P h)
    · exact hred₂ P h
  by_cases hQ : R.residue x ∈ Q.toValuationSubring
  ·
    exact mapDomain_eq_of_chart r D Q (fun P => Dom A P (x : F)) (Red A R (x : F))
      (fun P => hr₁ P Q hQ) _ fun T hT =>
        RegularProlongation.sum_ord_eq_ord_residue_of_residue_integralClosure_surjective
          A R x hx hfin hdeg hchart.1 f hf Q hQ D hD T hT
  ·
    have hQ' : R.residue xi ∈ Q.toValuationSubring := by
      rw [hxires]; exact (Q.toValuationSubring.mem_or_inv_mem _).resolve_left hQ
    exact mapDomain_eq_of_chart r D Q (fun P => Dom A P (xi : F)) (Red A R (xi : F))
      (fun P => hr₂ P Q hQ) _ fun T hT =>
        RegularProlongation.sum_ord_eq_ord_residue_of_residue_integralClosure_surjective
          A R xi hx' hfin' hdeg' hchart' f hf Q hQ' D hD T hT

end main

end AgreeR.Deuring

namespace AgreeR

theorem T_mem (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ)) (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) :
    ModularGroup.T ∈ Γ := by
  apply hΓ₁
  rw [CongruenceSubgroup.Gamma1_mem]
  simp [ModularGroup.T]

theorem coeffMap_jqModC' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    coeffMap f (jqModC R) = jqModC S :=
  map_jqModC f

theorem mem_or_neg_mem_gammaH_of_mem_sup (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1))) :
    γ ∈ CohCarrier.GammaH M H ∨ -γ ∈ CohCarrier.GammaH M H := by
  obtain ⟨hγ0, hmem⟩ := CohCarrier.mem_GammaH_iff.mp hγ
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hmem

  have hz' : z = 1 ∨ z = -1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rcases Int.even_or_odd k with hk | hk
    · exact Or.inl hk.neg_one_zpow
    · exact Or.inr hk.neg_one_zpow
  rcases hz' with rfl | rfl
  · left
    rw [mul_one] at hyz
    exact CohCarrier.mem_GammaH_iff.mpr ⟨hγ0, hyz ▸ hy⟩
  · right
    have hneg0 : -γ ∈ CongruenceSubgroup.Gamma0 M := by
      have h10 := CongruenceSubgroup.Gamma0_mem.mp hγ0
      rw [CongruenceSubgroup.Gamma0_mem]
      simp [Matrix.SpecialLinearGroup.coe_neg, h10]
    refine CohCarrier.mem_GammaH_iff.mpr ⟨hneg0, ?_⟩
    have hval : CohCarrier.gamma0Units M ⟨-γ, hneg0⟩ = -CohCarrier.gamma0Units M ⟨γ, hγ0⟩ := by
      apply Units.ext
      rw [Units.val_neg, CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
      simp [CongruenceSubgroup.Gamma0Map, Matrix.SpecialLinearGroup.coe_neg]
    rw [hval, ← hyz, mul_neg_one, neg_neg]
    exact hy

section charts

variable {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}

noncomputable def emb (L : Type*) [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) :
    ↥F₀ →+* ↥(laurentBaseChange L F₀) :=
  ((coeffEmb L).comp (algebraMap ↥F₀ (LaurentSeries ℚ))).codRestrict (laurentBaseChange L F₀)
    (fun z => coeffEmb_mem_laurentBaseChange L z.2)

@[scoped simp] theorem coe_emb (L : Type*) [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (z : ↥F₀) : ((emb L F₀ z : ↥(laurentBaseChange L F₀)) : LaurentSeries L) = coeffEmb L (z : LaurentSeries ℚ) :=
  rfl

theorem isIntegral_adjoin_emb (L : Type*) [Field L] [Algebra ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    {R : Type*} [CommRing R] [Algebra R ↥F₀] [Algebra R L]
    (hRL : ∀ c : R, ((emb L F₀ (algebraMap R ↥F₀ c) : ↥(laurentBaseChange L F₀)) : LaurentSeries L) =
      algebraMap L (LaurentSeries L) (algebraMap R L c))
    (s : ↥F₀) (b : ↥F₀) (hb : IsIntegral ↥(Algebra.adjoin R {s}) b) :
    IsIntegral ↥(Algebra.adjoin L {emb L F₀ s}) (emb L F₀ b) := by

  have hcomp : (emb L F₀).comp (algebraMap R ↥F₀) =
      (algebraMap L ↥(laurentBaseChange L F₀)).comp (algebraMap R L) := by
    refine RingHom.ext fun c => Subtype.ext ?_
    change ((emb L F₀ (algebraMap R ↥F₀ c) : ↥(laurentBaseChange L F₀)) : LaurentSeries L) = _
    rw [hRL c]
    rfl

  have hmap : ∀ z ∈ Algebra.adjoin R {s}, emb L F₀ z ∈ Algebra.adjoin L {emb L F₀ s} := by
    intro z hz
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hz ⊢
    obtain ⟨q, rfl⟩ := (AlgHom.mem_range _).mp hz
    refine (AlgHom.mem_range _).mpr ⟨q.map (algebraMap R L), ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hcomp, Polynomial.aeval_def,
      Polynomial.hom_eval₂]
  let φ : ↥(Algebra.adjoin R {s}) →+* ↥(Algebra.adjoin L {emb L F₀ s}) :=
    ((emb L F₀).comp (algebraMap ↥(Algebra.adjoin R {s}) ↥F₀)).codRestrict
      (Algebra.adjoin L {emb L F₀ s}) (fun z => hmap z z.2)
  exact hb.map_of_comp_eq φ (emb L F₀) (RingHom.ext fun z => rfl)

end charts

end AgreeR
p2m_reactivate "P2MW.S_ModularCurve_exists_isPlaceReductionQExpModL_chartCentre_of_not_dvd.AgreeR"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (j : ↥(qExpFunctionFieldC ℚ Γ)) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = jqModC ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [IsAlgClosed (ResidueField ↥A)] :
    ∃ r : Place (AlgebraicClosure ℚ)
          ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) →
        Place (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ),
      IsPlaceReductionQExpModL A Γ r ∧
      (∀ (P : Place (AlgebraicClosure ℚ)
            ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)))
        (β : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p)
            ↥(qExpFunctionFieldC ℚ Γ) j) →+* ↥A),
        (∀ b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p)
            ↥(qExpFunctionFieldC ℚ Γ) j),
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (b : ↥(qExpFunctionFieldC ℚ Γ)).2⟩ :
              ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) -
            algebraMap (AlgebraicClosure ℚ)
              ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) ((β b : ↥A) :
                AlgebraicClosure ℚ) ∈ P.toValuationSubring.nonunits) →
        ∀ (b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p)
            ↥(qExpFunctionFieldC ℚ Γ) j))
          (yb : LaurentSeries ↥A) (bbar : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)),
          coeffMap A.subtype yb =
            coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) →
          (bbar : LaurentSeries (ResidueField ↥A)) = coeffMap (residue ↥A) yb →
          bbar - algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)
              (residue ↥A (β b)) ∈ (r P).toValuationSubring.nonunits) ∧
      (∀ (P : Place (AlgebraicClosure ℚ)
            ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)))
        (β : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p)
            ↥(qExpFunctionFieldC ℚ Γ) j) →+* ↥A),
        (∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p)
            ↥(qExpFunctionFieldC ℚ Γ) j),
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (b : ↥(qExpFunctionFieldC ℚ Γ)).2⟩ :
              ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) -
            algebraMap (AlgebraicClosure ℚ)
              ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) ((β b : ↥A) :
                AlgebraicClosure ℚ) ∈ P.toValuationSubring.nonunits) →
        ∀ (b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p)
            ↥(qExpFunctionFieldC ℚ Γ) j))
          (yb : LaurentSeries ↥A) (bbar : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)),
          coeffMap A.subtype yb =
            coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) →
          (bbar : LaurentSeries (ResidueField ↥A)) = coeffMap (residue ↥A) yb →
          bbar - algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)
              (residue ↥A (β b)) ∈ (r P).toValuationSubring.nonunits) := by
  classical

  obtain ⟨H, rfl⟩ := CohCarrier.exists_eq_gammaH_of_gamma1_le_of_le_gamma0 M Γ hΓ₁ hΓ₀
  haveI hFI : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le hΓ₁
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := AgreeR.T_mem M _ hΓ₁
  haveI : CharP (ResidueField ↥A) p := A.residueField_charP_of_liesOverPrime Fact.out hA

  obtain ⟨R, -, hRres⟩ :=
    ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ) A (CohCarrier.GammaH M H) hT

  have hjb : coeffEmb (AlgebraicClosure ℚ) ((j : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) = coeffMap A.subtype (jqModC ↥A) := by
    rw [hj, AgreeR.coeffMap_jqModC']
    exact AgreeR.coeffMap_jqModC' _
  have hyj : coeffMap A.subtype (jqModC ↥A) ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := by
    rw [← hjb]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) j.2
  obtain ⟨hxO, hxres⟩ := hRres (jqModC ↥A) hyj
  set xF : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := ⟨coeffMap A.subtype (jqModC ↥A), hyj⟩ with hxF_def
  set x : ↥R.integers := ⟨xF, hxO⟩ with hx_def
  have hxF : (xF : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := AgreeR.coeffMap_jqModC' _
  have hxemb : AgreeR.emb (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j = xF := Subtype.ext hjb
  have hxres' : ((R.residue x : ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H))) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) := by
    rw [hxres]; exact AgreeR.coeffMap_jqModC' _

  obtain ⟨xb, hxb, hxbtr, hxbfd, hxble⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField (AlgebraicClosure ℚ) A (CohCarrier.GammaH M H) hT
  have hxbeq : R.residue x = xb := Subtype.ext (hxres'.trans hxb.symm)

  haveI : IsCurveOver (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H)) :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hxbtr hxbfd
  have hxFtr : Transcendental (AlgebraicClosure ℚ) xF := by
    refine (transcendental_algebraMap_iff
      (algebraMap ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) (LaurentSeries (AlgebraicClosure ℚ))).injective).mp ?_
    show Transcendental (AlgebraicClosure ℚ) (xF : LaurentSeries (AlgebraicClosure ℚ))
    rw [hxF]
    exact ModularCurve.transcendental_jqModC (AlgebraicClosure ℚ)
  haveI hxFfd : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({xF} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange (CohCarrier.GammaH M H) hT (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) rfl xF
      (hxF.trans (by rw [← ModularCurve.jqModC_rat]; exact (AgreeR.coeffMap_jqModC' _).symm))
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hxFtr hxFfd
  have hx : Transcendental (ResidueField ↥A) (R.residue x) := hxbeq ▸ hxbtr
  have hfin : 0 < Module.finrank ↥(IntermediateField.adjoin (ResidueField ↥A) ({R.residue x} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H)))) ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H)) := by
    rw [hxbeq]; exact Module.finrank_pos
  have hle1 := hxble xF hxF
  have hle2 := ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index (AlgebraicClosure ℚ) (CohCarrier.GammaH M H) hT
    (CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1))) (ModularCurve.GammaH_mono le_sup_left)
    (fun γ hγ => AgreeR.mem_or_neg_mem_gammaH_of_mem_sup M H γ hγ) xF hxF
  have hle3 := ModularCurve.index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField
    M H hpM A hA xb hxb
  have hdeg : Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({(x : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) =
      Module.finrank ↥(IntermediateField.adjoin (ResidueField ↥A) ({R.residue x} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H)))) ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H)) := by
    rw [hxbeq]
    show Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({xF} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) = _
    omega
  have hgood : genusFF (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H)) = genusFF (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) :=
    ModularCurve.genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd M H hpM (ResidueField ↥A)
  have hchart := AlgebraicCurve.RegularProlongation.residue_integralClosure_surjective_of_genusFF_eq
    A R x hx hfin hdeg hgood

  obtain ⟨r, hdiv, hred₁, hred₂⟩ := AgreeR.Deuring.main R x hx hfin hdeg hchart

  have hRL : ∀ c : ↥(GaloisRep.ratLocalizedAt p), ((AgreeR.emb (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) c) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) : LaurentSeries (AlgebraicClosure ℚ)) =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) c) := by
    intro c
    have hb : algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) c =
        algebraMap ℚ (AlgebraicClosure ℚ) (c : ℚ) := rfl
    have ha : ((algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) c :
        ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) =
        algebraMap ℚ (LaurentSeries ℚ) (c : ℚ) := by
      show ((algebraMap ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (c : ℚ) :
        ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) = _
      rw [eq_ratCast (algebraMap ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))),
        eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)), SubfieldClass.coe_ratCast]
    rw [hb, AgreeR.coe_emb, ha]
    change coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) _ = _
    rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]
  refine ⟨r, ?_, ?_, ?_⟩
  · show (∀ P, (r P).deg = P.deg) ∧ _
    refine ⟨fun P => ?_, ?_⟩
    · rw [IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed]
    · intro y hy hyk hy0 D hD Q
      obtain ⟨hO, hres⟩ := hRres y hy
      have hf : R.residue ⟨_, hO⟩ = ⟨coeffMap (residue ↥A) y, hyk⟩ := Subtype.ext hres
      have hf0 : R.residue ⟨_, hO⟩ ≠ 0 := by
        rw [hf]; exact fun h => hy0 (congrArg Subtype.val h)
      have := hdiv ⟨_, hO⟩ hf0 D hD Q
      rwa [hf] at this
  ·
    intro P β hβ b yb bbar hyb hbbar
    have hy' : coeffMap A.subtype yb ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := by
      rw [hyb]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))).2
    obtain ⟨hbO, hbres⟩ := hRres yb hy'
    have e1 : (⟨coeffMap A.subtype yb, hy'⟩ : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) = AgreeR.emb (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := Subtype.ext hyb
    have hfbO : AgreeR.emb (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ R.integers := e1 ▸ hbO
    have hresb : R.residue ⟨AgreeR.emb (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))), hfbO⟩ = bbar := by
      have e2 : (⟨⟨coeffMap A.subtype yb, hy'⟩, hbO⟩ : ↥R.integers) = ⟨_, hfbO⟩ := Subtype.ext e1
      rw [← e2]; exact Subtype.ext (hbres.trans hbbar.symm)
    have hint : IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ) {(x : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))}) ((⟨_, hfbO⟩ : ↥R.integers) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) := by
      show IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ) {xF}) (AgreeR.emb (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))
      rw [← hxemb]
      exact AgreeR.isIntegral_adjoin_emb (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) hRL j (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) b.2
    have hd : AgreeR.Deuring.Dom A P (x : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) :=
      ⟨β (TwoChartIntegralModel.jChartFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j), by
        convert hβ (TwoChartIntegralModel.jChartFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j) using 2
        exact Subtype.ext hjb.symm⟩
    have := hred₁ P hd ⟨_, hfbO⟩ hint (β b) (hβ b)
    rwa [hresb] at this
  ·
    intro P β hβ b yb bbar hyb hbbar
    have hy' : coeffMap A.subtype yb ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := by
      rw [hyb]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))).2
    obtain ⟨hbO, hbres⟩ := hRres yb hy'
    have e1 : (⟨coeffMap A.subtype yb, hy'⟩ : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) = AgreeR.emb (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := Subtype.ext hyb
    have hfbO : AgreeR.emb (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ R.integers := e1 ▸ hbO
    have hresb : R.residue ⟨AgreeR.emb (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))), hfbO⟩ = bbar := by
      have e2 : (⟨⟨coeffMap A.subtype yb, hy'⟩, hbO⟩ : ↥R.integers) = ⟨_, hfbO⟩ := Subtype.ext e1
      rw [← e2]; exact Subtype.ext (hbres.trans hbbar.symm)
    have hjinv : (j : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))⁻¹ ∈ TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j :=
      TwoChartIntegralModel.subset_chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) _ (Set.mem_singleton _)
    have hxembi : AgreeR.emb (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j⁻¹ = xF⁻¹ := by rw [map_inv₀, hxemb]
    have hint : IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ) {(x : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))⁻¹}) ((⟨_, hfbO⟩ : ↥R.integers) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) := by
      show IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ) {xF⁻¹}) (AgreeR.emb (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))
      rw [← hxembi]
      exact AgreeR.isIntegral_adjoin_emb (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) hRL j⁻¹ (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) b.2
    have hd : AgreeR.Deuring.Dom A P (x : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))⁻¹ :=
      ⟨β ⟨j⁻¹, hjinv⟩, by
        convert hβ ⟨j⁻¹, hjinv⟩ using 2
        exact hxembi.symm⟩
    have := hred₂ P hd ⟨_, hfbO⟩ hint (β b) (hβ b)
    rwa [hresb] at this

end S_ModularCurve_exists_isPlaceReductionQExpModL_chartCentre_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_exists_isPlaceReductionQExpModL_chartCentre_of_not_dvd (solution)
