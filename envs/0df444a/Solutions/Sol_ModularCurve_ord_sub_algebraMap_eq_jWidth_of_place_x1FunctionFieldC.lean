-- Prove2me | solution 1 for ModularCurve.ord_sub_algebraMap_eq_jWidth_of_place_x1FunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/efd2e6d7-fb27-5e57-ac30-65be1f935801

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_X0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable
import Theorems.Thm_ModularCurve_exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC
import Theorems.Thm_ModularCurve_card_fibres_jqModC_x1FunctionFieldC_le_natCard_doubleCoset_gamma1
import Theorems.Thm_ModularCurve_finrank_adjoin_x1FunctionFieldC_eq_index_gamma1_sup_of_isAlgClosed
import Theorems.Thm_ModularCurve_two_mul_genusFF_x1FunctionFieldC_add_natCard_doubleCoset_eq_index_add_two
import Theorems.Thm_ModularCurve_exists_ord_eq_zero_of_ord_pos_x1FunctionFieldC
import Theorems.Thm_AlgebraicCurve_exists_finset_sum_ord_sub_algebraMap_eq_finrank_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed
import Theorems.Thm_CongruenceSubgroup_index_gamma1_sup_zpowers_neg_one_eq_three_mul_natCard_doubleCoset_and_eq_two_mul
import Theorems.Thm_ModularCurve_three_dvd_mul_ord_and_two_dvd_mul_ord_sub_of_ord_eq_zero_x1FunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_sub_algebraMap_eq_jWidth_of_place_x1FunctionFieldC
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub"
p2m_attr_erase "instance" "KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add"
p2m_attr_erase "simp" "ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one"
p2m_attr_erase "simp" "TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers"
p2m_attr_erase "simp" "AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec"

set_option autoImplicit false
set_option maxHeartbeats 8000000

p2m_open "AlgebraicCurve~genus ModularCurve CongruenceSubgroup"
open scoped MatrixGroups ModularForm IntermediateField

namespace SqueezeStubs

section Ord
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_algebraMap {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have hmem : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hmem' : algebraMap K F c⁻¹ ∈ v.toValuationSubring := v.algebraMap_mem' c⁻¹
  let u : v.toValuationSubringˣ :=
    ⟨⟨algebraMap K F c, hmem⟩, ⟨algebraMap K F c⁻¹, hmem'⟩,
      Subtype.ext (by simp [hc]), Subtype.ext (by simp [hc])⟩
  exact v.ord_coe_unit u

theorem ord_neg (f : F) : v.ord (-f) = v.ord f := by
  simp only [Place.ord, Valuation.map_neg]

theorem ord_add_eq_of_lt {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f < v.ord g) :
    v.ord (f + g) = v.ord f := by
  simp only [Place.ord] at h ⊢
  have hf' := v.adicValuation_ne_zero hf
  have hg' := v.adicValuation_ne_zero hg
  have hlt : v.adicValuation g < v.adicValuation f := by
    rw [← WithZero.log_lt_log hg' hf']
    omega
  rw [Valuation.map_add_eq_of_lt_left _ hlt]

theorem min_ord_le_ord_add {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) := by
  simp only [Place.ord]
  have h := v.adicValuation.map_add f g
  have hf' := v.adicValuation_ne_zero hf
  have hg' := v.adicValuation_ne_zero hg
  have hfg' := v.adicValuation_ne_zero hfg
  rcases le_max_iff.mp h with h1 | h1
  · have : WithZero.log (v.adicValuation (f + g)) ≤ WithZero.log (v.adicValuation f) :=
      (WithZero.log_le_log hfg' hf').mpr h1
    omega
  · have : WithZero.log (v.adicValuation (f + g)) ≤ WithZero.log (v.adicValuation g) :=
      (WithZero.log_le_log hfg' hg').mpr h1
    omega

theorem not_ord_pos_of_ne (f : F) {a b : K} (hab : a ≠ b)
    (ha : 0 < v.ord (f - algebraMap K F a)) (hb : 0 < v.ord (f - algebraMap K F b)) : False := by
  have hfa : f - algebraMap K F a ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at ha; exact lt_irrefl _ ha
  have hfb : -(f - algebraMap K F b) ≠ 0 := by
    intro h; rw [neg_eq_zero] at h; rw [h, Place.ord_zero] at hb; exact lt_irrefl _ hb
  have heq : (f - algebraMap K F a) + -(f - algebraMap K F b) = algebraMap K F (b - a) := by
    rw [map_sub]; ring
  have hne : (f - algebraMap K F a) + -(f - algebraMap K F b) ≠ 0 := by
    rw [heq]; exact (map_ne_zero _).mpr (sub_ne_zero.mpr hab.symm)
  have h := min_ord_le_ord_add v hfa hfb hne
  rw [heq, ord_algebraMap v (sub_ne_zero.mpr hab.symm), ord_neg] at h
  rcases min_le_iff.mp h with h | h <;> omega

end Ord

theorem squeeze_arith {ι : Type*} (S₀ S₁ Sinf : Finset ι) (e₀ e₁ einf : ι → ℤ) (n N₃ N₂ c g ex : ℤ)
    (hsum₀ : ∑ P ∈ S₀, e₀ P = n) (hsum₁ : ∑ P ∈ S₁, e₁ P = n) (hsuminf : ∑ P ∈ Sinf, einf P = n)
    (hc₀ : (S₀.card : ℤ) ≤ N₃) (hc₁ : (S₁.card : ℤ) ≤ N₂) (hcinf : (Sinf.card : ℤ) ≤ c)
    (hgen : 2 * g + N₃ + N₂ + c ≤ n + 2) (hex : 1 ≤ ex)
    (hH : ∑ P ∈ S₀, (e₀ P - 1) + ∑ P ∈ S₁, (e₁ P - 1) + (ex - 1) + ∑ P ∈ Sinf, (einf P - 1) ≤
      2 * g - 2 + 2 * n) :
    (S₀.card : ℤ) = N₃ ∧ (S₁.card : ℤ) = N₂ ∧ ex = 1 := by
  have e0 : ∑ P ∈ S₀, (e₀ P - 1) = n - S₀.card := by
    rw [Finset.sum_sub_distrib, hsum₀, Finset.sum_const, nsmul_eq_mul, mul_one]
  have e1 : ∑ P ∈ S₁, (e₁ P - 1) = n - S₁.card := by
    rw [Finset.sum_sub_distrib, hsum₁, Finset.sum_const, nsmul_eq_mul, mul_one]
  have ei : ∑ P ∈ Sinf, (einf P - 1) = n - Sinf.card := by
    rw [Finset.sum_sub_distrib, hsuminf, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [e0, e1, ei] at hH
  omega

theorem eq_of_dvd_of_sum_eq {ι : Type*} (S : Finset ι) (e : ι → ℤ) (m : ℤ)
    (hdvd : ∀ P ∈ S, m ∣ e P) (hpos : ∀ P ∈ S, 0 < e P) (hsum : ∑ P ∈ S, e P = m * S.card) :
    ∀ P ∈ S, e P = m := by
  have hge : ∀ P ∈ S, m ≤ e P := fun P hP => Int.le_of_dvd (hpos P hP) (hdvd P hP)
  have hS : ∑ P ∈ S, (m : ℤ) = ∑ P ∈ S, e P := by
    rw [Finset.sum_const, hsum, nsmul_eq_mul, mul_comm]
  have := (Finset.sum_eq_sum_iff_of_le hge).mp hS
  exact fun P hP => (this P hP).symm

end SqueezeStubs

open SqueezeStubs

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ]
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (J : ↥(ModularCurve.x1FunctionFieldC κ M)) (hJ : (J : LaurentSeries κ) = ModularCurve.jqModC κ)
    (x : Place κ ↥(ModularCurve.x1FunctionFieldC κ M)) (hx : 0 ≤ x.ord J)
    (j₀ : κ) (hj₀ : 1 ≤ x.ord (J - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) j₀)) :
    x.ord (J - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) j₀) = (ModularCurve.jWidth j₀ : ℤ) := by
  classical

  obtain ⟨t, ht, htr, hfd, hsep⟩ := ModularCurve.exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC p M hM hpM κ
  have htJ : t = J := Subtype.ext (ht.trans hJ.symm)
  subst htJ
  haveI := hfd
  haveI := hsep
  set n : ℤ := (Module.finrank ↥κ⟮t⟯ ↥(ModularCurve.x1FunctionFieldC κ M) : ℤ) with hn

  obtain ⟨S₀, hS₀, hsum₀⟩ := AlgebraicCurve.exists_finset_sum_ord_sub_algebraMap_eq_finrank_of_isAlgClosed κ (t : ↥(ModularCurve.x1FunctionFieldC κ M)) htr hfd 0
  obtain ⟨S₁, hS₁, hsum₁⟩ := AlgebraicCurve.exists_finset_sum_ord_sub_algebraMap_eq_finrank_of_isAlgClosed κ (t : ↥(ModularCurve.x1FunctionFieldC κ M)) htr hfd 1728
  obtain ⟨Sinf, hSinf, hsuminf⟩ := AlgebraicCurve.exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed κ (t : ↥(ModularCurve.x1FunctionFieldC κ M)) htr hfd
  have hS₀' : ∀ Q, Q ∈ S₀ ↔ 0 < Q.ord t := by
    intro Q; rw [hS₀, map_zero, sub_zero]
  have hS₁' : ∀ Q, Q ∈ S₁ ↔ 0 < Q.ord (t - 1728) := by
    intro Q; rw [hS₁, map_ofNat]

  obtain ⟨hc₀, hc₁, hcinf⟩ := ModularCurve.card_fibres_jqModC_x1FunctionFieldC_le_natCard_doubleCoset_gamma1 M hpM κ t ht S₀ S₁ Sinf hS₀' hS₁' hSinf
  have hdeg := ModularCurve.finrank_adjoin_x1FunctionFieldC_eq_index_gamma1_sup_of_isAlgClosed p M hM hpM κ t ht
  have hgen := le_of_eq (ModularCurve.two_mul_genusFF_x1FunctionFieldC_add_natCard_doubleCoset_eq_index_add_two p M hM hpM κ)
  obtain ⟨h3, h2⟩ := CongruenceSubgroup.index_gamma1_sup_zpowers_neg_one_eq_three_mul_natCard_doubleCoset_and_eq_two_mul M hM
  set N₃ := Nat.card (DoubleCoset.Quotient (Gamma1 M : Set SL(2, ℤ))
        (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) : Set SL(2, ℤ))) with hN₃
  set N₂ := Nat.card (DoubleCoset.Quotient (Gamma1 M : Set SL(2, ℤ))
        (Subgroup.zpowers ModularGroup.S : Set SL(2, ℤ))) with hN₂
  set c := Nat.card (DoubleCoset.Quotient (Gamma1 M : Set SL(2, ℤ))
        ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ))) with hc
  set idx := (Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index with hidx
  have h1728 : (1728 : κ) ≠ 0 := by
    intro h
    have h' : ((1728 : ℕ) : κ) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff κ p] at h'
    have hp := (Fact.out : p.Prime)
    have : p ∣ 2 ^ 6 * 3 ^ 3 := by norm_num at h' ⊢; exact h'
    rcases (Nat.Prime.dvd_mul hp).mp this with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2); omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3); omega

  have hdiv₀ : ∀ P ∈ S₀, (3 : ℤ) ∣ P.ord t := by
    intro P hP
    have hP' : 0 < P.ord t := (hS₀' P).mp hP
    obtain ⟨k, g, pg, u, hk3, hg, hg0, hu, hPu⟩ := (ModularCurve.exists_ord_eq_zero_of_ord_pos_x1FunctionFieldC p hp5 κ M hM hpM t ht P).1 hP'
    have h := (ModularCurve.three_dvd_mul_ord_and_two_dvd_mul_ord_sub_of_ord_eq_zero_x1FunctionFieldC κ M t ht k g pg hg hg0 u hu P hPu).1
    have hk3' : ¬ (3 : ℤ) ∣ (k : ℤ) := by exact_mod_cast hk3
    exact (Int.Prime.dvd_mul' (by norm_num) h).resolve_left hk3'
  have hdiv₁ : ∀ P ∈ S₁, (2 : ℤ) ∣ P.ord (t - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728) := by
    intro P hP
    have hP' : 0 < P.ord (t - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728) := (hS₁ P).mp hP
    have hP0 : 0 ≤ P.ord t := by
      by_contra hneg
      push_neg at hneg
      have ht0 : (t : ↥(ModularCurve.x1FunctionFieldC κ M)) ≠ 0 := by
        intro h; rw [h, Place.ord_zero] at hneg; exact lt_irrefl _ hneg
      have hc : -(algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728) ≠ 0 := by
        rw [neg_ne_zero]; exact (map_ne_zero _).mpr h1728
      have hlt : P.ord t < P.ord (-(algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728)) := by
        rw [ord_neg, ord_algebraMap P h1728]; exact hneg
      have := ord_add_eq_of_lt P ht0 hc hlt
      rw [← sub_eq_add_neg] at this
      rw [this] at hP'
      exact lt_irrefl _ (hP'.trans hneg)
    obtain ⟨k, g, pg, u, hk2, hg, hg0, hu, hPu⟩ := (ModularCurve.exists_ord_eq_zero_of_ord_pos_x1FunctionFieldC p hp5 κ M hM hpM t ht P).2 hP'
    have h := (ModularCurve.three_dvd_mul_ord_and_two_dvd_mul_ord_sub_of_ord_eq_zero_x1FunctionFieldC κ M t ht k g pg hg hg0 u hu P hPu).2
    have hk2' : ¬ (2 : ℤ) ∣ (k : ℤ) := by exact_mod_cast hk2
    exact (Int.Prime.dvd_mul' (by norm_num) h).resolve_left hk2'

  have hpos₀ : ∀ P ∈ S₀, 0 < P.ord t := fun P hP => (hS₀' P).mp hP
  have hpos₁ : ∀ P ∈ S₁, 0 < P.ord (t - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728) := fun P hP => (hS₁ P).mp hP
  have hposinf : ∀ P ∈ Sinf, 0 < -P.ord t := fun P hP => by have := (hSinf P).mp hP; omega
  have hdisj : Disjoint S₀ S₁ := by
    rw [Finset.disjoint_left]
    intro P h0 h1
    exact not_ord_pos_of_ne P t (show (0 : κ) ≠ 1728 from h1728.symm)
      (by rw [map_zero, sub_zero]; exact hpos₀ P h0) (hpos₁ P h1)

  have hdeg' : n = (idx : ℤ) := by rw [hn, hdeg]
  have h3' : (idx : ℤ) = 3 * N₃ := by exact_mod_cast h3
  have h2' : (idx : ℤ) = 2 * N₂ := by exact_mod_cast h2
  have hgen' : 2 * (genusFF κ ↥(ModularCurve.x1FunctionFieldC κ M) : ℤ) + N₃ + N₂ + c ≤ (idx : ℤ) + 2 := by exact_mod_cast hgen
  have hc₀' : (S₀.card : ℤ) ≤ N₃ := by exact_mod_cast hc₀
  have hc₁' : (S₁.card : ℤ) ≤ N₂ := by exact_mod_cast hc₁
  have hcinf' : (Sinf.card : ℤ) ≤ c := by exact_mod_cast hcinf

  by_cases h0 : j₀ = 0
  · subst h0
    have hxS : x ∈ S₀ := (hS₀ x).mpr (by omega)

    have hH := AlgebraicCurve.sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable κ t htr hfd hsep (S₀ ∪ S₁) (fun P => if P ∈ S₀ then 0 else 1728)
      (by
        intro P hP
        beta_reduce
        rcases Finset.mem_union.mp hP with h | h
        · rw [if_pos h, map_zero, sub_zero]; exact hpos₀ P h
        · rw [if_neg (Finset.disjoint_right.mp hdisj h)]; exact hpos₁ P h)
      Sinf (fun P hP => (hSinf P).mp hP)
    rw [Finset.sum_union hdisj] at hH
    beta_reduce at hH
    have hH₀ : ∑ P ∈ S₀, (P.ord (t - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) (if P ∈ S₀ then 0 else 1728)) - 1) =
        ∑ P ∈ S₀, (P.ord t - 1) :=
      Finset.sum_congr rfl (fun P hP => by rw [if_pos hP, map_zero, sub_zero])
    have hH₁ : ∑ P ∈ S₁, (P.ord (t - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) (if P ∈ S₀ then 0 else 1728)) - 1) =
        ∑ P ∈ S₁, (P.ord (t - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728) - 1) :=
      Finset.sum_congr rfl (fun P hP => by rw [if_neg (Finset.disjoint_right.mp hdisj hP)])
    rw [hH₀, hH₁] at hH
    have hsq := squeeze_arith S₀ S₁ Sinf (fun P => P.ord t) (fun P => P.ord (t - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728))
      (fun P => -P.ord t) n N₃ N₂ c (genusFF κ ↥(ModularCurve.x1FunctionFieldC κ M)) 1
      (by simpa using hsum₀) hsum₁ hsuminf hc₀' hc₁' hcinf' (by omega) le_rfl (by simpa using hH)

    have hall := eq_of_dvd_of_sum_eq S₀ (fun P => P.ord t) 3 hdiv₀ hpos₀
      (by rw [show ∑ P ∈ S₀, P.ord t = n by rw [hn]; simpa using hsum₀, hdeg', h3', hsq.1])
    have h3x : x.ord t = 3 := hall x hxS
    simp only [map_zero, sub_zero]
    rw [h3x, ModularCurve.jWidth_of_eq_zero rfl]; rfl
  by_cases h1 : j₀ = 1728
  · subst h1
    have hxS : x ∈ S₁ := (hS₁ x).mpr (by omega)
    have hH := AlgebraicCurve.sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable κ t htr hfd hsep (S₀ ∪ S₁) (fun P => if P ∈ S₀ then 0 else 1728)
      (by
        intro P hP
        beta_reduce
        rcases Finset.mem_union.mp hP with h | h
        · rw [if_pos h, map_zero, sub_zero]; exact hpos₀ P h
        · rw [if_neg (Finset.disjoint_right.mp hdisj h)]; exact hpos₁ P h)
      Sinf (fun P hP => (hSinf P).mp hP)
    rw [Finset.sum_union hdisj] at hH
    beta_reduce at hH
    have hH₀ : ∑ P ∈ S₀, (P.ord (t - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) (if P ∈ S₀ then 0 else 1728)) - 1) =
        ∑ P ∈ S₀, (P.ord t - 1) :=
      Finset.sum_congr rfl (fun P hP => by rw [if_pos hP, map_zero, sub_zero])
    have hH₁ : ∑ P ∈ S₁, (P.ord (t - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) (if P ∈ S₀ then 0 else 1728)) - 1) =
        ∑ P ∈ S₁, (P.ord (t - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728) - 1) :=
      Finset.sum_congr rfl (fun P hP => by rw [if_neg (Finset.disjoint_right.mp hdisj hP)])
    rw [hH₀, hH₁] at hH
    have hsq := squeeze_arith S₀ S₁ Sinf (fun P => P.ord t) (fun P => P.ord (t - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728))
      (fun P => -P.ord t) n N₃ N₂ c (genusFF κ ↥(ModularCurve.x1FunctionFieldC κ M)) 1
      (by simpa using hsum₀) hsum₁ hsuminf hc₀' hc₁' hcinf' (by omega) le_rfl (by simpa using hH)
    have hall := eq_of_dvd_of_sum_eq S₁ (fun P => P.ord (t - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728)) 2 hdiv₁ hpos₁
      (by rw [hsum₁, ← hn, hdeg', h2', hsq.2.1])
    have h2x : x.ord (t - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728) = 2 := hall x hxS
    rw [h2x, ModularCurve.jWidth_of_eq_1728 rfl h1728]; rfl
  ·
    have hx0 : x ∉ S₀ := fun h => not_ord_pos_of_ne x t h0
      hj₀ (by rw [map_zero, sub_zero]; exact hpos₀ x h)
    have hx1 : x ∉ S₁ := fun h => not_ord_pos_of_ne x t h1 hj₀ (hpos₁ x h)
    have hdisj' : Disjoint (S₀ ∪ S₁) {x} := by
      rw [Finset.disjoint_singleton_right, Finset.mem_union, not_or]; exact ⟨hx0, hx1⟩
    let a : Place κ ↥(ModularCurve.x1FunctionFieldC κ M) → κ := fun P => if P ∈ S₀ then 0 else if P ∈ S₁ then 1728 else j₀
    have ha₀ : ∀ P ∈ S₀, a P = 0 := fun P hP => if_pos hP
    have ha₁ : ∀ P ∈ S₁, a P = 1728 := fun P hP => by
      show (if P ∈ S₀ then (0:κ) else if P ∈ S₁ then 1728 else j₀) = 1728
      rw [if_neg (Finset.disjoint_right.mp hdisj hP), if_pos hP]
    have hax : a x = j₀ := by
      show (if x ∈ S₀ then (0:κ) else if x ∈ S₁ then 1728 else j₀) = j₀
      rw [if_neg hx0, if_neg hx1]
    have hH := AlgebraicCurve.sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable κ t htr hfd hsep (S₀ ∪ S₁ ∪ {x}) a
      (by
        intro P hP
        rcases Finset.mem_union.mp hP with hP | hP
        · rcases Finset.mem_union.mp hP with h | h
          · rw [ha₀ P h, map_zero, sub_zero]; exact hpos₀ P h
          · rw [ha₁ P h]; exact hpos₁ P h
        · rw [Finset.mem_singleton.mp hP, hax]; omega)
      Sinf (fun P hP => (hSinf P).mp hP)
    rw [Finset.sum_union hdisj', Finset.sum_union hdisj, Finset.sum_singleton, hax] at hH
    have hH₀ : ∑ P ∈ S₀, (P.ord (t - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) (a P)) - 1) = ∑ P ∈ S₀, (P.ord t - 1) :=
      Finset.sum_congr rfl (fun P hP => by rw [ha₀ P hP, map_zero, sub_zero])
    have hH₁ : ∑ P ∈ S₁, (P.ord (t - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) (a P)) - 1) =
        ∑ P ∈ S₁, (P.ord (t - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728) - 1) :=
      Finset.sum_congr rfl (fun P hP => by rw [ha₁ P hP])
    rw [hH₀, hH₁] at hH
    have hsq := squeeze_arith S₀ S₁ Sinf (fun P => P.ord t) (fun P => P.ord (t - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728))
      (fun P => -P.ord t) n N₃ N₂ c (genusFF κ ↥(ModularCurve.x1FunctionFieldC κ M)) (x.ord (t - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) j₀))
      (by simpa using hsum₀) hsum₁ hsuminf hc₀' hc₁' hcinf' (by omega) hj₀ (by simpa using hH)
    rw [hsq.2.2, ModularCurve.jWidth_of_ne h0 h1]; rfl

end S_ModularCurve_ord_sub_algebraMap_eq_jWidth_of_place_x1FunctionFieldC
end P2MW
export P2MW.S_ModularCurve_ord_sub_algebraMap_eq_jWidth_of_place_x1FunctionFieldC (solution)
