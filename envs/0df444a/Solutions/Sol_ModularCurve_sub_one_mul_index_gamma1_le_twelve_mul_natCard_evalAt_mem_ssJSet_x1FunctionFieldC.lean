-- Prove2me | solution 1 for ModularCurve.sub_one_mul_index_gamma1_le_twelve_mul_natCard_evalAt_mem_ssJSet_x1FunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/31e0a66b-006d-5d5e-96d9-79eaa3553cf7

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_ModularCurve_mem_ssJSet_iff_eval_eq_zero_of_thetaL_pow_mul_aeval_eq
import Theorems.Thm_AlgebraicCurve_finrank_adjoin_le_mul_natCard_place_ord_sub_algebraMap_pos_of_forall_ord_le
import Theorems.Thm_AlgebraicCurve_Place_mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos
import Theorems.Thm_ModularCurve_isRational_place_x1FunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_ord_dvd_twelve_div_sub_one_of_ord_pos_x1FunctionFieldC_of_lt_five
import Theorems.Thm_ModularCurve_ord_sub_algebraMap_eq_jWidth_of_place_x1FunctionFieldC
import Theorems.Thm_ModularCurve_finrank_adjoin_x1FunctionFieldC_eq_index_gamma1_sup_of_isAlgClosed
import Theorems.Thm_ModularCurve_exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC
import Theorems.Thm_AlgebraicCurve_exists_finset_sum_ord_sub_algebraMap_eq_finrank_of_isAlgClosed
import Theorems.Thm_ModularCurve_ssJSet_finite
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_of_lt_five
import Theorems.Thm_ModularCurve_exists_separable_thetaL_jqModC_pow_mul_aeval_eq
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_sub_one_mul_index_gamma1_le_twelve_mul_natCard_evalAt_mem_ssJSet_x1FunctionFieldC
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite"
p2m_attr_erase "instance" "ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero"
p2m_attr_erase "simp" "TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward"
p2m_attr_erase "simp" "AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V"
p2m_attr_erase "simp" "WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one"
p2m_attr_erase "simp" "ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun"
p2m_attr_erase "simp" "KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add"
p2m_attr_erase "simp" "ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec"

set_option autoImplicit false

open AlgebraicCurve ModularCurve Polynomial
open scoped MatrixGroups

namespace SsCountAux

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

theorem ord_add_eq_of_lt {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f < v.ord g) :
    v.ord (f + g) = v.ord f := by
  simp only [Place.ord] at h ⊢
  have hf' := v.adicValuation_ne_zero hf
  have hg' := v.adicValuation_ne_zero hg
  have hlt : v.adicValuation g < v.adicValuation f := by
    rw [← WithZero.log_lt_log hg' hf']
    omega
  rw [Valuation.map_add_eq_of_lt_left _ hlt]

theorem ord_multiset_prod (s : Multiset F) (hs : ∀ f ∈ s, f ≠ 0) :
    v.ord s.prod = (s.map v.ord).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    have ha : a ≠ 0 := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ f ∈ s, f ≠ 0 := fun f hf => hs f (Multiset.mem_cons_of_mem hf)
    have hprod : s.prod ≠ 0 := Multiset.prod_ne_zero fun h0 => hs' 0 h0 rfl
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, v.ord_mul ha hprod, ih hs']

end Ord

section OrdPoly

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_pow' (f : F) (n : ℕ) : v.ord (f ^ n) = (n : ℤ) * v.ord f := by
  rw [← zpow_natCast]; exact v.ord_zpow f n

theorem ord_sub_algebraMap_eq_zero {J : F} (hJc : ∀ r : K, J - algebraMap K F r ≠ 0)
    {j₀ : K} (hj₀ : 1 ≤ v.ord (J - algebraMap K F j₀)) {r : K} (hr : r ≠ j₀) :
    v.ord (J - algebraMap K F r) = 0 := by
  have hsplit : J - algebraMap K F r = algebraMap K F (j₀ - r) + (J - algebraMap K F j₀) := by
    rw [map_sub, sub_add_sub_cancel']
  have hne : algebraMap K F (j₀ - r) ≠ 0 := (_root_.map_ne_zero _).mpr (sub_ne_zero.mpr hr.symm)
  have hc0 : v.ord (algebraMap K F (j₀ - r)) = 0 := ord_algebraMap v (sub_ne_zero.mpr hr.symm)
  have hlt : v.ord (algebraMap K F (j₀ - r)) < v.ord (J - algebraMap K F j₀) := by rw [hc0]; omega
  rw [hsplit, ord_add_eq_of_lt v hne (hJc j₀) hlt, hc0]

theorem ord_aeval_eq_zero [IsAlgClosed K] {J : F} (hJc : ∀ r : K, J - algebraMap K F r ≠ 0)
    {j₀ : K} (hj₀ : 1 ≤ v.ord (J - algebraMap K F j₀)) {Q : K[X]} (hQ : Q.Monic)
    (hev : Q.eval j₀ ≠ 0) : v.ord (aeval J Q) = 0 := by
  classical
  have hQroots : Q = (Q.roots.map fun r => X - C r).prod := by
    conv_lhs => rw [Splits.eq_prod_roots (IsAlgClosed.splits Q), hQ.leadingCoeff, map_one, one_mul]
  have haeval : aeval J Q = (Q.roots.map fun r => J - algebraMap K F r).prod := by
    conv_lhs => rw [hQroots]
    rw [map_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro r _
    simp [Function.comp]
  have hfac_ne : ∀ g ∈ (Q.roots.map fun r => J - algebraMap K F r), g ≠ 0 := by
    intro g hg
    obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hg
    exact hJc r
  rw [haeval, ord_multiset_prod v _ hfac_ne, Multiset.map_map]
  refine Multiset.sum_eq_zero fun z hz => ?_
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hz
  have hrj : r ≠ j₀ := by
    rintro rfl
    exact hev (Polynomial.IsRoot.def.mp ((mem_roots hQ.ne_zero).mp hr))
  exact ord_sub_algebraMap_eq_zero v hJc hj₀ hrj

end OrdPoly

end SsCountAux

open SsCountAux

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
    (jbar : ↥(ModularCurve.x1FunctionFieldC Ω M)) (hjbar : (jbar : LaurentSeries Ω) = ModularCurve.jqModC Ω) :
    (p - 1) * (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤
      12 * Nat.card {v : AlgebraicCurve.Place Ω ↥(ModularCurve.x1FunctionFieldC Ω M) //
          (jbar : ↥(ModularCurve.x1FunctionFieldC Ω M)) ∈ v.toValuationSubring ∧
            v.evalAt jbar ∈ ModularCurve.ssJSet p Ω} := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨t, ht, htr, hfd, -⟩ :=
    ModularCurve.exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC p M hM hpM Ω
  have htJ : t = jbar := Subtype.ext (ht.trans hjbar.symm)
  subst htJ
  have hμ := ModularCurve.finrank_adjoin_x1FunctionFieldC_eq_index_gamma1_sup_of_isAlgClosed p M hM hpM Ω t hjbar
  haveI := hfd

  have hrat : ∀ v : Place Ω ↥(ModularCurve.x1FunctionFieldC Ω M), v.IsRational := fun v =>
    ModularCurve.isRational_place_x1FunctionFieldC_of_isAlgClosed p M hM hpM Ω v

  have hjr : ∀ r : Ω, jqModC Ω - algebraMap Ω (LaurentSeries Ω) r ≠ 0 := fun r h0 =>
    X_sub_C_ne_zero r (transcendental_iff.mp (transcendental_jqModC Ω) (X - C r)
      (by rw [map_sub, aeval_X, aeval_C]; exact h0))
  have hJc : ∀ a : Ω, t - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) a ≠ 0 := by
    intro a h0
    have h1 := congrArg (fun z : ↥(ModularCurve.x1FunctionFieldC Ω M) => (z : LaurentSeries Ω)) h0
    simp only [AddSubgroupClass.coe_sub, ZeroMemClass.coe_zero] at h1
    apply hjr a
    rw [← hjbar]
    exact h1

  have fib : ∀ a : Ω, ∃ S : Finset (Place Ω ↥(ModularCurve.x1FunctionFieldC Ω M)),
      (∀ v, v ∈ S ↔ 0 < v.ord (t - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) a)) := fun a => by
    obtain ⟨S, hS, -⟩ := AlgebraicCurve.exists_finset_sum_ord_sub_algebraMap_eq_finrank_of_isAlgClosed Ω t htr hfd a
    exact ⟨S, hS⟩
  choose F hF using fib
  have hcardF : ∀ a : Ω, Nat.card {v : Place Ω ↥(ModularCurve.x1FunctionFieldC Ω M) // 0 < v.ord (t - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) a)} = (F a).card := by
    intro a
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun v => (hF a v).symm)), Nat.card_eq_fintype_card,
      Fintype.card_coe]

  have hfibge : ∀ (a : Ω) (e : ℕ), (∀ v : Place Ω ↥(ModularCurve.x1FunctionFieldC Ω M), 0 < v.ord (t - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) a) →
      v.ord (t - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) a) ≤ e) → (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤ e * (F a).card := by
    intro a e he
    have h := AlgebraicCurve.finrank_adjoin_le_mul_natCard_place_ord_sub_algebraMap_pos_of_forall_ord_le Ω t htr hfd a e he
    rwa [hμ, hcardF] at h

  have hdisj : ∀ a b : Ω, a ≠ b → Disjoint (F a) (F b) := by
    intro a b hab
    rw [Finset.disjoint_left]
    intro v hva hvb
    rw [hF] at hva hvb
    have h1 : 1 ≤ v.ord (t - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) a) := hva
    have := ord_sub_algebraMap_eq_zero v hJc h1 (Ne.symm hab)
    omega

  set T : Finset Ω := (ModularCurve.ssJSet_finite p Ω).toFinset with hTdef
  have hTmem : ∀ a, a ∈ T ↔ a ∈ ssJSet p Ω := fun a => by rw [hTdef, Set.Finite.mem_toFinset]
  set U : Finset (Place Ω ↥(ModularCurve.x1FunctionFieldC Ω M)) := T.biUnion F with hUdef
  have hUmem : ∀ v : Place Ω ↥(ModularCurve.x1FunctionFieldC Ω M),
      ((t : ↥(ModularCurve.x1FunctionFieldC Ω M)) ∈ v.toValuationSubring ∧ v.evalAt t ∈ ssJSet p Ω) ↔ v ∈ U := by
    intro v
    rw [hUdef, Finset.mem_biUnion]
    constructor
    · rintro ⟨hmem, hss⟩
      refine ⟨v.evalAt t, (hTmem _).mpr hss, ?_⟩
      rw [hF]
      exact (AlgebraicCurve.Place.mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos v (hrat v) t (v.evalAt t)
        (sub_ne_zero.mp (hJc _))).mp ⟨hmem, rfl⟩
    · rintro ⟨a, haT, hva⟩
      rw [hF] at hva
      obtain ⟨hmem, hev⟩ := (AlgebraicCurve.Place.mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos v (hrat v) t a
        (sub_ne_zero.mp (hJc _))).mpr hva
      exact ⟨hmem, hev ▸ (hTmem a).mp haT⟩
  have hcardU : Nat.card {v : Place Ω ↥(ModularCurve.x1FunctionFieldC Ω M) //
      (t : ↥(ModularCurve.x1FunctionFieldC Ω M)) ∈ v.toValuationSubring ∧ v.evalAt t ∈ ssJSet p Ω} = U.card := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hUmem), Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hcardU]
  have hUsum : U.card = ∑ a ∈ T, (F a).card := by
    rw [hUdef, Finset.card_biUnion]
    intro a _ b _ hab
    exact hdisj a b hab
  have hle_of_mem : ∀ a ∈ T, (F a).card ≤ U.card := by
    intro a ha
    rw [hUsum]
    exact Finset.single_le_sum (f := fun a => (F a).card) (fun _ _ => Nat.zero_le _) ha

  have haff : ∀ (a : Ω) (v : Place Ω ↥(ModularCurve.x1FunctionFieldC Ω M)), 0 < v.ord (t - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) a) → 0 ≤ v.ord t := by
    intro a v hva
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [map_zero, sub_zero] at hva; omega
    · have h1 : 1 ≤ v.ord (t - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) a) := hva
      have h := ord_sub_algebraMap_eq_zero v hJc h1 (r := 0) (Ne.symm ha0)
      rw [map_zero, sub_zero] at h; omega
  by_cases hp5 : 5 ≤ p
  ·
    obtain ⟨m, e₄, e₆, S, hS⟩ := ModularCurve.exists_separable_thetaL_jqModC_pow_mul_aeval_eq p hp5 Ω
    have hbr := ModularCurve.mem_ssJSet_iff_eval_eq_zero_of_thetaL_pow_mul_aeval_eq p hp5 Ω m e₄ e₆ S hS
    obtain ⟨hm, he₄, he₆, hSmonic, hSsep, hSdeg, hS0, hS1728, -⟩ := hS
    have h1728 : (1728 : Ω) ≠ 0 := by
      intro h
      have h2 : ((2 : ℕ) : Ω) ≠ 0 := by
        rw [Ne, CharP.cast_eq_zero_iff Ω p]; intro hd; have := Nat.le_of_dvd two_pos hd; omega
      have h3 : ((3 : ℕ) : Ω) ≠ 0 := by
        rw [Ne, CharP.cast_eq_zero_iff Ω p]; intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
      have : (1728 : Ω) = ((2 : ℕ) : Ω) ^ 6 * ((3 : ℕ) : Ω) ^ 3 := by push_cast; norm_num
      rw [this] at h
      exact (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)) h

    have hfr : ∀ (a : Ω) (v : Place Ω ↥(ModularCurve.x1FunctionFieldC Ω M)), 0 < v.ord (t - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) a) →
        v.ord (t - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) a) ≤ (ModularCurve.jWidth a : ℤ) := by
      intro a v hva
      exact (ModularCurve.ord_sub_algebraMap_eq_jWidth_of_place_x1FunctionFieldC p hp5 Ω M hM hpM t hjbar v
        (haff a v hva) a hva).le

    set Sr : Finset Ω := S.roots.toFinset with hSrdef
    have hSrcard : Sr.card = m := by
      rw [hSrdef, Multiset.toFinset_card_of_nodup (nodup_roots hSsep), ← hSdeg]
      exact (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits S))
    have hSr_mem : ∀ a ∈ Sr, S.eval a = 0 ∧ a ≠ 0 ∧ a ≠ 1728 := by
      intro a ha
      rw [hSrdef, Multiset.mem_toFinset, mem_roots hSmonic.ne_zero] at ha
      refine ⟨ha, ?_, ?_⟩
      · rintro rfl; exact hS0 ha
      · rintro rfl; exact hS1728 ha
    have hroot_ss : ∀ a : Ω, Polynomial.eval a (X ^ e₄ * (X - C (1728 : Ω)) ^ e₆ * S) = 0 → a ∈ T := fun a h =>
      (hTmem a).mpr ((hbr a).mpr h)
    have hSr_T : ∀ a ∈ Sr, a ∈ T := by
      intro a ha
      apply hroot_ss
      rw [eval_mul, (hSr_mem a ha).1, mul_zero]
    have hSr_bound : ∀ a ∈ Sr, (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤ (F a).card := by
      intro a ha
      have h := hfibge a 1 (fun v hv => by
        have := hfr a v hv; rw [jWidth_of_ne (hSr_mem a ha).2.1 (hSr_mem a ha).2.2] at this; exact_mod_cast this)
      simpa using h

    have hsumSr : m * (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤ ∑ a ∈ Sr, (F a).card := by
      rw [← hSrcard]
      have := Finset.card_nsmul_le_sum Sr (fun a => (F a).card) _ hSr_bound
      simpa using this
    have hSr_sub : ∑ a ∈ Sr, (F a).card ≤ ∑ a ∈ T, (F a).card :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun a ha => hSr_T a ha) (fun _ _ _ => Nat.zero_le _)

    have h0_notin : (0 : Ω) ∉ Sr := fun h => (hSr_mem 0 h).2.1 rfl
    have h1728_notin : (1728 : Ω) ∉ Sr := fun h => (hSr_mem 1728 h).2.2 rfl

    have hbig : ∑ a ∈ Sr, (F a).card + (if e₄ = 1 then (F 0).card else 0) + (if e₆ = 1 then (F 1728).card else 0)
        ≤ ∑ a ∈ T, (F a).card := by
      set R0 : Finset Ω := if e₄ = 1 then {0} else ∅ with hR0
      set R1 : Finset Ω := if e₆ = 1 then {1728} else ∅ with hR1
      have hR0T : ∀ a ∈ R0, a ∈ T := by
        intro a ha; rw [hR0] at ha; split_ifs at ha with h
        · rw [Finset.mem_singleton] at ha; subst ha
          apply hroot_ss; rw [h]; simp
        · simp at ha
      have hR1T : ∀ a ∈ R1, a ∈ T := by
        intro a ha; rw [hR1] at ha; split_ifs at ha with h
        · rw [Finset.mem_singleton] at ha; subst ha
          apply hroot_ss; rw [h]; simp
        · simp at ha
      have hd1 : Disjoint Sr R0 := by
        rw [hR0]; split_ifs
        · exact Finset.disjoint_singleton_right.mpr h0_notin
        · exact Finset.disjoint_empty_right _
      have hd2 : Disjoint (Sr ∪ R0) R1 := by
        rw [hR1]; split_ifs
        · rw [Finset.disjoint_singleton_right, Finset.mem_union, not_or]
          refine ⟨h1728_notin, ?_⟩
          rw [hR0]; split_ifs
          · rw [Finset.mem_singleton]; exact h1728
          · exact Finset.notMem_empty _
        · exact Finset.disjoint_empty_right _
      have hsub : Sr ∪ R0 ∪ R1 ⊆ T := by
        intro a ha
        rcases Finset.mem_union.mp ha with ha | ha
        · rcases Finset.mem_union.mp ha with ha | ha
          · exact hSr_T a ha
          · exact hR0T a ha
        · exact hR1T a ha
      have hsum0 : ∑ a ∈ R0, (F a).card = (if e₄ = 1 then (F 0).card else 0) := by
        rw [hR0]; split_ifs <;> simp
      have hsum1 : ∑ a ∈ R1, (F a).card = (if e₆ = 1 then (F 1728).card else 0) := by
        rw [hR1]; split_ifs <;> simp
      calc ∑ a ∈ Sr, (F a).card + (if e₄ = 1 then (F 0).card else 0) + (if e₆ = 1 then (F 1728).card else 0)
          = ∑ a ∈ Sr ∪ R0 ∪ R1, (F a).card := by
            rw [Finset.sum_union hd2, Finset.sum_union hd1, hsum0, hsum1]
        _ ≤ ∑ a ∈ T, (F a).card := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

    have h0b : e₄ = 1 → (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤ 3 * (F 0).card := by
      intro h
      exact hfibge 0 3 (fun v hv => by have := hfr 0 v hv; rw [jWidth_of_eq_zero rfl] at this; exact_mod_cast this)
    have h1728b : e₆ = 1 → (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤ 2 * (F 1728).card := by
      intro h
      exact hfibge 1728 2 (fun v hv => by
        have := hfr 1728 v hv; rw [jWidth_of_eq_1728 rfl h1728] at this; exact_mod_cast this)

    rw [hUsum, ← hm]
    set μ := (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he₄ with h4 | h4 <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he₆ with h6 | h6 <;>
      simp only [h4, h6, if_true, if_false, Nat.zero_ne_one, add_zero] at hbig ⊢
    · nlinarith [hsumSr, hbig]
    · nlinarith [hsumSr, hbig, h1728b h6]
    · nlinarith [hsumSr, hbig, h0b h4]
    · nlinarith [hsumSr, hbig, h0b h4, h1728b h6]
  ·
    push Not at hp5
    have h0ss : (0 : Ω) ∈ ssJSet p Ω := ModularCurve.zero_mem_ssJSet_of_lt_five (q := p) hp5
    have h0T : (0 : Ω) ∈ T := (hTmem 0).mpr h0ss
    have he : ∀ v : Place Ω ↥(ModularCurve.x1FunctionFieldC Ω M), 0 < v.ord (t - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) 0) →
        v.ord (t - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) 0) ≤ ((12 / (p - 1) : ℕ) : ℤ) := by
      intro v hv
      rw [map_zero, sub_zero] at hv ⊢
      have hd := ModularCurve.ord_dvd_twelve_div_sub_one_of_ord_pos_x1FunctionFieldC_of_lt_five p hp5 M hpM Ω t hjbar v hv
      apply Int.le_of_dvd _ hd
      have h2 := hp.two_le
      exact_mod_cast Nat.div_pos (by omega) (by omega)
    have hb := hfibge 0 (12 / (p - 1)) he
    have hF0 := hle_of_mem 0 h0T
    have h2 := hp.two_le
    have hp23 : p = 2 ∨ p = 3 := by
      have h4 : p ≠ 4 := by intro h; rw [h] at hp; norm_num at hp
      omega
    rcases hp23 with rfl | rfl
    · norm_num at hb ⊢; omega
    · norm_num at hb ⊢; omega

end S_ModularCurve_sub_one_mul_index_gamma1_le_twelve_mul_natCard_evalAt_mem_ssJSet_x1FunctionFieldC
end P2MW
export P2MW.S_ModularCurve_sub_one_mul_index_gamma1_le_twelve_mul_natCard_evalAt_mem_ssJSet_x1FunctionFieldC (solution)
