-- Prove2me | solution 1 for ModularCurve.sub_one_dvd_ord_sub_one_of_coe_eq_hasseRootFn_pow_of_eval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/8c972339-2eab-5669-864d-b516f43001ae

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_ModularCurve_thetaL_jq_pow_six
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_pow_twelve_mul_pow_sub_one_eq_of_coe_eq_hasseRootFn_pow
import Theorems.Thm_ModularCurve_twelve_dvd_ord_of_coe_eq_div_of_ord_nonneg_x1FunctionFieldC
import Theorems.Thm_ModularCurve_ord_sub_algebraMap_eq_jWidth_of_place_x1FunctionFieldC
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_sub_one_dvd_ord_sub_one_of_coe_eq_hasseRootFn_pow_of_eval_eq_zero
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub"
p2m_attr_erase "instance" "KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"
p2m_attr_erase "simp" "CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq"
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0"
p2m_attr_erase "simp" "ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec"

set_option autoImplicit false

open AlgebraicCurve ModularCurve Polynomial

namespace HasseOrdBody

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

section ThetaR

open HahnSeries

variable {R : Type*} [CommRing R]

noncomputable def thetaR (f : LaurentSeries R) : LaurentSeries R :=
  single (1 : ℤ) (1 : R) * LaurentSeries.derivative R f

theorem coeff_single_one_mul_derivative_add_one (f : LaurentSeries R) (m : ℤ) :
    (single (1 : ℤ) (1 : R) * LaurentSeries.derivative R f).coeff (m + 1) =
      ((m + 1 : ℤ) : R) * f.coeff (m + 1) := by
  rw [HahnSeries.coeff_single_mul_add, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff, Ring.choose_one_right, zsmul_eq_mul]
  simp only [Nat.cast_one]

theorem coeff_single_one_mul_derivative (f : LaurentSeries R) (n : ℤ) :
    (single (1 : ℤ) (1 : R) * LaurentSeries.derivative R f).coeff n = (n : R) * f.coeff n := by
  have h := coeff_single_one_mul_derivative_add_one f (n - 1)
  simp only [sub_add_cancel] at h
  exact h

theorem coeff_thetaR (f : LaurentSeries R) (n : ℤ) : (thetaR f).coeff n = (n : R) * f.coeff n :=
  coeff_single_one_mul_derivative f n

theorem laurentMap_thetaR {k : Type*} [Field k] (φ : R →+* k) (f : LaurentSeries R) :
    laurentMap φ (thetaR f) = thetaL k (laurentMap φ f) := by
  ext n
  rw [thetaL_apply, coeff_single_one_mul_derivative, laurentMap_coeff, coeff_thetaR, map_mul,
    map_intCast, laurentMap_coeff]

end ThetaR

theorem laurentMap_jqInt_eq_jqModC (k : Type*) [CommRing k] :
    laurentMap (Int.castRingHom k) jqInt = jqModC k := by
  rw [jqInt, map_mul, laurentMap_single, laurentMap_ofPowerSeries, map_one]
  rfl

section QSeries

variable (κ : Type*) [Field κ]

theorem theta_pow_six :
    thetaL κ (jqModC κ) ^ 6 = jqModC κ ^ 4 * (jqModC κ - 1728) ^ 3 *
      intSeriesC κ (PowerSeries.X * dedekindEtaUnit) := by
  have hZ : thetaR jqInt ^ 6 = jqInt ^ 4 * (jqInt - 1728) ^ 3 *
      (HahnSeries.single (1 : ℤ) (1 : ℤ) * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnit) := by
    apply laurentMap_injective (f := Int.castRingHom ℚ) Int.cast_injective
    rw [map_pow, laurentMap_thetaR, map_mul, map_mul, map_mul, map_pow, map_pow, map_sub,
      laurentMap_single, laurentMap_ofPowerSeries, laurentMap_jqInt, map_ofNat, map_one]
    exact thetaL_jq_pow_six
  have h := congrArg (laurentMap (Int.castRingHom κ)) hZ
  rw [map_pow, laurentMap_thetaR, map_mul, map_mul, map_mul, map_pow, map_pow, map_sub,
    laurentMap_single, laurentMap_ofPowerSeries, laurentMap_jqInt_eq_jqModC, map_ofNat, map_one] at h
  rw [h, intSeriesC, map_mul, PowerSeries.map_X, map_mul, HahnSeries.ofPowerSeries_X]

theorem intSeriesC_pow (q : PowerSeries ℤ) (n : ℕ) : intSeriesC κ (q ^ n) = intSeriesC κ q ^ n := by
  induction n with
  | zero => simp [intSeriesC]
  | succ n ih => rw [pow_succ, intSeriesC_mul, ih, pow_succ]

theorem intSeriesC_X : intSeriesC κ PowerSeries.X = HahnSeries.single 1 1 := by
  rw [intSeriesC, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]

theorem jqModC_mul_delta :
    jqModC κ * intSeriesC κ (PowerSeries.X * dedekindEtaUnit) = intSeriesC κ eisenstein4 ^ 3 := by
  have hj : jqModC κ = HahnSeries.single (-1 : ℤ) (1 : κ) * intSeriesC κ jNum := rfl
  calc jqModC κ * intSeriesC κ (PowerSeries.X * dedekindEtaUnit)
      = (HahnSeries.single (-1 : ℤ) (1 : κ) * HahnSeries.single (1 : ℤ) (1 : κ)) *
          (intSeriesC κ jNum * intSeriesC κ dedekindEtaUnit) := by
        rw [hj, intSeriesC_mul, intSeriesC_X]; ring
    _ = intSeriesC κ (jNum * dedekindEtaUnit) := by
        rw [HahnSeries.single_mul_single, neg_add_cancel, mul_one, ← intSeriesC_mul]
        rw [show (HahnSeries.single (0 : ℤ) (1 : κ)) = 1 from rfl, one_mul]
    _ = intSeriesC κ eisenstein4 ^ 3 := by
        rw [jNum, mul_assoc, mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, mul_one, intSeriesC_pow]

theorem intSeriesC_ne_zero_of_constantCoeff {q : PowerSeries ℤ} (hq : PowerSeries.constantCoeff q = 1) :
    intSeriesC κ q ≠ 0 := by
  intro h0
  have h1 := HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm)
  have h2 := congrArg (PowerSeries.coeff 0) h1
  rw [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, hq, map_one, map_zero] at h2
  exact one_ne_zero h2

theorem eisenstein4_ne_zero : intSeriesC κ eisenstein4 ≠ 0 :=
  intSeriesC_ne_zero_of_constantCoeff κ constantCoeff_eisenstein4

theorem eisenstein4_eq_mk_sigma :
    eisenstein4 = PowerSeries.mk fun n => if n = 0 then (1 : ℤ) else 240 * (ArithmeticFunction.sigma 3 n : ℤ) := by
  ext n
  simp only [eisenstein4, PowerSeries.coeff_mk, ArithmeticFunction.sigma_apply, Nat.cast_sum, Nat.cast_pow]

theorem aeval_jqModC_ne_zero {Q : κ[X]} (hQ : Q ≠ 0) : aeval (jqModC κ) Q ≠ 0 :=
  fun h => ModularCurve.transcendental_jqModC κ ⟨Q, hQ, h⟩

theorem cast_1728_ne_zero (q : ℕ) (hp : q.Prime) (hq : 5 ≤ q) [CharP κ q] : (1728 : κ) ≠ 0 := by
  intro h
  have h' : ((1728 : ℕ) : κ) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff κ q] at h'
  have : q ∣ 2 ^ 6 * 3 ^ 3 := by norm_num at h' ⊢; exact h'
  rcases (Nat.Prime.dvd_mul hp).mp this with h2 | h3
  · have := Nat.le_of_dvd (by norm_num) (Nat.Prime.dvd_of_dvd_pow hp h2); omega
  · have := Nat.le_of_dvd (by norm_num) (Nat.Prime.dvd_of_dvd_pow hp h3); omega

end QSeries

theorem elim {L : Type*} [Field L] {T j k D E S σ : L} {N m e₄ e₆ : ℕ}
    (hN : N = 6 * m + 2 * e₄ + 3 * e₆) (hσ : σ ^ 12 = 1)
    (hS : T ^ N * S = σ * (j ^ (4 * m + e₄ + 2 * e₆) * k ^ (3 * m + e₄ + e₆)))
    (h6 : T ^ 6 = j ^ 4 * k ^ 3 * D) (hE : j * D = E ^ 3) (hj : j ≠ 0) (hk : k ≠ 0) :
    E ^ (6 * N) * S ^ 12 * k ^ (6 * e₆) = j ^ (12 * m + 6 * e₆) := by
  have eq1 : E ^ (6 * N) = j ^ (2 * N) * D ^ (2 * N) := by
    rw [show E ^ (6 * N) = (E ^ 3) ^ (2 * N) by ring, ← hE, mul_pow]
  have eq2 : D ^ (2 * N) * (j ^ (8 * N) * k ^ (6 * N)) = T ^ (12 * N) := by
    rw [show T ^ (12 * N) = (T ^ 6) ^ (2 * N) by ring, h6]; ring
  have eq3 : T ^ (12 * N) * S ^ 12 = j ^ (12 * (4 * m + e₄ + 2 * e₆)) * k ^ (12 * (3 * m + e₄ + e₆)) := by
    calc T ^ (12 * N) * S ^ 12 = (T ^ N * S) ^ 12 := by ring
      _ = (σ * (j ^ (4 * m + e₄ + 2 * e₆) * k ^ (3 * m + e₄ + e₆))) ^ 12 := by rw [hS]
      _ = _ := by rw [mul_pow, hσ, one_mul]; ring
  have key : E ^ (6 * N) * S ^ 12 * k ^ (6 * e₆) * (j ^ (8 * N) * k ^ (6 * N)) =
      j ^ (12 * m + 6 * e₆) * (j ^ (8 * N) * k ^ (6 * N)) := by
    calc E ^ (6 * N) * S ^ 12 * k ^ (6 * e₆) * (j ^ (8 * N) * k ^ (6 * N))
        = j ^ (2 * N) * k ^ (6 * e₆) * (D ^ (2 * N) * (j ^ (8 * N) * k ^ (6 * N))) * S ^ 12 := by
          rw [eq1]; ring
      _ = j ^ (2 * N) * k ^ (6 * e₆) * (T ^ (12 * N) * S ^ 12) := by rw [eq2]; ring
      _ = j ^ (2 * N) * k ^ (6 * e₆) * (j ^ (12 * (4 * m + e₄ + 2 * e₆)) * k ^ (12 * (3 * m + e₄ + e₆))) := by
          rw [eq3]
      _ = j ^ (12 * m + 6 * e₆) * (j ^ (8 * N) * k ^ (6 * N)) := by subst hN; ring
  exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero _ hj) (pow_ne_zero _ hk)) key

theorem final {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] [Field F] [Algebra K F]
    (x : Place K F) {J u b : F} {S : K[X]} {m e₄ e₆ N : ℕ} (he₄ : e₄ ≤ 1) (he₆ : e₆ ≤ 1)
    (hNm : N = 6 * m + 2 * e₄ + 3 * e₆) (hSmonic : S.Monic) (hS0 : S.eval 0 ≠ 0)
    (hS1728 : S.eval 1728 ≠ 0) (h1728 : (1728 : K) ≠ 0)
    (hJc : ∀ r : K, J - algebraMap K F r ≠ 0) (hSJ : aeval J S ≠ 0) (hb0 : b ≠ 0) (hu0 : u ≠ 0)
    (hK : b ^ 12 * J ^ (12 * m + 6 * e₆) =
      u ^ (6 * N) * (J - algebraMap K F 1728) ^ (6 * e₆) * (aeval J S) ^ 12)
    (hxu : 3 * x.ord u = x.ord J) {j₀ : K} (hj₀ : 1 ≤ x.ord (J - algebraMap K F j₀)) :
    (jWidth j₀ : ℤ) * x.ord b = x.ord (aeval J (X ^ e₄ * (X - C (1728 : K)) ^ e₆ * S)) := by
  have hJ0 : J ≠ 0 := by
    have h := hJc 0
    rwa [map_zero, sub_zero] at h
  have hJ' : J - algebraMap K F 1728 ≠ 0 := hJc 1728

  have hord := congrArg x.ord hK
  rw [x.ord_mul (pow_ne_zero _ hb0) (pow_ne_zero _ hJ0), ord_pow', ord_pow',
    x.ord_mul (mul_ne_zero (pow_ne_zero _ hu0) (pow_ne_zero _ hJ')) (pow_ne_zero _ hSJ),
    x.ord_mul (pow_ne_zero _ hu0) (pow_ne_zero _ hJ'), ord_pow', ord_pow', ord_pow'] at hord
  have hmain : 12 * x.ord b = 4 * (e₄ : ℤ) * x.ord J +
      6 * (e₆ : ℤ) * x.ord (J - algebraMap K F 1728) + 12 * x.ord (aeval J S) := by
    subst hNm
    push_cast at hord
    linear_combination hord + (12 * (m : ℤ) + 4 * e₄ + 6 * e₆) * hxu

  have hP : aeval J (X ^ e₄ * (X - C (1728 : K)) ^ e₆ * S) =
      J ^ e₄ * (J - algebraMap K F 1728) ^ e₆ * aeval J S := by
    rw [map_mul, map_mul, map_pow, map_pow, map_sub, aeval_X, aeval_C]
  have hordP : x.ord (aeval J (X ^ e₄ * (X - C (1728 : K)) ^ e₆ * S)) =
      (e₄ : ℤ) * x.ord J + (e₆ : ℤ) * x.ord (J - algebraMap K F 1728) + x.ord (aeval J S) := by
    rw [hP, x.ord_mul (mul_ne_zero (pow_ne_zero _ hJ0) (pow_ne_zero _ hJ')) hSJ,
      x.ord_mul (pow_ne_zero _ hJ0) (pow_ne_zero _ hJ'), ord_pow', ord_pow']
  rw [hordP]

  rcases eq_or_ne j₀ 0 with rfl | hj₀0
  · have hk0 : x.ord (J - algebraMap K F 1728) = 0 := ord_sub_algebraMap_eq_zero x hJc hj₀ h1728
    have hS' : x.ord (aeval J S) = 0 := ord_aeval_eq_zero x hJc hj₀ hSmonic hS0
    rw [jWidth_of_eq_zero rfl, hk0, hS']
    rw [hk0, hS'] at hmain
    interval_cases e₄ <;> push_cast at hmain ⊢ <;> omega
  · rcases eq_or_ne j₀ 1728 with rfl | hj₀1728
    · have hJord : x.ord J = 0 := by
        have h := ord_sub_algebraMap_eq_zero x hJc hj₀ (r := 0) h1728.symm
        rwa [map_zero, sub_zero] at h
      have hS' : x.ord (aeval J S) = 0 := ord_aeval_eq_zero x hJc hj₀ hSmonic hS1728
      rw [jWidth_of_eq_1728 rfl h1728, hJord, hS']
      rw [hJord, hS'] at hmain
      interval_cases e₆ <;> push_cast at hmain ⊢ <;> omega
    · have hJord : x.ord J = 0 := by
        have h := ord_sub_algebraMap_eq_zero x hJc hj₀ (r := 0) (Ne.symm hj₀0)
        rwa [map_zero, sub_zero] at h
      have hk0 : x.ord (J - algebraMap K F 1728) = 0 :=
        ord_sub_algebraMap_eq_zero x hJc hj₀ (Ne.symm hj₀1728)
      rw [jWidth_of_ne hj₀0 hj₀1728, hJord, hk0]
      rw [hJord, hk0] at hmain
      push_cast at hmain ⊢
      omega

end HasseOrdBody

namespace IszeAux

open HasseOrdBody CongruenceSubgroup
open scoped MatrixGroups ModularForm

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_aeval_eq_ord_sub [IsAlgClosed K] [DecidableEq K] (v : Place K F) {J : F}
    (hJc : ∀ r : K, J - algebraMap K F r ≠ 0)
    {j₀ : K} (hj₀ : 1 ≤ v.ord (J - algebraMap K F j₀)) {Q : K[X]} (hQ : Q.Monic) (hsep : Q.Separable)
    (hev : Q.eval j₀ = 0) : v.ord (aeval J Q) = v.ord (J - algebraMap K F j₀) := by
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
  have hmem : j₀ ∈ Q.roots := (mem_roots hQ.ne_zero).mpr hev
  have hnodup : Q.roots.Nodup := nodup_roots hsep
  rw [haeval, ord_multiset_prod v _ hfac_ne, Multiset.map_map, ← Multiset.cons_erase hmem, Multiset.map_cons,
    Multiset.sum_cons]
  have hrest : ((Q.roots.erase j₀).map (Function.comp v.ord fun r => J - algebraMap K F r)).sum = 0 := by
    refine Multiset.sum_eq_zero fun z hz => ?_
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hz
    have hrj : r ≠ j₀ := ((hnodup.mem_erase_iff).mp hr).1
    exact ord_sub_algebraMap_eq_zero v hJc hj₀ hrj
  rw [hrest, add_zero]
  rfl

noncomputable def D12 (M : ℕ) : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrictForm (Subgroup.map_le_range _ _) (CuspForm.discriminant : ModularForm 𝒮ℒ 12)

theorem isIntegralQExp_D12 (M : ℕ) : IsIntegralQExp (D12 M : UpperHalfPlane → ℂ) (PowerSeries.X * dedekindEtaUnit) :=
  ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm

theorem one_mem_strictPeriods_Gamma1 (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, ?_, ?_⟩
  · exact (by rw [Gamma1_mem]; simp [ModularGroup.coe_T] : ModularGroup.T ∈ Gamma1 N)
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom]

theorem exists_T (κ : Type) [Field κ] (M : ℕ) (w : IntegralWeightOneForm κ M) :
    ∃ T : ↥(x1FunctionFieldC κ M),
      (T : LaurentSeries κ) = intSeriesC κ (w.series ^ 12) / intSeriesC κ (PowerSeries.X * dedekindEtaUnit) := by
  let W12 : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 12 :=
    (w.form.pow 12).mcast (by norm_num)
  have hW12 : IsIntegralQExp (⇑W12) (w.series ^ 12) := by
    rw [IsIntegralQExp, map_pow]
    show _ = UpperHalfPlane.qExpansion 1 (⇑((w.form.pow 12).mcast _))
    rw [ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos (one_mem_strictPeriods_Gamma1 M),
      ← w.isIntegralQExp]
  have hΔ : intSeriesC κ (PowerSeries.X * dedekindEtaUnit) ≠ 0 := by
    rw [intSeriesC_mul, HasseOrdBody.intSeriesC_X]
    refine mul_ne_zero ?_ (HasseOrdBody.intSeriesC_ne_zero_of_constantCoeff κ constantCoeff_dedekindEtaUnit)
    intro h; exact one_ne_zero ((HahnSeries.single_eq_zero_iff).mp h)
  exact ⟨⟨_, div_mem_qExpFunctionFieldC W12 (D12 M) hW12 (isIntegralQExp_D12 M) hΔ⟩, rfl⟩

end IszeAux

open HasseOrdBody IszeAux

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ]
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (w : ModularCurve.IntegralWeightOneForm κ M)
    (m e₄ e₆ : ℕ) (S : Polynomial κ)
    (hS : 12 * m + 4 * e₄ + 6 * e₆ = p - 1 ∧ e₄ ≤ 1 ∧ e₆ ≤ 1 ∧
      S.Monic ∧ S.Separable ∧ S.natDegree = m ∧ S.eval 0 ≠ 0 ∧ S.eval 1728 ≠ 0 ∧
      thetaL κ (jqModC κ) ^ ((p - 1) / 2) * Polynomial.aeval (jqModC κ) S =
        (-1) ^ ((p - 1) / 2) *
          (jqModC κ ^ (4 * m + e₄ + 2 * e₆) * (jqModC κ - 1728) ^ (3 * m + e₄ + e₆)))
    (J : ↥(ModularCurve.x1FunctionFieldC κ M)) (hJ : (J : LaurentSeries κ) = jqModC κ)
    (b : ↥(ModularCurve.x1FunctionFieldC κ M)) (hb : (b : LaurentSeries κ) = w.hasseRootFn ^ (p - 1))
    (x : Place κ ↥(ModularCurve.x1FunctionFieldC κ M)) (j₀ : κ)
    (hj₀ : 1 ≤ x.ord (J - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) j₀))
    (hss : Polynomial.eval j₀ (X ^ e₄ * (X - C (1728 : κ)) ^ e₆ * S) = 0) :
    ((p - 1 : ℕ) : ℤ) ∣ x.ord b - 1 := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨hm, he₄, he₆, hSmonic, hSsep, -, hS0, hS1728, -⟩ := id hS
  have h1728 : (1728 : κ) ≠ 0 := cast_1728_ne_zero κ p hp hp5
  have hw0 : intSeriesC κ w.series ≠ 0 := w.intSeriesC_ne_zero
  have hΔ : intSeriesC κ (PowerSeries.X * dedekindEtaUnit) ≠ 0 := by
    rw [intSeriesC_mul, intSeriesC_X]
    refine mul_ne_zero ?_ (intSeriesC_ne_zero_of_constantCoeff κ constantCoeff_dedekindEtaUnit)
    intro h; exact one_ne_zero ((HahnSeries.single_eq_zero_iff).mp h)

  obtain ⟨T, hT⟩ := IszeAux.exists_T κ M w
  have hid := ModularCurve.pow_twelve_mul_pow_sub_one_eq_of_coe_eq_hasseRootFn_pow p hp5 κ M (by omega) hpM w
    m e₄ e₆ S hS J hJ b hb T hT

  have hj : jqModC κ ≠ 0 := by
    have h := aeval_jqModC_ne_zero κ (Q := X) X_ne_zero
    rwa [aeval_X] at h
  have hjr : ∀ r : κ, jqModC κ - algebraMap κ (LaurentSeries κ) r ≠ 0 := fun r => by
    have h := aeval_jqModC_ne_zero κ (Q := X - C r) (X_sub_C_ne_zero r)
    rwa [map_sub, aeval_X, aeval_C] at h
  have hcoealg : ∀ r : κ, ((algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) r : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ) =
      algebraMap κ (LaurentSeries κ) r := fun r => rfl
  have hcoeaeval : ∀ Q : κ[X], ((aeval J Q : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ) = aeval (jqModC κ) Q := fun Q => by
    rw [← hJ, show ((aeval J Q : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ) =
      (ModularCurve.x1FunctionFieldC κ M).val (aeval J Q) from rfl, ← aeval_algHom_apply]
    rfl
  have hne_of_coe : ∀ {z : ↥(ModularCurve.x1FunctionFieldC κ M)}, (z : LaurentSeries κ) ≠ 0 → z ≠ 0 :=
    fun h h0 => h (by rw [h0]; rfl)
  have hJc : ∀ r : κ, J - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) r ≠ 0 := fun r =>
    hne_of_coe (by rw [AddSubgroupClass.coe_sub, hcoealg, hJ]; exact hjr r)
  have hJ0 : J ≠ 0 := hne_of_coe (by rw [hJ]; exact hj)
  have hJ' : J - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728 ≠ 0 := hJc 1728
  have hSJ : aeval J S ≠ 0 := hne_of_coe (by rw [hcoeaeval]; exact aeval_jqModC_ne_zero κ hSmonic.ne_zero)
  have hb0 : b ≠ 0 := hne_of_coe (by rw [hb]; exact pow_ne_zero _ w.hasseRootFn_ne_zero)
  have hT0 : T ≠ 0 := hne_of_coe (by rw [hT]; exact div_ne_zero (by rw [intSeriesC_pow]; exact pow_ne_zero _ hw0) hΔ)

  have hx : 0 ≤ x.ord J := by
    rcases eq_or_ne j₀ 0 with rfl | hj₀0
    · rw [map_zero, sub_zero] at hj₀; omega
    · have h := ord_sub_algebraMap_eq_zero x hJc hj₀ (r := 0) (Ne.symm hj₀0)
      rw [map_zero, sub_zero] at h; omega

  have hord := congrArg x.ord hid
  rw [x.ord_mul (pow_ne_zero _ hb0) (pow_ne_zero _ hT0), ord_pow', ord_pow',
    x.ord_mul (mul_ne_zero (pow_ne_zero _ hJ0) (pow_ne_zero _ hJ')) (pow_ne_zero _ hSJ),
    x.ord_mul (pow_ne_zero _ hJ0) (pow_ne_zero _ hJ'), ord_pow', ord_pow', ord_pow'] at hord

  obtain ⟨t, ht⟩ := ModularCurve.twelve_dvd_ord_of_coe_eq_div_of_ord_nonneg_x1FunctionFieldC p κ M hM hpM w J hJ T hT x hx
  have hfr := ModularCurve.ord_sub_algebraMap_eq_jWidth_of_place_x1FunctionFieldC p hp5 κ M hM hpM J hJ x hx j₀ hj₀

  have hRHS : 4 * (e₄ : ℤ) * x.ord J + 6 * (e₆ : ℤ) * x.ord (J - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728) +
      12 * x.ord (aeval J S) = 12 := by
    rcases eq_or_ne j₀ 0 with rfl | hj₀0
    ·
      have hk0 : x.ord (J - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728) = 0 := ord_sub_algebraMap_eq_zero x hJc hj₀ h1728
      have hS' : x.ord (aeval J S) = 0 := ord_aeval_eq_zero x hJc hj₀ hSmonic hS0
      have hJord : x.ord J = 3 := by
        have h := hfr; rw [map_zero, sub_zero, jWidth_of_eq_zero rfl] at h; exact_mod_cast h
      have he₄1 : e₄ = 1 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he₄ with h0 | h1
        · exfalso; subst h0
          rw [pow_zero, one_mul, eval_mul, eval_pow, eval_sub, eval_X, eval_C, zero_sub] at hss
          exact (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr h1728)) hS0) hss
        · exact h1
      rw [hk0, hS', hJord, he₄1]; norm_num
    · rcases eq_or_ne j₀ 1728 with rfl | hj₀1728
      ·
        have hJord : x.ord J = 0 := by
          have h := ord_sub_algebraMap_eq_zero x hJc hj₀ (r := 0) h1728.symm
          rwa [map_zero, sub_zero] at h
        have hS' : x.ord (aeval J S) = 0 := ord_aeval_eq_zero x hJc hj₀ hSmonic hS1728
        have hk : x.ord (J - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728) = 2 := by
          have h := hfr; rw [jWidth_of_eq_1728 rfl h1728] at h; exact_mod_cast h
        have he₆1 : e₆ = 1 := by
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he₆ with h0 | h1
          · exfalso; subst h0
            rw [pow_zero, mul_one, eval_mul, eval_pow, eval_X] at hss
            exact (mul_ne_zero (pow_ne_zero _ h1728) hS1728) hss
          · exact h1
        rw [hJord, hS', hk, he₆1]; norm_num
      ·
        have hJord : x.ord J = 0 := by
          have h := ord_sub_algebraMap_eq_zero x hJc hj₀ (r := 0) (Ne.symm hj₀0)
          rwa [map_zero, sub_zero] at h
        have hk0 : x.ord (J - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728) = 0 :=
          ord_sub_algebraMap_eq_zero x hJc hj₀ (Ne.symm hj₀1728)
        have hSev : S.eval j₀ = 0 := by
          rw [eval_mul, eval_mul, eval_pow, eval_pow, eval_sub, eval_X, eval_C] at hss
          rcases mul_eq_zero.mp hss with h | h
          · exfalso
            exact (mul_ne_zero (pow_ne_zero _ hj₀0) (pow_ne_zero _ (sub_ne_zero.mpr hj₀1728))) h
          · exact h
        have hS' : x.ord (aeval J S) = 1 := by
          rw [ord_aeval_eq_ord_sub x hJc hj₀ hSmonic hSsep hSev, hfr, jWidth_of_ne hj₀0 hj₀1728]; rfl
        rw [hJord, hk0, hS']; norm_num

  generalize hP : ((p - 1 : ℕ) : ℤ) = P at hord ⊢
  push_cast at hord
  rw [hRHS, ht] at hord
  refine ⟨-t, ?_⟩
  rw [mul_neg]
  have key : 12 * x.ord b + 12 * (P * t) = 12 := by linear_combination hord
  generalize P * t = E at key ⊢
  omega

end S_ModularCurve_sub_one_dvd_ord_sub_one_of_coe_eq_hasseRootFn_pow_of_eval_eq_zero
end P2MW
export P2MW.S_ModularCurve_sub_one_dvd_ord_sub_one_of_coe_eq_hasseRootFn_pow_of_eval_eq_zero (solution)
