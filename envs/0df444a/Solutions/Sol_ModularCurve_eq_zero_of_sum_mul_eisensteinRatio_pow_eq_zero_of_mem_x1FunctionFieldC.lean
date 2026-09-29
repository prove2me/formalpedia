-- Prove2me | solution 1 for ModularCurve.eq_zero_of_sum_mul_eisensteinRatio_pow_eq_zero_of_mem_x1FunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/a48af073-d666-5910-bad3-0d4ddc123ab4

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Theorems.Thm_ModularForm_exists_gamma1_isIntegralQExp_eisenstein_four_six
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_isKummerGenerator_hasseRootFn_and_relfinrank_igusaFunctionFieldX1C
import Theorems.Thm_ModularCurve_nonempty_integralWeightOneForm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eq_zero_of_sum_mul_eisensteinRatio_pow_eq_zero_of_mem_x1FunctionFieldC
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub"
p2m_attr_erase "instance" "KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec"
p2m_attr_erase "simp" "CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃"
p2m_attr_erase "simp" "ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero"
p2m_attr_erase "simp" "Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"

set_option autoImplicit false

open scoped ArithmeticFunction.sigma
p2m_open "ModularCurve P2MW.S_ModularCurve_eq_zero_of_sum_mul_eisensteinRatio_pow_eq_zero_of_mem_x1FunctionFieldC.ModularCurve CongruenceSubgroup UpperHalfPlane"
open scoped MatrixGroups ModularForm

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "IsIntegralQExp intSeriesC intSeriesC_mul div_mem_qExpFunctionFieldC x1FunctionFieldC dedekindEtaUnit constantCoeff_dedekindEtaUnit IntegralWeightOneForm IntegralWeightOneForm.hasseRootFn IgusaCover.igusaFunctionField IgusaCover.le_igusaFunctionField IgusaCover.IsKummerGenerator qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit isKummerGenerator_hasseRootFn_and_relfinrank_igusaFunctionFieldX1C nonempty_integralWeightOneForm"
namespace EisRatio
p2m_open "ModularCurve"

def P4 : PowerSeries ℤ := PowerSeries.mk fun n => if n = 0 then 1 else 240 * (σ 3 n : ℤ)

def P6 : PowerSeries ℤ := PowerSeries.mk fun n => if n = 0 then 1 else -504 * (σ 5 n : ℤ)

def gbar (κ : Type) [Field κ] : LaurentSeries κ :=
  ModularCurve.intSeriesC κ P4 * ModularCurve.intSeriesC κ P6 /
    ModularCurve.intSeriesC κ (PowerSeries.X * ModularCurve.dedekindEtaUnit)

private def restrictSL {k : ℤ} (F : ModularForm 𝒮ℒ k) (Γ : Subgroup SL(2, ℤ)) :
    ModularForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k where
  toFun := ⇑F
  slash_action_eq' A hA := SlashInvariantFormClass.slash_action_eq F A (Subgroup.map_le_range _ _ hA)
  holo' := ModularFormClass.holo F
  bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps F (hc.mono (Subgroup.map_le_range _ _))

@[scoped simp] private theorem coe_restrictSL {k : ℤ} (F : ModularForm 𝒮ℒ k) (Γ : Subgroup SL(2, ℤ)) :
    (⇑(restrictSL F Γ) : ℍ → ℂ) = ⇑F := rfl

private def ofCuspSL {k : ℤ} (F : CuspForm 𝒮ℒ k) : ModularForm 𝒮ℒ k where
  toFun := ⇑F
  slash_action_eq' := fun γ hγ => SlashInvariantFormClass.slash_action_eq F γ hγ
  holo' := ModularFormClass.holo F
  bdd_at_cusps' := fun hc => ModularFormClass.bdd_at_cusps F hc

@[scoped simp] private theorem coe_ofCuspSL {k : ℤ} (F : CuspForm 𝒮ℒ k) : (⇑(ofCuspSL F) : ℍ → ℂ) = ⇑F := rfl

theorem intSeriesC_delta_ne_zero (K : Type*) [Field K] :
    intSeriesC K (PowerSeries.X * dedekindEtaUnit) ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : LaurentSeries K => z.coeff 1) h
  simp only [intSeriesC, HahnSeries.coeff_zero] at h1
  have h2 : (HahnSeries.ofPowerSeries ℤ K
      ((PowerSeries.X * dedekindEtaUnit).map (Int.castRingHom K))).coeff ((1 : ℕ) : ℤ) = 1 := by
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_dedekindEtaUnit, map_one]
  rw [show ((1 : ℕ) : ℤ) = 1 from rfl] at h2
  rw [h2] at h1
  exact one_ne_zero h1

theorem intSeriesC_ne_zero_of_constantCoeff_eq_one (K : Type*) [Field K] (p : PowerSeries ℤ)
    (hp : PowerSeries.constantCoeff p = 1) : intSeriesC K p ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : LaurentSeries K => z.coeff 0) h
  simp only [intSeriesC, HahnSeries.coeff_zero] at h1
  have h2 : (HahnSeries.ofPowerSeries ℤ K (p.map (Int.castRingHom K))).coeff ((0 : ℕ) : ℤ) = 1 := by
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      hp, map_one]
  rw [show ((0 : ℕ) : ℤ) = 0 from rfl] at h2
  rw [h2] at h1
  exact one_ne_zero h1

theorem constantCoeff_P4 : PowerSeries.constantCoeff P4 = 1 := by
  rw [P4, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, if_pos rfl]

theorem constantCoeff_P6 : PowerSeries.constantCoeff P6 = 1 := by
  rw [P6, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, if_pos rfl]

theorem gbar_ne_zero (κ : Type) [Field κ] : gbar κ ≠ 0 :=
  div_ne_zero (mul_ne_zero (intSeriesC_ne_zero_of_constantCoeff_eq_one κ P4 constantCoeff_P4)
    (intSeriesC_ne_zero_of_constantCoeff_eq_one κ P6 constantCoeff_P6)) (intSeriesC_delta_ne_zero κ)

theorem sq_mul_gbar_mem (κ : Type) [Field κ] (M : ℕ) [NeZero M] (w : ModularCurve.IntegralWeightOneForm κ M) :
    ModularCurve.intSeriesC κ w.series ^ 2 * gbar κ ∈ ModularCurve.x1FunctionFieldC κ M := by
  obtain ⟨E4, E6, hE4, hE6⟩ := ModularForm.exists_gamma1_isIntegralQExp_eisenstein_four_six M

  let Dl : ModularForm 𝒮ℒ 12 := ofCuspSL CuspForm.discriminant
  let G : ModularForm (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 12 := restrictSL Dl (Gamma1 M)
  have hG : IsIntegralQExp G (PowerSeries.X * dedekindEtaUnit) := by
    rw [IsIntegralQExp]
    show _ = qExpansion 1 (⇑Dl : ℍ → ℂ)
    rw [show (⇑Dl : ℍ → ℂ) = ModularForm.discriminant from CuspForm.coe_discriminant]
    exact ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm

  let F : ModularForm (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 12 := ((w.form.mul w.form).mul (E4.mul E6)).mcast (by norm_num)
  have h1 : (1 : ℝ) ∈ ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma1]
    exact AddSubgroup.mem_zmultiples _
  have hF : IsIntegralQExp F (w.series ^ 2 * (P4 * P6)) := by
    rw [IsIntegralQExp]
    show _ = qExpansion 1 (⇑((w.form.mul w.form).mul (E4.mul E6)) : ℍ → ℂ)
    rw [ModularForm.qExpansion_mul one_pos h1, ModularForm.qExpansion_mul one_pos h1, ModularForm.qExpansion_mul one_pos h1,
      map_mul, map_mul, map_pow, w.isIntegralQExp, sq]
    have e4 : (P4).map (Int.castRingHom ℂ) = qExpansion 1 (⇑E4 : ℍ → ℂ) := hE4
    have e6 : (P6).map (Int.castRingHom ℂ) = qExpansion 1 (⇑E6 : ℍ → ℂ) := hE6
    rw [e4, e6]
  have hg0 : intSeriesC κ (PowerSeries.X * dedekindEtaUnit) ≠ 0 := intSeriesC_delta_ne_zero κ
  have hmem := div_mem_qExpFunctionFieldC F G hF hG hg0
  have e : ModularCurve.intSeriesC κ w.series ^ 2 * gbar κ =
      intSeriesC κ (w.series ^ 2 * (P4 * P6)) / intSeriesC κ (PowerSeries.X * dedekindEtaUnit) := by
    simp only [gbar, sq, intSeriesC_mul]
    ring
  rw [e]
  exact hmem

theorem hasseRootFn_sq_mul {κ : Type} [Field κ] {M : ℕ} (w : ModularCurve.IntegralWeightOneForm κ M) :
    w.hasseRootFn ^ 2 * (ModularCurve.intSeriesC κ w.series ^ 2 * gbar κ) = gbar κ := by
  rw [ModularCurve.IntegralWeightOneForm.hasseRootFn, inv_pow, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero 2 w.intSeriesC_ne_zero), one_mul]

open IntermediateField Polynomial in

theorem eq_zero_of_sum_mul_pow_eq_zero_of_isKummerGenerator
    {κ Ω : Type*} [Field κ] [Field Ω] [Algebra κ Ω]
    (K₀ : IntermediateField κ Ω) (a : Ω) (n : ℕ) (hK : IgusaCover.IsKummerGenerator n K₀ a)
    (hdeg : K₀.relfinrank (IgusaCover.igusaFunctionField K₀ a) = n)
    (c : Fin n → Ω) (hc : ∀ m, c m ∈ K₀) (h : ∑ m, c m * a ^ (m : ℕ) = 0) : ∀ m, c m = 0 := by
  classical

  have hint : IsIntegral K₀ a := by
    refine ⟨X ^ n - C ⟨a ^ n, hK.pow_mem⟩, monic_X_pow_sub_C _ (Nat.pos_iff_ne_zero.mp hK.pos), ?_⟩
    simp [eval₂_sub, eval₂_X_pow, eval₂_C]

  have hle : K₀ ≤ IgusaCover.igusaFunctionField K₀ a := IgusaCover.le_igusaFunctionField K₀ a
  have hext : extendScalars hle = K₀⟮a⟯ := by
    apply IntermediateField.restrictScalars_injective κ
    rw [IntermediateField.extendScalars_restrictScalars, IntermediateField.restrictScalars_adjoin]
    rfl
  have hnat : (minpoly K₀ a).natDegree = n := by
    rw [← IntermediateField.adjoin.finrank hint, ← hext, ← IntermediateField.relfinrank_eq_finrank_of_le hle, hdeg]

  set P : K₀[X] := ∑ m : Fin n, C (⟨c m, hc m⟩ : K₀) * X ^ (m : ℕ) with hP
  have hPa : aeval a P = 0 := by
    rw [hP, map_sum]
    simp only [map_mul, aeval_C, map_pow, aeval_X, IntermediateField.algebraMap_apply]
    exact h
  have hPdeg : P.degree < n := by
    rw [hP]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr fun m _ => ?_
    refine lt_of_le_of_lt (degree_C_mul_X_pow_le (m : ℕ) _) ?_
    exact WithBot.coe_lt_coe.mpr m.isLt
  have hP0 : P = 0 := by
    by_contra hne
    have h1 := minpoly.degree_le_of_ne_zero K₀ a hne hPa
    have h2 : (minpoly K₀ a).degree = n := by
      rw [degree_eq_natDegree (minpoly.ne_zero hint), hnat]
    rw [h2] at h1
    exact absurd (lt_of_le_of_lt h1 hPdeg) (lt_irrefl _)
  intro m
  have hcoeff : P.coeff m = (⟨c m, hc m⟩ : K₀) := by
    rw [hP, finsetSum_coeff]
    rw [Finset.sum_eq_single m]
    · rw [coeff_C_mul_X_pow, if_pos rfl]
    · intro m' _ hm'
      rw [coeff_C_mul_X_pow, if_neg]
      exact fun heq => hm' (Fin.ext heq).symm
    · intro hm; exact absurd (Finset.mem_univ m) hm
  rw [hP0, coeff_zero] at hcoeff
  have := congrArg Subtype.val hcoeff
  simpa using this.symm

theorem eq_zero_of_sum_mul_gbar_pow_eq_zero
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (κ : Type) [Field κ] [CharP κ q]
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hqM : ¬ q ∣ M)
    (e : Fin ((q - 1) / 2) → LaurentSeries κ) (he : ∀ i, e i ∈ ModularCurve.x1FunctionFieldC κ M)
    (h : ∑ i, e i * gbar κ ^ (i : ℕ) = 0) : ∀ i, e i = 0 := by
  classical
  obtain ⟨w⟩ := ModularCurve.nonempty_integralWeightOneForm κ M (by omega)
  obtain ⟨hK, hdeg⟩ :=
    ModularCurve.isKummerGenerator_hasseRootFn_and_relfinrank_igusaFunctionFieldX1C q hq κ M hM hqM w
  set K₀ := ModularCurve.x1FunctionFieldC κ M with hK₀
  obtain ⟨a, ha⟩ : ∃ a, a = w.hasseRootFn := ⟨_, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k, k = ModularCurve.intSeriesC κ w.series ^ 2 * gbar κ := ⟨_, rfl⟩
  rw [← ha] at hK
  have hk : k ∈ K₀ := by rw [hkdef]; exact sq_mul_gbar_mem κ M w
  have hga : gbar κ = a ^ 2 * k := by rw [hkdef, ha]; exact (hasseRootFn_sq_mul w).symm
  have hk0 : k ≠ 0 := by
    intro h0
    apply gbar_ne_zero κ
    rw [hga, h0, mul_zero]

  have hlt : ∀ i : Fin ((q - 1) / 2), 2 * (i : ℕ) < q - 1 := fun i =>
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left i.isLt two_pos) (Nat.mul_div_le (q - 1) 2)
  let g : Fin ((q - 1) / 2) → Fin (q - 1) := fun i => ⟨2 * (i : ℕ), hlt i⟩
  have hginj : Function.Injective g := by
    intro i j hij
    apply Fin.ext
    have := congrArg Fin.val hij
    simpa [g] using this

  let c : Fin (q - 1) → LaurentSeries κ := fun m => ∑ i ∈ Finset.univ.filter (fun i => g i = m), e i * k ^ (i : ℕ)
  have hc : ∀ m, c m ∈ K₀ := fun m =>
    sum_mem fun i _ => mul_mem (he i) (pow_mem hk _)
  have hsum : ∑ m, c m * a ^ (m : ℕ) = 0 := by
    have step1 : ∀ m, c m * a ^ (m : ℕ) =
        ∑ i ∈ Finset.univ.filter (fun i => g i = m), e i * k ^ (i : ℕ) * a ^ ((g i : Fin (q - 1)) : ℕ) := by
      intro m
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(Finset.mem_filter.mp hi).2]
    simp_rw [step1]
    rw [Finset.sum_fiberwise Finset.univ g (fun i => e i * k ^ (i : ℕ) * a ^ ((g i : Fin (q - 1)) : ℕ))]
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    show e i * k ^ (i : ℕ) * a ^ (2 * (i : ℕ)) = e i * gbar κ ^ (i : ℕ)
    rw [hga, mul_pow, pow_mul, mul_assoc, mul_comm (k ^ (i : ℕ))]
  have hdeg' : K₀.relfinrank (IgusaCover.igusaFunctionField K₀ a) = q - 1 := by
    rw [ha]; exact hdeg
  have hc0 := eq_zero_of_sum_mul_pow_eq_zero_of_isKummerGenerator K₀ a (q - 1) hK hdeg' c hc hsum
  intro i
  have hci : c (g i) = e i * k ^ (i : ℕ) := by
    show ∑ i' ∈ Finset.univ.filter (fun i' => g i' = g i), e i' * k ^ (i' : ℕ) = _
    rw [Finset.sum_eq_single i]
    · intro j hj hji
      exact absurd (hginj (Finset.mem_filter.mp hj).2) hji
    · intro hi
      exact (hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩)).elim
  have := hc0 (g i)
  rw [hci] at this
  exact (mul_eq_zero.mp this).resolve_right (pow_ne_zero _ hk0)

end ModularCurve.EisRatio
p2m_reactivate "P2MW.S_ModularCurve_eq_zero_of_sum_mul_eisensteinRatio_pow_eq_zero_of_mem_x1FunctionFieldC.ModularCurve P2MW.S_ModularCurve_eq_zero_of_sum_mul_eisensteinRatio_pow_eq_zero_of_mem_x1FunctionFieldC.ModularCurve.EisRatio"
p2m_reactivate "P2MW.S_ModularCurve_eq_zero_of_sum_mul_eisensteinRatio_pow_eq_zero_of_mem_x1FunctionFieldC.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_eq_zero_of_sum_mul_eisensteinRatio_pow_eq_zero_of_mem_x1FunctionFieldC.ModularCurve P2MW.S_ModularCurve_eq_zero_of_sum_mul_eisensteinRatio_pow_eq_zero_of_mem_x1FunctionFieldC.ModularCurve.EisRatio"

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (κ : Type) [Field κ] [CharP κ q]
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hqM : ¬ q ∣ M)
    (e : Fin ((q - 1) / 2) → LaurentSeries κ) (he : ∀ i, e i ∈ ModularCurve.x1FunctionFieldC κ M)
    (h : ∑ i, e i *
      (ModularCurve.intSeriesC κ (PowerSeries.mk fun n => if n = 0 then 1 else 240 * (σ 3 n : ℤ)) *
          ModularCurve.intSeriesC κ (PowerSeries.mk fun n => if n = 0 then 1 else -504 * (σ 5 n : ℤ)) /
        ModularCurve.intSeriesC κ (PowerSeries.X * ModularCurve.dedekindEtaUnit)) ^ (i : ℕ) = 0) :
    ∀ i, e i = 0 :=
  ModularCurve.EisRatio.eq_zero_of_sum_mul_gbar_pow_eq_zero q hq κ M hM hqM e he h

end S_ModularCurve_eq_zero_of_sum_mul_eisensteinRatio_pow_eq_zero_of_mem_x1FunctionFieldC
end P2MW
export P2MW.S_ModularCurve_eq_zero_of_sum_mul_eisensteinRatio_pow_eq_zero_of_mem_x1FunctionFieldC (solution)
