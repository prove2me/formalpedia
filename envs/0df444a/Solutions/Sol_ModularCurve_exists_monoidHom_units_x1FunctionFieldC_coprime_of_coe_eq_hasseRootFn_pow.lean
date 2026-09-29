-- Prove2me | solution 1 for ModularCurve.exists_monoidHom_units_x1FunctionFieldC_coprime_of_coe_eq_hasseRootFn_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/f47788eb-1c8c-5cfe-9426-f17b11dfdb8b

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_ModularCurve_ord_sub_algebraMap_eq_jWidth_of_place_x1FunctionFieldC
import Theorems.Thm_ModularCurve_exists_place_x1FunctionFieldC_ord_aeval_pos_of_integralWeightOneForm
import Theorems.Thm_ModularCurve_jWidth_mul_ord_eq_ord_aeval_of_coe_eq_hasseRootFn_pow
import Theorems.Thm_ModularCurve_exists_separable_thetaL_jqModC_pow_mul_aeval_eq
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_isKummerGenerator_hasseRootFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_monoidHom_units_x1FunctionFieldC_coprime_of_coe_eq_hasseRootFn_pow
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub"
p2m_attr_erase "instance" "KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq"
p2m_attr_erase "simp" "CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP"
p2m_attr_erase "simp" "ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve~coeffMap_ofPowerSeries Polynomial"
open scoped MatrixGroups

namespace ISZAsmE95

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

section BaseChange

variable {κ L : Type*} [Field κ] [Field L] (f : κ →+* L)

theorem coeffMap_ofPowerSeries (q : PowerSeries κ) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ κ q) = HahnSeries.ofPowerSeries ℤ L (q.map f) := by
  ext k
  rw [coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

theorem coeffMap_intSeriesC (q : PowerSeries ℤ) : coeffMap f (intSeriesC κ q) = intSeriesC L q := by
  rw [intSeriesC, intSeriesC, coeffMap_ofPowerSeries, ← RingHom.comp_apply (PowerSeries.map f),
    ← PowerSeries.map_comp, RingHom.ext_int (f.comp (Int.castRingHom κ)) (Int.castRingHom L)]

theorem coeffMap_algebraMap' (c : κ) :
    coeffMap f (algebraMap κ (LaurentSeries κ) c) = algebraMap L (LaurentSeries L) (f c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem coeffMap_mem_qExpFunctionFieldC (Γ : Subgroup SL(2, ℤ)) {g : LaurentSeries κ}
    (hg : g ∈ qExpFunctionFieldC κ Γ) : coeffMap f g ∈ qExpFunctionFieldC L Γ := by

  let T : Subfield (LaurentSeries κ) := (qExpFunctionFieldC L Γ).toSubfield.comap (coeffMap f)
  have hgen : Set.range (algebraMap κ (LaurentSeries κ)) ∪ intFormRatiosC κ Γ ⊆ (T : Set (LaurentSeries κ)) := by
    rintro y (⟨c, rfl⟩ | hy)
    · change coeffMap f (algebraMap κ (LaurentSeries κ) c) ∈ qExpFunctionFieldC L Γ
      rw [coeffMap_algebraMap']
      exact (qExpFunctionFieldC L Γ).algebraMap_mem _
    · obtain ⟨k, F₁, G₁, pf, pg, hF, hG, hne, rfl⟩ := hy
      change coeffMap f (intSeriesC κ pf / intSeriesC κ pg) ∈ qExpFunctionFieldC L Γ
      rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]
      refine div_mem_qExpFunctionFieldC F₁ G₁ hF hG ?_
      intro h0
      apply hne
      apply (coeffMap f).injective
      rw [coeffMap_intSeriesC, h0, map_zero]
  have hle : (qExpFunctionFieldC κ Γ).toSubfield ≤ T := by
    rw [qExpFunctionFieldC, IntermediateField.adjoin_toSubfield]
    exact Subfield.closure_le.mpr hgen
  exact hle hg

end BaseChange

section Weight4

open ModularForm EisensteinSeries UpperHalfPlane CongruenceSubgroup

theorem isIntegralQExp_E4 : IsIntegralQExp (E₄ : ℍ → ℂ) eisenstein4 := by
  rw [isIntegralQExp_iff]
  intro n
  rw [E_qExpansion_coeff (by norm_num) (by decide) n, eisenstein4, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 4 = -1 / 30 by decide +kernel, ArithmeticFunction.sigma_apply]
    push_cast
    ring

theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ Gamma1 N := by
  rw [Gamma1_mem]
  simp [ModularGroup.T]

theorem one_mem_strictPeriods {Δ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Δ) :
    (1 : ℝ) ∈ (Δ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, hT, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom]

theorem eisenstein4_eq_mk_sigma :
    eisenstein4 = PowerSeries.mk fun n => if n = 0 then (1 : ℤ) else 240 * (ArithmeticFunction.sigma 3 n : ℤ) := by
  ext n
  simp only [eisenstein4, PowerSeries.coeff_mk, ArithmeticFunction.sigma_apply, Nat.cast_sum, Nat.cast_pow]

end Weight4

end ISZAsmE95

namespace ISZAsmE95

section SSPoly

variable {L : Type*} [Field L]

theorem monic_separable_ssPoly {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) [CharP L p]
    {e₄ e₆ : ℕ} (he₄ : e₄ ≤ 1) (he₆ : e₆ ≤ 1) {S : Polynomial L}
    (hSmonic : S.Monic) (hSsep : S.Separable) (hS0 : S.eval 0 ≠ 0) (hS1728 : S.eval 1728 ≠ 0) :
    (X ^ e₄ * (X - C (1728 : L)) ^ e₆ * S).Monic ∧ (X ^ e₄ * (X - C (1728 : L)) ^ e₆ * S).Separable := by
  have h1728 : (1728 : L) ≠ 0 := by
    intro h
    have h' : ((1728 : ℕ) : L) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff L p] at h'
    have h2 : p ∣ 2 ∨ p ∣ 3 := by
      have : (1728 : ℕ) = 2 ^ 6 * 3 ^ 3 := by norm_num
      rw [this] at h'
      rcases hp.dvd_mul.mp h' with h2 | h3
      · exact Or.inl (hp.dvd_of_dvd_pow h2)
      · exact Or.inr (hp.dvd_of_dvd_pow h3)
    rcases h2 with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) h2; omega
    · have := Nat.le_of_dvd (by norm_num) h3; omega
  refine ⟨((monic_X_pow e₄).mul ((monic_X_sub_C _).pow e₆)).mul hSmonic, ?_⟩
  have hsepA : (X ^ e₄ : Polynomial L).Separable := by
    interval_cases e₄
    · simpa using separable_one
    · simpa using separable_X
  have hsepB : ((X - C (1728 : L)) ^ e₆).Separable := by
    interval_cases e₆
    · simpa using separable_one
    · simpa using separable_X_sub_C
  have hcop_lin : ∀ {a : L} {Q : Polynomial L}, Q.eval a ≠ 0 → IsCoprime (X - C a) Q := by
    intro a Q hQ
    rw [(irreducible_X_sub_C a).coprime_iff_not_dvd, dvd_iff_isRoot]
    exact hQ
  have hcopX : ∀ {Q : Polynomial L}, Q.eval 0 ≠ 0 → IsCoprime (X : Polynomial L) Q := by
    intro Q hQ
    have := hcop_lin hQ
    rwa [map_zero, sub_zero] at this
  have hcopAB : IsCoprime (X ^ e₄ : Polynomial L) ((X - C (1728 : L)) ^ e₆) := by
    refine IsCoprime.pow (hcopX ?_)
    rw [eval_sub, eval_X, eval_C, zero_sub, neg_ne_zero]
    exact h1728
  have hcopS : IsCoprime (X ^ e₄ * (X - C (1728 : L)) ^ e₆) S :=
    IsCoprime.mul_left (IsCoprime.pow_left (hcopX hS0)) (IsCoprime.pow_left (hcop_lin hS1728))
  exact (hsepA.mul hsepB hcopAB).mul hSsep hcopS

end SSPoly

section OrdPoly

variable {L F : Type*} [Field L] [Field F] [Algebra L F] [IsAlgClosed L]

theorem exists_root_ord_aeval_eq (x : Place L F) (J : F) (hJc : ∀ r : L, J - algebraMap L F r ≠ 0)
    (hx : 0 ≤ x.ord J) {P : Polynomial L} (hPmonic : P.Monic) (hPsep : P.Separable)
    (hP : 1 ≤ x.ord (aeval J P)) (W : L → ℤ) (hW : ∀ j, 0 < W j)
    (hFR : ∀ j₀ : L, 1 ≤ x.ord (J - algebraMap L F j₀) → x.ord (J - algebraMap L F j₀) = W j₀) :
    ∃ j₀ : L, 1 ≤ x.ord (J - algebraMap L F j₀) ∧ x.ord (aeval J P) = W j₀ := by
  classical
  have hJne : J ≠ 0 := by
    have := hJc 0
    rwa [map_zero, sub_zero] at this
  have hProots : P = (P.roots.map fun r => X - C r).prod := by
    conv_lhs => rw [Splits.eq_prod_roots (IsAlgClosed.splits P), hPmonic.leadingCoeff, map_one, one_mul]
  have hnodup : P.roots.Nodup := nodup_roots hPsep
  have haeval : aeval J P = (P.roots.map fun r => J - algebraMap L F r).prod := by
    conv_lhs => rw [hProots]
    rw [map_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro r _
    simp [Function.comp]
  have hfac_ne : ∀ g ∈ (P.roots.map fun r => J - algebraMap L F r), g ≠ 0 := by
    intro g hg
    obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hg
    exact hJc r
  have hord_nonneg : ∀ r : L, 0 ≤ x.ord (J - algebraMap L F r) := by
    intro r
    rcases eq_or_ne r 0 with rfl | hr
    · rw [map_zero, sub_zero]; exact hx
    · have hc : x.ord (-algebraMap L F r) = 0 := by
        rw [ord_neg, ord_algebraMap x hr]
      have hmin := min_ord_le_ord_add x hJne (neg_ne_zero.mpr ((_root_.map_ne_zero _).mpr hr))
        (by rw [← sub_eq_add_neg]; exact hJc r)
      rw [← sub_eq_add_neg, hc] at hmin
      exact le_trans (le_min hx le_rfl) hmin
  have hord_sum : x.ord (aeval J P) = (P.roots.map fun r => x.ord (J - algebraMap L F r)).sum := by
    rw [haeval, ord_multiset_prod x _ hfac_ne, Multiset.map_map]
    rfl

  obtain ⟨j₀, hj₀mem, hj₀⟩ : ∃ j₀ ∈ P.roots, 1 ≤ x.ord (J - algebraMap L F j₀) := by
    by_contra hcon
    push Not at hcon
    have hzero : (P.roots.map fun r => x.ord (J - algebraMap L F r)).sum = 0 := by
      refine Multiset.sum_eq_zero ?_
      intro z hz
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hz
      have h1 := hcon r hr
      have h2 := hord_nonneg r
      omega
    rw [hord_sum, hzero] at hP
    exact absurd hP (by norm_num)
  have hFR₀ := hFR j₀ hj₀

  have hother : ∀ r ∈ P.roots.erase j₀, x.ord (J - algebraMap L F r) = 0 := by
    intro r hr
    have hrj : r ≠ j₀ := ((hnodup.mem_erase_iff).mp hr).1
    have hsplit : J - algebraMap L F r = algebraMap L F (j₀ - r) + (J - algebraMap L F j₀) := by
      rw [map_sub, sub_add_sub_cancel']
    have hne : algebraMap L F (j₀ - r) ≠ 0 := (_root_.map_ne_zero _).mpr (sub_ne_zero.mpr hrj.symm)
    have hc0 : x.ord (algebraMap L F (j₀ - r)) = 0 := ord_algebraMap x (sub_ne_zero.mpr hrj.symm)
    have hlt : x.ord (algebraMap L F (j₀ - r)) < x.ord (J - algebraMap L F j₀) := by
      rw [hc0, hFR₀]; exact hW j₀
    rw [hsplit, ord_add_eq_of_lt x hne (hJc j₀) hlt, hc0]
  refine ⟨j₀, hj₀, ?_⟩
  rw [hord_sum, ← Multiset.cons_erase hj₀mem, Multiset.map_cons, Multiset.sum_cons, hFR₀,
    Multiset.sum_eq_zero (fun z hz => ?_), add_zero]
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hz
  exact hother r hr

end OrdPoly

section Closed

open ModularForm CongruenceSubgroup

theorem exists_place_ord_hasseRootFn_pow_eq_one (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (L : Type) [Field L] [CharP L p] [IsAlgClosed L] [DecidableEq L]
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M) (w' : ModularCurve.IntegralWeightOneForm L M) :
    ∃ x : Place L ↥(x1FunctionFieldC L M),
      x.ord (⟨w'.hasseRootFn ^ (p - 1), (ModularCurve.isKummerGenerator_hasseRootFn p hp5 L M w').pow_mem⟩ :
        ↥(x1FunctionFieldC L M)) = 1 := by
  have hp : p.Prime := Fact.out
  have hM4 : 4 ≤ M := le_trans (by norm_num) hM

  obtain ⟨m, e₄, e₆, S, hS⟩ := ModularCurve.exists_separable_thetaL_jqModC_pow_mul_aeval_eq p hp5 L

  have hJmem : jqModC L ∈ x1FunctionFieldC L M :=
    intFormRatiosC_subset L (Gamma1 M) (ModularCurve.jqModC_mem_intFormRatiosC L (Gamma1 M))
  let J : ↥(x1FunctionFieldC L M) := ⟨jqModC L, hJmem⟩
  have hJ : (J : LaurentSeries L) = jqModC L := rfl

  let E4M : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 4 :=
    restrictForm (Subgroup.map_le_range _ (Gamma1 M)) E₄
  have hE4M : IsIntegralQExp E4M eisenstein4 := by
    rw [IsIntegralQExp, coe_restrictForm]
    exact isIntegralQExp_E4
  let W4 : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 4 :=
    (w'.form.pow 4).mcast (by norm_num)
  have hW4 : IsIntegralQExp W4 (w'.series ^ 4) := by
    rw [IsIntegralQExp, ModularForm.coe_mcast, map_pow, w'.isIntegralQExp]
    exact (ModularForm.qExpansion_pow one_pos (one_mem_strictPeriods (T_mem_Gamma1 M)) w'.form 4).symm
  have hW4L : intSeriesC L (w'.series ^ 4) ≠ 0 := by
    rw [show intSeriesC L (w'.series ^ 4) = intSeriesC L w'.series ^ 4 by simp [intSeriesC]]
    exact pow_ne_zero _ w'.intSeriesC_ne_zero
  have humem : intSeriesC L eisenstein4 / intSeriesC L (w'.series ^ 4) ∈ x1FunctionFieldC L M :=
    div_mem_qExpFunctionFieldC E4M W4 hE4M hW4 hW4L
  let u : ↥(x1FunctionFieldC L M) := ⟨_, humem⟩
  have hu : (u : LaurentSeries L) =
      intSeriesC L (PowerSeries.mk fun n => if n = 0 then (1 : ℤ) else 240 * (ArithmeticFunction.sigma 3 n : ℤ)) /
        intSeriesC L (w'.series ^ 4) := by
    change intSeriesC L eisenstein4 / intSeriesC L (w'.series ^ 4) = _
    rw [eisenstein4_eq_mk_sigma]

  set b' : ↥(x1FunctionFieldC L M) :=
    ⟨w'.hasseRootFn ^ (p - 1), (ModularCurve.isKummerGenerator_hasseRootFn p hp5 L M w').pow_mem⟩ with hb'def
  have hb' : (b' : LaurentSeries L) = w'.hasseRootFn ^ (p - 1) := rfl

  obtain ⟨x, hx, hxu, hP⟩ :=
    ModularCurve.exists_place_x1FunctionFieldC_ord_aeval_pos_of_integralWeightOneForm p hp5 L M hM hpM w'
      m e₄ e₆ S hS J hJ u hu
  obtain ⟨h12, he₄, he₆, hSmonic, hSsep, hSdeg, hS0, hS1728, hSeq⟩ := hS
  obtain ⟨hPmonic, hPsep⟩ := monic_separable_ssPoly (L := L) hp hp5 he₄ he₆ hSmonic hSsep hS0 hS1728

  have hJtr : Transcendental L (jqModC L) := ModularCurve.transcendental_jqModC L
  have hJc : ∀ r : L, (J : ↥(x1FunctionFieldC L M)) - algebraMap L ↥(x1FunctionFieldC L M) r ≠ 0 := by
    intro r h
    apply hJtr
    have h' : ((J : ↥(x1FunctionFieldC L M)) : LaurentSeries L) =
        ((algebraMap L ↥(x1FunctionFieldC L M) r : ↥(x1FunctionFieldC L M)) : LaurentSeries L) :=
      congrArg (fun z : ↥(x1FunctionFieldC L M) => (z : LaurentSeries L)) (sub_eq_zero.mp h)
    change IsAlgebraic L ((J : ↥(x1FunctionFieldC L M)) : LaurentSeries L)
    rw [h']
    exact isAlgebraic_algebraMap r

  obtain ⟨j₀, hj₀, hordP⟩ := exists_root_ord_aeval_eq x J hJc hx hPmonic hPsep hP (fun j => (jWidth j : ℤ))
    (fun j => show (0 : ℤ) < (jWidth j : ℤ) by exact_mod_cast jWidth_pos j)
    (fun j₀ hj₀ => ModularCurve.ord_sub_algebraMap_eq_jWidth_of_place_x1FunctionFieldC p hp5 L M hM hpM J hJ x hx j₀ hj₀)

  have hHO := ModularCurve.jWidth_mul_ord_eq_ord_aeval_of_coe_eq_hasseRootFn_pow p hp5 L M hM4 hpM w'
    m e₄ e₆ S ⟨h12, he₄, he₆, hSmonic, hSsep, hSdeg, hS0, hS1728, hSeq⟩ J hJ u hu b' hb' x hx hxu j₀ hj₀
  have hjW : (jWidth j₀ : ℤ) ≠ 0 := by exact_mod_cast (jWidth_pos j₀).ne'
  refine ⟨x, ?_⟩
  rw [hordP] at hHO
  exact (mul_eq_left₀ hjW).mp hHO

end Closed

end ISZAsmE95

open ISZAsmE95 CongruenceSubgroup in

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (κ : Type) [Field κ] [CharP κ p]
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (w : ModularCurve.IntegralWeightOneForm κ M) :
    ∃ φ : (↥(ModularCurve.x1FunctionFieldC κ M))ˣ →* Multiplicative ℤ,
      ∀ b : (↥(ModularCurve.x1FunctionFieldC κ M))ˣ,
        ((b : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ) = w.hasseRootFn ^ (p - 1) →
        (Multiplicative.toAdd (φ b)).natAbs.Coprime (p - 1) := by
  classical
  have hp : p.Prime := Fact.out

  let L := AlgebraicClosure κ
  let f : κ →+* L := algebraMap κ L
  let ι : LaurentSeries κ →+* LaurentSeries L := coeffMap f
  have hιmem : ∀ g : ↥(x1FunctionFieldC κ M), ι (g : LaurentSeries κ) ∈ x1FunctionFieldC L M := fun g =>
    coeffMap_mem_qExpFunctionFieldC f (Gamma1 M) g.2
  let ι₀ : ↥(x1FunctionFieldC κ M) →+* ↥(x1FunctionFieldC L M) :=
    (ι.comp (algebraMap ↥(x1FunctionFieldC κ M) (LaurentSeries κ))).codRestrict (x1FunctionFieldC L M) hιmem
  have hι₀ : ∀ g : ↥(x1FunctionFieldC κ M), ((ι₀ g : ↥(x1FunctionFieldC L M)) : LaurentSeries L) = ι g :=
    fun _ => rfl
  have hι₀inj : Function.Injective ι₀ := ι₀.injective

  have hserL : intSeriesC L w.series ≠ 0 := by
    intro h0
    apply w.intSeriesC_ne_zero
    apply ι.injective
    rw [coeffMap_intSeriesC, h0, map_zero]
  let w' : IntegralWeightOneForm L M := ⟨w.form, w.series, w.isIntegralQExp, hserL⟩
  have hιa : ι w.hasseRootFn = w'.hasseRootFn := by
    change coeffMap f (intSeriesC κ w.series)⁻¹ = (intSeriesC L w.series)⁻¹
    rw [map_inv₀, coeffMap_intSeriesC]

  obtain ⟨x, hordb⟩ := exists_place_ord_hasseRootFn_pow_eq_one p hp5 L M hM hpM w'

  let φ : (↥(x1FunctionFieldC κ M))ˣ →* Multiplicative ℤ :=
    { toFun := fun c => Multiplicative.ofAdd (x.ord (ι₀ (c : ↥(x1FunctionFieldC κ M))))
      map_one' := by simp
      map_mul' := fun c d => by
        have hc : ι₀ (c : ↥(x1FunctionFieldC κ M)) ≠ 0 := (map_ne_zero_iff ι₀ hι₀inj).mpr (Units.ne_zero c)
        have hd : ι₀ (d : ↥(x1FunctionFieldC κ M)) ≠ 0 := (map_ne_zero_iff ι₀ hι₀inj).mpr (Units.ne_zero d)
        rw [Units.val_mul, map_mul, x.ord_mul hc hd, ofAdd_add] }
  refine ⟨φ, fun c hc => ?_⟩
  have hιc : ι₀ (c : ↥(x1FunctionFieldC κ M)) =
      ⟨w'.hasseRootFn ^ (p - 1), (ModularCurve.isKummerGenerator_hasseRootFn p hp5 L M w').pow_mem⟩ := by
    apply Subtype.ext
    rw [hι₀, hc, map_pow, hιa]
  change (Multiplicative.toAdd (Multiplicative.ofAdd
    (x.ord (ι₀ (c : ↥(x1FunctionFieldC κ M)))))).natAbs.Coprime (p - 1)
  rw [toAdd_ofAdd, hιc, hordb]
  exact Nat.coprime_one_left _

end S_ModularCurve_exists_monoidHom_units_x1FunctionFieldC_coprime_of_coe_eq_hasseRootFn_pow
end P2MW
export P2MW.S_ModularCurve_exists_monoidHom_units_x1FunctionFieldC_coprime_of_coe_eq_hasseRootFn_pow (solution)
