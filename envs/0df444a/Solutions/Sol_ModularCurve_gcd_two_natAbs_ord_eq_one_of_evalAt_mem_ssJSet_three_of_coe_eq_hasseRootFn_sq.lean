-- Prove2me | solution 1 for ModularCurve.gcd_two_natAbs_ord_eq_one_of_evalAt_mem_ssJSet_three_of_coe_eq_hasseRootFn_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/a8bfc505-78cd-50b8-a46b-c1199df0fc7c

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Theorems.Thm_ModularCurve_twelve_dvd_ord_of_coe_eq_div_of_ord_nonneg_x1FunctionFieldC
import Theorems.Thm_AlgebraicCurve_Place_mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos
import Theorems.Thm_ModularCurve_isRational_place_x1FunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_ord_dvd_twelve_div_sub_one_of_ord_pos_x1FunctionFieldC_of_lt_five
import Theorems.Thm_WeierstrassCurve_forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_gcd_two_natAbs_ord_eq_one_of_evalAt_mem_ssJSet_three_of_coe_eq_hasseRootFn_sq
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion"
p2m_attr_erase "instance" "instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub"
p2m_attr_erase "instance" "KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero"
p2m_attr_erase "simp" "ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul"
p2m_attr_erase "simp" "KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar"
p2m_attr_erase "simp" "ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open ModularCurve CongruenceSubgroup AlgebraicCurve
open scoped MatrixGroups ModularForm

namespace SsGcd3Aux

theorem intSeriesC_pow (K : Type) [Field K] (q : PowerSeries ℤ) (n : ℕ) :
    intSeriesC K (q ^ n) = intSeriesC K q ^ n := by
  induction n with
  | zero => simp [intSeriesC]
  | succ n ih => rw [pow_succ, intSeriesC_mul, ih, pow_succ]

theorem intSeriesC_X (K : Type) [Field K] : intSeriesC K PowerSeries.X = HahnSeries.single 1 1 := by
  rw [intSeriesC, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]

theorem jqModC_mul_delta (K : Type) [Field K] :
    jqModC K * intSeriesC K (PowerSeries.X * dedekindEtaUnit) = intSeriesC K (eisenstein4 ^ 3) := by
  have hj : jqModC K = HahnSeries.single (-1 : ℤ) (1 : K) * intSeriesC K jNum := rfl
  calc jqModC K * intSeriesC K (PowerSeries.X * dedekindEtaUnit)
      = (HahnSeries.single (-1 : ℤ) (1 : K) * HahnSeries.single (1 : ℤ) (1 : K)) *
          (intSeriesC K jNum * intSeriesC K dedekindEtaUnit) := by
        rw [hj, intSeriesC_mul, intSeriesC_X]; ring
    _ = intSeriesC K (jNum * dedekindEtaUnit) := by
        rw [HahnSeries.single_mul_single, neg_add_cancel, mul_one, ← intSeriesC_mul]
        rw [show (HahnSeries.single (0 : ℤ) (1 : K)) = 1 from rfl, one_mul]
    _ = intSeriesC K (eisenstein4 ^ 3) := by
        rw [jNum, mul_assoc, mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, mul_one]

theorem intSeriesC_eisenstein4_eq_one (κ : Type) [Field κ] [CharP κ 3] : intSeriesC κ eisenstein4 = 1 := by
  have h : eisenstein4.map (Int.castRingHom κ) = 1 := by
    ext n
    rw [PowerSeries.coeff_map, eisenstein4, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    split_ifs with hn
    · simp
    · have h240 : ((240 : ℤ) : κ) = 0 := by
        have : ((240 : ℕ) : κ) = 0 := by
          rw [show (240 : ℕ) = 3 * 80 by norm_num, Nat.cast_mul, CharP.cast_eq_zero κ 3, zero_mul]
        exact_mod_cast this
      have h240' : (Int.castRingHom κ) 240 = 0 := by rw [eq_intCast]; exact h240
      rw [map_mul, h240', zero_mul]
  rw [intSeriesC, h, map_one]

noncomputable def D12 (M : ℕ) : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrictForm (Subgroup.map_le_range _ _) (CuspForm.discriminant : ModularForm 𝒮ℒ 12)

theorem isIntegralQExp_D12 (M : ℕ) : IsIntegralQExp (D12 M : UpperHalfPlane → ℂ) (PowerSeries.X * dedekindEtaUnit) :=
  ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm

theorem intSeriesC_delta_ne_zero (κ : Type) [Field κ] : intSeriesC κ (PowerSeries.X * dedekindEtaUnit) ≠ 0 := by
  rw [intSeriesC_mul, intSeriesC_X]
  refine mul_ne_zero ?_ ?_
  · intro h; exact one_ne_zero ((HahnSeries.single_eq_zero_iff).mp h)
  · intro h0
    have h1 := HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm)
    have h2 := congrArg PowerSeries.constantCoeff h1
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_dedekindEtaUnit, map_one, map_zero] at h2
    exact one_ne_zero h2

theorem one_mem_strictPeriods_Gamma1 (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, ?_, ?_⟩
  · exact (by rw [Gamma1_mem]; simp [ModularGroup.coe_T] : ModularGroup.T ∈ Gamma1 N)
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom]

end SsGcd3Aux

namespace SsGcd3Aux

theorem eq_zero_of_mem_ssJSet_three {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [CharP Ω 3]
    {a : Ω} (ha : a ∈ ssJSet 3 Ω) : a = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hj : (WeierstrassCurve.ofJ a).j = a := WeierstrassCurve.ofJ_j a
  have hP : ∀ P : (WeierstrassCurve.ofJ a).toAffine.Point, 3 • P = 0 → P = 0 := by
    rw [mem_ssJSet_iff] at ha
    exact ha (WeierstrassCurve.ofJ a) hj
  have hH : (WeierstrassCurve.ofJ a).hasseInvariant 3 = 0 :=
    (WeierstrassCurve.forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero 3 (by norm_num) (WeierstrassCurve.ofJ a)).mp hP
  have hb₂ : (WeierstrassCurve.ofJ a).b₂ = 0 := by
    have : (WeierstrassCurve.ofJ a).hasseInvariant 3 = (WeierstrassCurve.ofJ a).b₂ := by
      rw [WeierstrassCurve.hasseInvariant, show (3 - 1) / 2 = 1 from rfl, pow_one, show 3 - 1 = 2 from rfl, Cubic.coeff_eq_b]
      rfl
    rw [← this]; exact hH
  have hc₄ : (WeierstrassCurve.ofJ a).c₄ = 0 := by rw [WeierstrassCurve.c₄_of_char_three, hb₂]; ring
  rw [← hj]
  exact (WeierstrassCurve.ofJ a).j_eq_zero hc₄

end SsGcd3Aux

open SsGcd3Aux

theorem solution
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) (h3M : ¬ 3 ∣ M)
    (Ω : Type) [Field Ω] [CharP Ω 3] [IsAlgClosed Ω] [DecidableEq Ω]
    (w : ModularCurve.IntegralWeightOneForm Ω M)
    (jbar : ↥(ModularCurve.x1FunctionFieldC Ω M)) (hjbar : (jbar : LaurentSeries Ω) = ModularCurve.jqModC Ω)
    (b : ↥(ModularCurve.x1FunctionFieldC Ω M)) (hb : (b : LaurentSeries Ω) = w.hasseRootFn ^ 2)
    (v : AlgebraicCurve.Place Ω ↥(ModularCurve.x1FunctionFieldC Ω M))
    (hv : (jbar : ↥(ModularCurve.x1FunctionFieldC Ω M)) ∈ v.toValuationSubring ∧ v.evalAt jbar ∈ ModularCurve.ssJSet 3 Ω) :
    Nat.gcd 2 (v.ord b).natAbs = 1 := by
  classical
  haveI h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJmem, hss⟩ := hv
  set J := jbar with hJdef

  have ha0 : v.evalAt J = 0 := eq_zero_of_mem_ssJSet_three hss
  have hrat : v.IsRational := ModularCurve.isRational_place_x1FunctionFieldC_of_isAlgClosed 3 M hM h3M Ω v
  have hj0 : jqModC Ω ≠ 0 := fun h0 =>
    Polynomial.X_ne_zero (transcendental_iff.mp (transcendental_jqModC Ω) Polynomial.X (by rw [Polynomial.aeval_X]; exact h0))
  have hJ0 : J ≠ 0 := by
    intro h0
    have := congrArg (fun z : ↥(ModularCurve.x1FunctionFieldC Ω M) => (z : LaurentSeries Ω)) h0
    simp only [ZeroMemClass.coe_zero] at this
    exact hj0 (hjbar ▸ this)
  have hJne : J ≠ algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) 0 := by rw [map_zero]; exact hJ0
  have hordJ : 0 < v.ord J := by
    have h := (AlgebraicCurve.Place.mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos v hrat J 0 hJne).mp ⟨hJmem, ha0⟩
    rwa [map_zero, sub_zero] at h

  have hJ6 : v.ord J ∣ 6 := by
    have h := ModularCurve.ord_dvd_twelve_div_sub_one_of_ord_pos_x1FunctionFieldC_of_lt_five 3 (by norm_num) M h3M Ω J hjbar v hordJ
    norm_num at h
    exact h

  have hw0 : intSeriesC Ω w.series ≠ 0 := w.intSeriesC_ne_zero
  have hΔ : intSeriesC Ω (PowerSeries.X * dedekindEtaUnit) ≠ 0 := intSeriesC_delta_ne_zero Ω
  let W12 : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 12 :=
    (w.form.pow 12).mcast (by norm_num)
  have hW12 : IsIntegralQExp (⇑W12) (w.series ^ 12) := by
    rw [IsIntegralQExp, map_pow]
    show _ = UpperHalfPlane.qExpansion 1 (⇑((w.form.pow 12).mcast _))
    rw [ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos (one_mem_strictPeriods_Gamma1 M),
      ← w.isIntegralQExp]
  have hTmem : intSeriesC Ω (w.series ^ 12) / intSeriesC Ω (PowerSeries.X * dedekindEtaUnit) ∈ ModularCurve.x1FunctionFieldC Ω M :=
    div_mem_qExpFunctionFieldC W12 (D12 M) hW12 (isIntegralQExp_D12 M) hΔ
  set T : ↥(ModularCurve.x1FunctionFieldC Ω M) := ⟨_, hTmem⟩ with hTdef
  have hT : (T : LaurentSeries Ω) = intSeriesC Ω (w.series ^ 12) / intSeriesC Ω (PowerSeries.X * dedekindEtaUnit) := rfl
  obtain ⟨t, ht⟩ := ModularCurve.twelve_dvd_ord_of_coe_eq_div_of_ord_nonneg_x1FunctionFieldC 3 Ω M hM h3M w J hjbar T hT v hordJ.le

  have hjΔ : jqModC Ω * intSeriesC Ω (PowerSeries.X * dedekindEtaUnit) = 1 := by
    rw [jqModC_mul_delta Ω, intSeriesC_pow, intSeriesC_eisenstein4_eq_one Ω, one_pow]
  have hbTJ : b ^ 6 * T = J := by
    apply Subtype.ext
    show (b : LaurentSeries Ω) ^ 6 * (intSeriesC Ω (w.series ^ 12) / intSeriesC Ω (PowerSeries.X * dedekindEtaUnit)) = (J : LaurentSeries Ω)
    rw [hb, hjbar, IntegralWeightOneForm.hasseRootFn, ← pow_mul, show 2 * 6 = 12 from rfl, intSeriesC_pow, inv_pow,
      div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hw0), one_mul, eq_inv_of_mul_eq_one_left hjΔ]
  have hb0 : b ≠ 0 := by
    intro h0
    have := congrArg (fun z : ↥(ModularCurve.x1FunctionFieldC Ω M) => (z : LaurentSeries Ω)) h0
    simp only [ZeroMemClass.coe_zero] at this
    rw [hb] at this
    exact pow_ne_zero _ w.hasseRootFn_ne_zero this
  have hT0 : T ≠ 0 := by
    intro h0
    have := congrArg (fun z : ↥(ModularCurve.x1FunctionFieldC Ω M) => (z : LaurentSeries Ω)) h0
    simp only [ZeroMemClass.coe_zero] at this
    rw [hT] at this
    exact div_ne_zero (by rw [intSeriesC_pow]; exact pow_ne_zero _ hw0) hΔ this
  have hord : 6 * v.ord b + v.ord T = v.ord J := by
    rw [← hbTJ, Place.ord_mul _ (pow_ne_zero _ hb0) hT0, ← zpow_natCast, Place.ord_zpow]
    push_cast; ring

  have h6pos : (0 : ℤ) < 6 := by norm_num
  have hJle : v.ord J ≤ 6 := Int.le_of_dvd h6pos hJ6
  have hodd : Odd (v.ord b) := by
    rw [Int.odd_iff]
    rcases Int.emod_two_eq_zero_or_one (v.ord b) with h | h
    · exfalso
      obtain ⟨s, hs⟩ : (2 : ℤ) ∣ v.ord b := Int.dvd_of_emod_eq_zero h
      rw [hs, ht] at hord

      omega
    · exact h
  rw [Nat.coprime_two_left.mpr (Int.natAbs_odd.mpr hodd)]

end S_ModularCurve_gcd_two_natAbs_ord_eq_one_of_evalAt_mem_ssJSet_three_of_coe_eq_hasseRootFn_sq
end P2MW
export P2MW.S_ModularCurve_gcd_two_natAbs_ord_eq_one_of_evalAt_mem_ssJSet_three_of_coe_eq_hasseRootFn_sq (solution)
