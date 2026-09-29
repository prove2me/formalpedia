-- Prove2me | solution 1 for ModularCurve.exists_place_x1FunctionFieldC_ord_aeval_pos_of_integralWeightOneForm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/89d34f1d-c2a9-5b1e-8594-4c099db4c316

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_ord_sub_algebraMap_eq_jWidth_of_place_x1FunctionFieldC
import Theorems.Thm_ModularCurve_exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC
import Theorems.Thm_ModularCurve_exists_coe_eq_div_pow_and_mul_min_ord_le_ord_x1FunctionFieldC
import Theorems.Thm_AlgebraicCurve_exists_finset_sum_ord_sub_algebraMap_eq_finrank_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_sum_support
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_place_x1FunctionFieldC_ord_aeval_pos_of_integralWeightOneForm
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex"
p2m_attr_erase "instance" "TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg"
p2m_attr_erase "instance" "KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply"
p2m_attr_erase "simp" "TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq"
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar"
p2m_attr_erase "simp" "ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec"

set_option autoImplicit false

p2m_open "CongruenceSubgroup ModularCurve~eisenstein6 AlgebraicCurve ModularForm EisensteinSeries UpperHalfPlane Polynomial"
open scoped MatrixGroups ModularForm

namespace SsnvE96

def eisenstein6 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5

theorem isIntegralQExp_E4 : IsIntegralQExp (E₄ : ℍ → ℂ) eisenstein4 := by
  unfold IsIntegralQExp
  ext n
  rw [PowerSeries.coeff_map, E_qExpansion_coeff (by norm_num) (by decide) n, eisenstein4, PowerSeries.coeff_mk,
    eq_intCast]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 4 = -1 / 30 by decide +kernel, ArithmeticFunction.sigma_apply]
    push_cast
    ring

theorem isIntegralQExp_E6 : IsIntegralQExp (E₆ : ℍ → ℂ) eisenstein6 := by
  unfold IsIntegralQExp
  ext n
  rw [PowerSeries.coeff_map, E_qExpansion_coeff (by norm_num) (by decide) n, eisenstein6, PowerSeries.coeff_mk,
    eq_intCast]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 6 = 1 / 42 by decide +kernel, ArithmeticFunction.sigma_apply]
    push_cast
    ring

theorem eisenstein4_cube_sub_eisenstein6_sq :
    eisenstein4 ^ 3 - eisenstein6 ^ 2 = PowerSeries.C (1728 : ℤ) * (PowerSeries.X * dedekindEtaUnit) := by
  apply PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective
  have h4 : PowerSeries.map (Int.castRingHom ℂ) eisenstein4 = qExpansion 1 (E₄ : ℍ → ℂ) := isIntegralQExp_E4
  have h6 : PowerSeries.map (Int.castRingHom ℂ) eisenstein6 = qExpansion 1 (E₆ : ℍ → ℂ) := isIntegralQExp_E6
  rw [map_sub, map_pow, map_pow, h4, h6, map_mul, PowerSeries.map_C,
    ← ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit, eq_intCast, Int.cast_ofNat]
  let F12 : ModularForm 𝒮ℒ 12 := ModularForm.mcast (by decide) (E₄.pow 3) - ModularForm.mcast (by decide) (E₆.pow 2)
  have hq : qExpansion 1 (F12 : ℍ → ℂ) = qExpansion 1 (E₄ : ℍ → ℂ) ^ 3 - qExpansion 1 (E₆ : ℍ → ℂ) ^ 2 := by
    simp only [F12, ModularForm.coe_sub, coe_mcast, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  have hcoeΔ : ((CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ℍ → ℂ) = ModularForm.discriminant := rfl
  have hfun : (F12 : ℍ → ℂ) = (1728 : ℂ) • ((CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ℍ → ℂ) := by
    rw [hcoeΔ]
    funext z
    simp only [F12, ModularForm.coe_sub, coe_mcast, ModularForm.coe_pow, Pi.sub_apply, Pi.pow_apply, Pi.smul_apply, smul_eq_mul]
    rw [discriminant_eq_E₄_cube_sub_E₆_sq]
    ring
  rw [← hq, hfun, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL (1728 : ℂ)
    (CuspForm.discriminant : CuspForm 𝒮ℒ 12), hcoeΔ, PowerSeries.smul_eq_C_mul]

theorem intSeriesC_pow (K : Type) [Field K] (q : PowerSeries ℤ) (n : ℕ) :
    intSeriesC K (q ^ n) = intSeriesC K q ^ n := by
  induction n with
  | zero => simp [intSeriesC]
  | succ n ih => rw [pow_succ, intSeriesC_mul, ih, pow_succ]

theorem intSeriesC_sub (K : Type) [Field K] (q r : PowerSeries ℤ) :
    intSeriesC K (q - r) = intSeriesC K q - intSeriesC K r := by
  simp [intSeriesC, map_sub]

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

theorem jqModC_sub_mul_delta (K : Type) [Field K] :
    (jqModC K - 1728) * intSeriesC K (PowerSeries.X * dedekindEtaUnit) = intSeriesC K (eisenstein6 ^ 2) := by
  have h := congrArg (intSeriesC K) eisenstein4_cube_sub_eisenstein6_sq
  rw [intSeriesC_sub, intSeriesC_mul] at h
  rw [sub_mul, jqModC_mul_delta]
  have hC : intSeriesC K (PowerSeries.C (1728 : ℤ)) = 1728 := by
    rw [intSeriesC, PowerSeries.map_C, HahnSeries.ofPowerSeries_C, eq_intCast, Int.cast_ofNat, map_ofNat]
  rw [hC] at h
  linear_combination h

theorem eisenstein4_eq_mk_sigma :
    eisenstein4 = PowerSeries.mk fun n => if n = 0 then (1 : ℤ) else 240 * (ArithmeticFunction.sigma 3 n : ℤ) := by
  ext n
  simp only [eisenstein4, PowerSeries.coeff_mk, ArithmeticFunction.sigma_apply]
  push_cast
  rfl

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

theorem ord_pow' (f : F) (n : ℕ) : v.ord (f ^ n) = (n : ℤ) * v.ord f := by
  rw [← zpow_natCast]; exact v.ord_zpow f n

theorem ord_sub_algebraMap_nonneg {J : F} (hJ : J ≠ 0) (hJc : ∀ r : K, J - algebraMap K F r ≠ 0)
    (hx : 0 ≤ v.ord J) (r : K) : 0 ≤ v.ord (J - algebraMap K F r) := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [map_zero, sub_zero]; exact hx
  · have hc : v.ord (-algebraMap K F r) = 0 := by rw [ord_neg, ord_algebraMap v hr]
    have hmin := min_ord_le_ord_add v hJ (neg_ne_zero.mpr ((_root_.map_ne_zero _).mpr hr))
      (by rw [← sub_eq_add_neg]; exact hJc r)
    rw [← sub_eq_add_neg, hc] at hmin
    exact le_trans (le_min hx le_rfl) hmin

theorem ord_sub_algebraMap_eq_zero_of_ne {J : F} (hJc : ∀ r : K, J - algebraMap K F r ≠ 0)
    {j₀ : K} (hj₀ : 1 ≤ v.ord (J - algebraMap K F j₀)) {r : K} (hr : r ≠ j₀) :
    v.ord (J - algebraMap K F r) = 0 := by
  have hsplit : J - algebraMap K F r = algebraMap K F (j₀ - r) + (J - algebraMap K F j₀) := by
    rw [map_sub, sub_add_sub_cancel']
  have hne : algebraMap K F (j₀ - r) ≠ 0 := (_root_.map_ne_zero _).mpr (sub_ne_zero.mpr hr.symm)
  have hc0 : v.ord (algebraMap K F (j₀ - r)) = 0 := ord_algebraMap v (sub_ne_zero.mpr hr.symm)
  have hlt : v.ord (algebraMap K F (j₀ - r)) < v.ord (J - algebraMap K F j₀) := by rw [hc0]; omega
  rw [hsplit, ord_add_eq_of_lt v hne (hJc j₀) hlt, hc0]

theorem ord_sub_le_ord_aeval [IsAlgClosed K] {J : F} (hJ : J ≠ 0) (hJc : ∀ r : K, J - algebraMap K F r ≠ 0)
    (hx : 0 ≤ v.ord J) {P : Polynomial K} (hPmonic : P.Monic) {j₀ : K} (hroot : P.IsRoot j₀) :
    v.ord (J - algebraMap K F j₀) ≤ v.ord (aeval J P) := by
  classical
  have hProots : P = (P.roots.map fun r => X - C r).prod := by
    conv_lhs => rw [Splits.eq_prod_roots (IsAlgClosed.splits P), hPmonic.leadingCoeff, map_one, one_mul]
  have haeval : aeval J P = (P.roots.map fun r => J - algebraMap K F r).prod := by
    conv_lhs => rw [hProots]
    rw [map_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro r _
    simp [Function.comp]
  have hfac_ne : ∀ g ∈ (P.roots.map fun r => J - algebraMap K F r), g ≠ 0 := by
    intro g hg
    obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hg
    exact hJc r
  have hord_sum : v.ord (aeval J P) = (P.roots.map fun r => v.ord (J - algebraMap K F r)).sum := by
    rw [haeval, ord_multiset_prod v _ hfac_ne, Multiset.map_map]
    rfl
  have hmem : j₀ ∈ P.roots := (mem_roots hPmonic.ne_zero).mpr hroot
  rw [hord_sum, ← Multiset.cons_erase hmem, Multiset.map_cons, Multiset.sum_cons]
  have hrest : 0 ≤ ((P.roots.erase j₀).map fun r => v.ord (J - algebraMap K F r)).sum :=
    Multiset.sum_nonneg fun z hz => by
      obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hz
      exact ord_sub_algebraMap_nonneg v hJ hJc hx r
  omega

end Ord

theorem exists_act (κ : Type) [Field κ] (M : ℕ) [NeZero M]
    (J : ↥(ModularCurve.x1FunctionFieldC κ M)) (hJ : (J : LaurentSeries κ) = ModularCurve.jqModC κ)
    (g : ModularForm (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 1) (pg : PowerSeries ℤ) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC κ pg ≠ 0) :
    ∃ a c t : ↥(ModularCurve.x1FunctionFieldC κ M),
      ((a : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ) = intSeriesC κ eisenstein4 / intSeriesC κ (pg ^ 4) ∧
      ((t : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ) =
        intSeriesC κ (PowerSeries.X * dedekindEtaUnit) / intSeriesC κ (pg ^ 12) ∧
      a ^ 3 = J * t ∧ c ^ 2 = (J - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728) * t ∧
      a ≠ 0 ∧ c ≠ 0 ∧ t ≠ 0 ∧ J ≠ 0 ∧ J - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728 ≠ 0 := by
  classical
  have hΓ : ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := Subgroup.map_le_range _ _
  have hT : ModularGroup.T ∈ Gamma1 M := by
    rw [Gamma1_mem]; simp [ModularGroup.T]
  have h1per : (1 : ℝ) ∈ ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [Subgroup.mem_strictPeriods_iff]
    refine ⟨ModularGroup.T, hT, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom]
  have hIpow : ∀ {w : ℤ} (f : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) w)
      (pf : PowerSeries ℤ), IsIntegralQExp f pf → ∀ n : ℕ, IsIntegralQExp (f.pow n) (pf ^ n) := by
    intro w f pf hf n
    unfold IsIntegralQExp at hf ⊢
    rw [map_pow, hf, ModularForm.qExpansion_pow one_pos h1per]
  have hE4 : IsIntegralQExp (restrictForm hΓ E₄) eisenstein4 := isIntegralQExp_E4
  have hE6 : IsIntegralQExp (restrictForm hΓ E₆) eisenstein6 := isIntegralQExp_E6
  have hg4 := hIpow g pg hg 4
  have hg6 := hIpow g pg hg 6
  have hg12 := hIpow g pg hg 12
  have hcast : ∀ {x y : ℤ} (hxy : x = y) (f : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) x)
      (pf : PowerSeries ℤ), IsIntegralQExp f pf → IsIntegralQExp (ModularForm.mcast hxy f) pf := by
    intro x y hxy f pf hf
    unfold IsIntegralQExp at hf ⊢
    rw [coe_mcast]; exact hf
  have hg4ne : intSeriesC κ (pg ^ 4) ≠ 0 := by rw [intSeriesC_pow]; exact pow_ne_zero _ hg0
  have hg6ne : intSeriesC κ (pg ^ 6) ≠ 0 := by rw [intSeriesC_pow]; exact pow_ne_zero _ hg0
  have hg12ne : intSeriesC κ (pg ^ 12) ≠ 0 := by rw [intSeriesC_pow]; exact pow_ne_zero _ hg0
  have hΔne : intSeriesC κ (PowerSeries.X * dedekindEtaUnit) ≠ 0 := by
    rw [intSeriesC_mul]
    refine mul_ne_zero ?_ ?_
    · rw [intSeriesC, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]
      exact HahnSeries.single_ne_zero one_ne_zero
    · intro h0
      have h1 := HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm)
      have h2 := congrArg (PowerSeries.coeff 0) h1
      rw [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_dedekindEtaUnit,
        map_one, map_zero] at h2
      exact one_ne_zero h2
  have hE4ne : intSeriesC κ eisenstein4 ≠ 0 := by
    intro h0
    have h1 := HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm)
    have h2 := congrArg (PowerSeries.coeff 0) h1
    rw [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_eisenstein4,
      map_one, map_zero] at h2
    exact one_ne_zero h2
  have hE6ne : intSeriesC κ eisenstein6 ≠ 0 := by
    intro h0
    have h1 := HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm)
    have h2 := congrArg (PowerSeries.coeff 0) h1
    have h3 : PowerSeries.coeff 0 eisenstein6 = 1 := by simp [eisenstein6]
    rw [PowerSeries.coeff_map, h3, map_one, map_zero] at h2
    exact one_ne_zero h2
  have hmem : ∀ {w : ℤ} (F G : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) w) (pF pG : PowerSeries ℤ),
      IsIntegralQExp F pF → IsIntegralQExp G pG → intSeriesC κ pG ≠ 0 →
      intSeriesC κ pF / intSeriesC κ pG ∈ ModularCurve.x1FunctionFieldC κ M := by
    intro w F G pF pG hF hG hG0
    rw [x1FunctionFieldC, qExpFunctionFieldC]
    exact IntermediateField.subset_adjoin _ _ ⟨w, F, G, pF, pG, hF, hG, hG0, rfl⟩
  have hwa : (4 : ℤ) = ((4 : ℕ) : ℤ) * (1 : ℤ) := by norm_num
  have hwc : (6 : ℤ) = ((6 : ℕ) : ℤ) * (1 : ℤ) := by norm_num
  have hwt : (12 : ℤ) = ((12 : ℕ) : ℤ) * (1 : ℤ) := by norm_num
  have hamem := hmem (restrictForm hΓ E₄) (ModularForm.mcast hwa.symm (g.pow 4)) eisenstein4 (pg ^ 4)
    hE4 (hcast hwa.symm _ _ hg4) hg4ne
  have hcmem := hmem (restrictForm hΓ E₆) (ModularForm.mcast hwc.symm (g.pow 6)) eisenstein6 (pg ^ 6)
    hE6 (hcast hwc.symm _ _ hg6) hg6ne
  have hΔI : IsIntegralQExp (restrictForm hΓ ((CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ModularForm 𝒮ℒ 12))
      (PowerSeries.X * dedekindEtaUnit) := by
    unfold IsIntegralQExp
    rw [coe_restrictForm]
    exact ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm
  have htmem := hmem (restrictForm hΓ ((CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ModularForm 𝒮ℒ 12))
    (ModularForm.mcast hwt.symm (g.pow 12)) (PowerSeries.X * dedekindEtaUnit) (pg ^ 12)
    hΔI (hcast hwt.symm _ _ hg12) hg12ne
  set a : ↥(ModularCurve.x1FunctionFieldC κ M) := ⟨_, hamem⟩ with ha
  set c : ↥(ModularCurve.x1FunctionFieldC κ M) := ⟨_, hcmem⟩ with hc
  set t : ↥(ModularCurve.x1FunctionFieldC κ M) := ⟨_, htmem⟩ with htdef
  set e4 := intSeriesC κ eisenstein4 with he4
  set e6 := intSeriesC κ eisenstein6 with he6
  set eg := intSeriesC κ pg with heg
  set eΔ := intSeriesC κ (PowerSeries.X * dedekindEtaUnit) with heΔ
  have hj4 : ModularCurve.jqModC κ = e4 ^ 3 / eΔ := by
    rw [eq_div_iff hΔne, he4, ← intSeriesC_pow]; exact jqModC_mul_delta κ
  have hj6 : ModularCurve.jqModC κ - 1728 = e6 ^ 2 / eΔ := by
    rw [eq_div_iff hΔne, he6, ← intSeriesC_pow]; exact jqModC_sub_mul_delta κ
  have hacoe : ((a : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ) = e4 / eg ^ 4 := by
    rw [ha]; show intSeriesC κ eisenstein4 / intSeriesC κ (pg ^ 4) = _; rw [intSeriesC_pow]
  have hccoe : ((c : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ) = e6 / eg ^ 6 := by
    rw [hc]; show intSeriesC κ eisenstein6 / intSeriesC κ (pg ^ 6) = _; rw [intSeriesC_pow]
  have htcoe : ((t : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ) = eΔ / eg ^ 12 := by
    rw [htdef]; show intSeriesC κ (PowerSeries.X * dedekindEtaUnit) / intSeriesC κ (pg ^ 12) = _; rw [intSeriesC_pow]
  have h1728 : ((algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728 : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ) = 1728 := by
    rw [map_ofNat]; push_cast; rfl
  have ha3 : a ^ 3 = J * t := by
    apply Subtype.ext
    push_cast
    rw [hacoe, hJ, htcoe, hj4]
    field_simp
  have h1728' : algebraMap κ (LaurentSeries κ) 1728 = 1728 := map_ofNat _ _
  have hc2 : c ^ 2 = (J - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728) * t := by
    apply Subtype.ext
    push_cast
    rw [hccoe, h1728', hJ, htcoe, hj6]
    field_simp
  have hne_of_coe : ∀ {z : ↥(ModularCurve.x1FunctionFieldC κ M)}, (z : LaurentSeries κ) ≠ 0 → z ≠ 0 :=
    fun h h0 => h (by rw [h0]; rfl)
  have ha0 : a ≠ 0 := hne_of_coe (by rw [hacoe]; exact div_ne_zero hE4ne (pow_ne_zero _ hg0))
  have hc0 : c ≠ 0 := hne_of_coe (by rw [hccoe]; exact div_ne_zero hE6ne (pow_ne_zero _ hg0))
  have ht0 : t ≠ 0 := hne_of_coe (by rw [htcoe]; exact div_ne_zero hΔne (pow_ne_zero _ hg0))
  have hJ0 : J ≠ 0 := hne_of_coe (by rw [hJ, hj4]; exact div_ne_zero (pow_ne_zero _ hE4ne) hΔne)
  have hJ' : J - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728 ≠ 0 :=
    hne_of_coe (by rw [AddSubgroupClass.coe_sub, h1728, hJ, hj6]; exact div_ne_zero (pow_ne_zero _ hE6ne) hΔne)
  refine ⟨a, c, t, ?_, ?_, ha3, hc2, ha0, hc0, ht0, hJ0, hJ'⟩
  · rw [ha]
  · rw [htdef]

end SsnvE96

set_option maxHeartbeats 16000000 in

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
    (u : ↥(ModularCurve.x1FunctionFieldC κ M))
    (hu : (u : LaurentSeries κ) =
      intSeriesC κ (PowerSeries.mk fun n => if n = 0 then (1 : ℤ) else 240 * (ArithmeticFunction.sigma 3 n : ℤ)) /
        intSeriesC κ (w.series ^ 4)) :
    ∃ x : Place κ ↥(ModularCurve.x1FunctionFieldC κ M),
      0 ≤ x.ord J ∧ 3 * x.ord u = x.ord J ∧
      1 ≤ x.ord (Polynomial.aeval J (X ^ e₄ * (X - C (1728 : κ)) ^ e₆ * S)) := by
  classical
  have hp := (inferInstance : Fact p.Prime).out

  obtain ⟨t₁, ht₁, htr, hfd, -⟩ :=
    ModularCurve.exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC
      p M hM hpM κ
  obtain rfl : t₁ = J := Subtype.ext (ht₁.trans hJ.symm)
  haveI := hfd
  haveI hCO : IsCurveOver κ ↥(ModularCurve.x1FunctionFieldC κ M) := isCurveOver_of_isAlgClosed_of_transcendental t₁ htr
  set N : ℕ := Module.finrank ↥(IntermediateField.adjoin κ ({t₁} : Set ↥(ModularCurve.x1FunctionFieldC κ M))) ↥(ModularCurve.x1FunctionFieldC κ M) with hNdef
  have hNpos : 0 < N := Module.finrank_pos

  obtain ⟨a, c, t, hacoe, htcoe, ha3, hc2, ha0, hc0, ht0, hJ0, hJ'⟩ :=
    SsnvE96.exists_act κ M t₁ hJ w.form w.series w.isIntegralQExp w.intSeriesC_ne_zero
  have hua : u = a := by
    apply Subtype.ext
    rw [hu, hacoe, SsnvE96.eisenstein4_eq_mk_sigma]
  obtain ⟨T, hT, hTREGk⟩ := ModularCurve.exists_coe_eq_div_pow_and_mul_min_ord_le_ord_x1FunctionFieldC
    p κ M hpM t₁ hJ 1 w.form w.series w.isIntegralQExp w.intSeriesC_ne_zero
  rw [pow_one] at hT
  have hTREG : ∀ y : Place κ ↥(ModularCurve.x1FunctionFieldC κ M), min 0 (y.ord t₁) ≤ y.ord T := fun y => by
    have := hTREGk y; rwa [Nat.cast_one, one_mul] at this
  have hTt : T = t⁻¹ := by
    apply Subtype.ext
    push_cast
    rw [hT, htcoe, inv_div]
  have hT0 : T ≠ 0 := by rw [hTt]; exact inv_ne_zero ht0
  have hJc : ∀ r : κ, t₁ - algebraMap κ _ r ≠ 0 := by
    intro r h
    apply htr
    rw [sub_eq_zero] at h
    rw [h]; exact isAlgebraic_algebraMap r

  have hordT : ∀ y : Place κ ↥(ModularCurve.x1FunctionFieldC κ M), y.ord T = - y.ord t := by
    intro y; rw [hTt, y.ord_inv]
  have hR3 : ∀ y : Place κ ↥(ModularCurve.x1FunctionFieldC κ M), 3 * y.ord u = y.ord t₁ + y.ord t := by
    intro y
    have h := congrArg y.ord ha3
    rw [SsnvE96.ord_pow', y.ord_mul hJ0 ht0] at h
    rw [hua]; exact_mod_cast h
  have hR2 : ∀ y : Place κ ↥(ModularCurve.x1FunctionFieldC κ M),
      2 * y.ord c = y.ord (t₁ - algebraMap κ _ 1728) + y.ord t := by
    intro y
    have h := congrArg y.ord hc2
    rw [SsnvE96.ord_pow', y.ord_mul hJ' ht0] at h
    exact_mod_cast h

  obtain ⟨hSdeg, he₄, he₆, hSmonic, hSsep, hSnat, -, -, -⟩ := hS
  set P : Polynomial κ := X ^ e₄ * (X - C (1728 : κ)) ^ e₆ * S with hPdef
  have hPmonic : P.Monic := ((monic_X_pow e₄).mul ((monic_X_sub_C _).pow e₆)).mul hSmonic
  have hPnat : P.natDegree = e₄ + e₆ + m := by
    rw [hPdef, ((monic_X_pow e₄).mul ((monic_X_sub_C _).pow e₆)).natDegree_mul hSmonic,
      (monic_X_pow e₄).natDegree_mul ((monic_X_sub_C _).pow e₆), natDegree_X_pow, natDegree_pow,
      natDegree_X_sub_C, mul_one, hSnat]
  have hp5' : 4 ≤ p - 1 := by omega
  have hPdeg : P.degree ≠ 0 := by
    rw [degree_eq_natDegree hPmonic.ne_zero, hPnat]
    exact_mod_cast (show e₄ + e₆ + m ≠ 0 by omega)
  obtain ⟨j₀, hj₀⟩ := IsAlgClosed.exists_root P hPdeg

  have h1728 : (1728 : κ) ≠ 0 := by
    intro h
    have h' : (p : ℕ) ∣ 1728 := by
      rw [← CharP.cast_eq_zero_iff κ p 1728]; exact_mod_cast h
    have h2 : p ∣ 2 ^ 6 * 3 ^ 3 := by norm_num at h' ⊢; exact h'
    rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3); omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3); omega

  obtain ⟨S0, hS0mem, hS0sum⟩ :=
    AlgebraicCurve.exists_finset_sum_ord_sub_algebraMap_eq_finrank_of_isAlgClosed κ t₁ htr hfd j₀
  obtain ⟨Sp, hSpmem, hSpsum⟩ := AlgebraicCurve.exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed κ t₁ htr hfd
  obtain ⟨PT, hPT, hPT0⟩ := (IsCurveOver.hasPrincipalDivisors (K := κ) (F := ↥(ModularCurve.x1FunctionFieldC κ M))).exists_divisor T hT0
  have hsumT : ∑ v ∈ PT.support, v.ord T = 0 := by
    have h := hPT0
    rw [AlgebraicCurve.Divisor.degree_eq_sum_support] at h
    rw [← h]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [IsCurveOver.deg_eq_one_of_isAlgClosed v, Nat.cast_one, mul_one, hPT v]

  have hF : ∀ v ∈ S0, 0 ≤ v.ord t₁ ∧ (3 : ℤ) ∣ v.ord t₁ ∧ (2 : ℤ) ∣ v.ord (t₁ - algebraMap κ _ 1728) ∧
      v.ord (t₁ - algebraMap κ _ j₀) = (ModularCurve.jWidth j₀ : ℤ) ∧ 0 ≤ v.ord T ∧ (6 : ℤ) ∣ v.ord T := by
    intro v hv
    have h1 : 1 ≤ v.ord (t₁ - algebraMap κ _ j₀) := by have := (hS0mem v).mp hv; omega

    have hordJ : v.ord t₁ = if j₀ = 0 then v.ord (t₁ - algebraMap κ _ j₀) else 0 := by
      split_ifs with hj
      · rw [hj, map_zero, sub_zero]
      · have := SsnvE96.ord_sub_algebraMap_eq_zero_of_ne v hJc h1 (Ne.symm hj)
        rwa [map_zero, sub_zero] at this
    have hx : 0 ≤ v.ord t₁ := by rw [hordJ]; split_ifs <;> omega
    have hFR := ModularCurve.ord_sub_algebraMap_eq_jWidth_of_place_x1FunctionFieldC p hp5 κ M hM hpM t₁ hJ v hx j₀ h1
    have h3 : (3 : ℤ) ∣ v.ord t₁ := by
      rw [hordJ]
      split_ifs with hj
      · rw [hFR, ModularCurve.jWidth_of_eq_zero hj]; norm_num
      · exact dvd_zero _
    have h2 : (2 : ℤ) ∣ v.ord (t₁ - algebraMap κ _ 1728) := by
      by_cases hj : j₀ = 1728
      · rw [← hj, hFR, ModularCurve.jWidth_of_eq_1728 hj (by rw [hj]; exact h1728)]; norm_num
      · rw [SsnvE96.ord_sub_algebraMap_eq_zero_of_ne v hJc h1 (Ne.symm hj)]; exact dvd_zero _
    have hTnonneg : 0 ≤ v.ord T := by have := hTREG v; rw [min_eq_left hx] at this; exact this
    refine ⟨hx, h3, h2, hFR, hTnonneg, ?_⟩
    have e3 := hR3 v
    have e2 := hR2 v
    have eT := hordT v
    omega

  by_contra hcon
  push Not at hcon

  have hbig : ∀ v ∈ S0, (6 : ℤ) ≤ v.ord T := by
    intro v hv
    obtain ⟨hx, -, -, -, hTnn, h6⟩ := hF v hv
    have hne : v.ord T ≠ 0 := by
      intro h0
      have hlt := hcon v hx (by have := hR3 v; have := hordT v; omega)
      have h1 : 1 ≤ v.ord (t₁ - algebraMap κ _ j₀) := by have := (hS0mem v).mp hv; omega
      have h2 := SsnvE96.ord_sub_le_ord_aeval v hJ0 hJc hx hPmonic hj₀
      omega
    omega

  set A := PT.support.filter (fun v => 0 ≤ v.ord t₁) with hAdef
  set B := PT.support.filter (fun v => ¬ 0 ≤ v.ord t₁) with hBdef
  have hsplit : ∑ v ∈ A, v.ord T + ∑ v ∈ B, v.ord T = 0 := by
    rw [hAdef, hBdef, Finset.sum_filter_add_sum_filter_not, hsumT]

  have hB : -(N : ℤ) ≤ ∑ v ∈ B, v.ord T := by
    have h1 : ∑ v ∈ B, v.ord t₁ ≤ ∑ v ∈ B, v.ord T := by
      refine Finset.sum_le_sum fun v hv => ?_
      have hneg : v.ord t₁ < 0 := by rw [hBdef, Finset.mem_filter] at hv; omega
      have := hTREG v
      rw [min_eq_right (by omega)] at this
      exact this
    have h2 : ∑ v ∈ B, (-v.ord t₁) ≤ ∑ v ∈ Sp, (-v.ord t₁) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro v hv
        rw [hBdef, Finset.mem_filter] at hv
        exact (hSpmem v).mpr (by omega)
      · intro v hv _
        have := (hSpmem v).mp hv; omega
    rw [hSpsum] at h2
    have h3 : ∑ v ∈ B, (-v.ord t₁) = -∑ v ∈ B, v.ord t₁ := Finset.sum_neg_distrib ..
    rw [h3] at h2
    linarith
  have hA : ∑ v ∈ A, v.ord T ≤ N := by linarith

  have hsub : S0 ⊆ A := by
    intro v hv
    rw [hAdef, Finset.mem_filter, Finsupp.mem_support_iff, hPT v]
    obtain ⟨hx, -⟩ := hF v hv
    have := hbig v hv
    exact ⟨by omega, hx⟩
  have hAnonneg : ∀ v ∈ A, v ∉ S0 → 0 ≤ v.ord T := by
    intro v hv _
    rw [hAdef, Finset.mem_filter] at hv
    have := hTREG v
    rw [min_eq_left hv.2] at this
    exact this
  have h6 : 6 * (S0.card : ℤ) ≤ ∑ v ∈ A, v.ord T := by
    calc 6 * (S0.card : ℤ) = ∑ v ∈ S0, (6 : ℤ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ S0, v.ord T := Finset.sum_le_sum hbig
      _ ≤ ∑ v ∈ A, v.ord T := Finset.sum_le_sum_of_subset_of_nonneg hsub hAnonneg

  have hN3 : (N : ℤ) ≤ 3 * S0.card := by
    have h1 : (N : ℤ) = ∑ v ∈ S0, (ModularCurve.jWidth j₀ : ℤ) := by
      rw [← hS0sum]
      exact Finset.sum_congr rfl fun v hv => (hF v hv).2.2.2.1
    rw [h1, Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hw : (ModularCurve.jWidth j₀ : ℤ) ≤ 3 := by
      rcases ModularCurve.jWidth_eq_one_or j₀ with h | h | h <;> rw [h] <;> norm_num
    have hc : (0 : ℤ) ≤ S0.card := Nat.cast_nonneg _
    nlinarith
  have : (N : ℤ) ≤ 0 := by linarith
  have : (0 : ℤ) < N := by exact_mod_cast hNpos
  linarith

end S_ModularCurve_exists_place_x1FunctionFieldC_ord_aeval_pos_of_integralWeightOneForm
end P2MW
export P2MW.S_ModularCurve_exists_place_x1FunctionFieldC_ord_aeval_pos_of_integralWeightOneForm (solution)
