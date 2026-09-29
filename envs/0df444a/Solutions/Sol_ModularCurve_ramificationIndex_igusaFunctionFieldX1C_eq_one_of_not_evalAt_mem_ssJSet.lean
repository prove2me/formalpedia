-- Prove2me | solution 1 for ModularCurve.ramificationIndex_igusaFunctionFieldX1C_eq_one_of_not_evalAt_mem_ssJSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/ed6c6e92-1572-5dbe-8029-2a7e147f034c

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_QExpansionDiff
import Theorems.Thm_ModularCurve_IgusaCover_ramificationIndexAlong_incl_eq_of_ord_hasseRootFn_pow_igusaFunctionFieldX1C
import Theorems.Thm_ModularCurve_hasseRootFn_pow_mem_and_finite_and_isSeparable_igusaFunctionFieldX1C
import Theorems.Thm_ModularCurve_pow_twelve_mul_pow_sub_one_eq_of_coe_eq_hasseRootFn_pow
import Theorems.Thm_ModularCurve_twelve_dvd_ord_of_coe_eq_div_of_ord_nonneg_x1FunctionFieldC
import Theorems.Thm_ModularCurve_twelve_dvd_ord_sub_ord_of_coe_eq_div_of_ord_neg_x1FunctionFieldC
import Theorems.Thm_ModularCurve_exists_separable_thetaL_jqModC_pow_mul_aeval_eq
import Theorems.Thm_ModularCurve_mem_ssJSet_iff_eval_eq_zero_of_thetaL_pow_mul_aeval_eq
import Theorems.Thm_ModularCurve_isRational_place_x1FunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict
import Theorems.Thm_AlgebraicCurve_Place_mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_of_lt_five
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ramificationIndex_igusaFunctionFieldX1C_eq_one_of_not_evalAt_mem_ssJSet
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub"
p2m_attr_erase "instance" "KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"
p2m_attr_erase "simp" "CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec"
p2m_attr_erase "simp" "CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar"
p2m_attr_erase "simp" "ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "ModularCurve CongruenceSubgroup AlgebraicCurve~genus"
open scoped MatrixGroups

open Polynomial
open scoped ModularForm

namespace UnramAux

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

end UnramAux

namespace UnramQAux

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

end UnramQAux

open UnramQAux

namespace UnramAux
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_sub_algebraMap_eq_of_ord_neg {J : F} (hJ : J ≠ 0) (hneg : v.ord J < 0) (r : K) :
    v.ord (J - algebraMap K F r) = v.ord J := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [map_zero, sub_zero]
  · have hne : -algebraMap K F r ≠ 0 := neg_ne_zero.mpr ((_root_.map_ne_zero _).mpr hr)
    have h0 : v.ord (-algebraMap K F r) = 0 := by rw [ord_neg, ord_algebraMap v hr]
    rw [sub_eq_add_neg, ord_add_eq_of_lt v hJ hne (by rw [h0]; exact hneg)]

theorem ord_aeval_eq_mul_of_ord_neg [IsAlgClosed K] {J : F} (hJ : J ≠ 0) (hneg : v.ord J < 0)
    (hJc : ∀ r : K, J - algebraMap K F r ≠ 0) {Q : K[X]} (hQ : Q.Monic) :
    v.ord (aeval J Q) = Q.natDegree * v.ord J := by
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
  have hcard : Multiset.card Q.roots = Q.natDegree := (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits Q))
  rw [haeval, ord_multiset_prod v _ hfac_ne, Multiset.map_map]
  have : (Q.roots.map (v.ord ∘ fun r => J - algebraMap K F r)) = Q.roots.map (fun _ => v.ord J) :=
    Multiset.map_congr rfl (fun r _ => by simp [Function.comp, ord_sub_algebraMap_eq_of_ord_neg v hJ hneg r])
  rw [this, Multiset.map_const', Multiset.sum_replicate, hcard, nsmul_eq_mul]

theorem mem_iff_ord_nonneg' {f : F} (hf : f ≠ 0) : f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥v.toValuationSubring
  constructor
  · intro hmem
    have hx0 : (⟨f, hmem⟩ : ↥v.toValuationSubring) ≠ 0 := fun h => hf (congrArg Subtype.val h)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    have h1 := v.ord_unit_smul_zpow u hϖ (n : ℤ)
    rw [zpow_natCast] at h1
    have h2 : f = ((u : ↥v.toValuationSubring) : F) * ((ϖ : F) ^ n) := by
      have := congrArg Subtype.val hu; simpa using this
    rw [h2, h1]; exact Int.natCast_nonneg n
  · intro h
    obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hϖ
    rw [hu]
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
    rw [hn, zpow_natCast]
    exact mul_mem (u : ↥v.toValuationSubring).2 (pow_mem ϖ.2 n)

end UnramAux

open UnramAux

set_option maxHeartbeats 6400000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
    (w : ModularCurve.IntegralWeightOneForm Ω M)
    (jIg : ↥(ModularCurve.igusaFunctionFieldX1C Ω M w)) (hjIg : (jIg : LaurentSeries Ω) = ModularCurve.jqModC Ω) :
    letI : Algebra ↥(ModularCurve.x1FunctionFieldC Ω M) ↥(ModularCurve.igusaFunctionFieldX1C Ω M w) :=
      (IntermediateField.inclusion (ModularCurve.x1FunctionFieldC_le_igusaFunctionFieldX1C Ω M w)).toRingHom.toAlgebra
    ∀ P : AlgebraicCurve.Place Ω ↥(ModularCurve.igusaFunctionFieldX1C Ω M w),
      ¬ (jIg ∈ P.toValuationSubring ∧ P.evalAt jIg ∈ ModularCurve.ssJSet p Ω) →
        P.ramificationIndex ↥(ModularCurve.x1FunctionFieldC Ω M) = 1 := by
  intro P hP
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨hbmem, hfin, -⟩ := ModularCurve.hasseRootFn_pow_mem_and_finite_and_isSeparable_igusaFunctionFieldX1C p M hM hpM Ω w
  letI algI : Algebra ↥(ModularCurve.x1FunctionFieldC Ω M) ↥(ModularCurve.igusaFunctionFieldX1C Ω M w) :=
    (IntermediateField.inclusion (ModularCurve.x1FunctionFieldC_le_igusaFunctionFieldX1C Ω M w)).toRingHom.toAlgebra
  haveI : IsScalarTower Ω ↥(ModularCurve.x1FunctionFieldC Ω M) ↥(ModularCurve.igusaFunctionFieldX1C Ω M w) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite ↥(ModularCurve.x1FunctionFieldC Ω M) ↥(ModularCurve.igusaFunctionFieldX1C Ω M w) := hfin
  haveI hII : Algebra.IsIntegral ↥(ModularCurve.x1FunctionFieldC Ω M) ↥(ModularCurve.igusaFunctionFieldX1C Ω M w) := Algebra.IsIntegral.of_finite _ _
  have hint : (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC Ω M) w.hasseRootFn).toRingHom.IsIntegral :=
    fun x => hII.isIntegral x
  set b : ↥(ModularCurve.x1FunctionFieldC Ω M) := ⟨w.hasseRootFn ^ (p - 1), hbmem⟩ with hbdef
  have hb : (b : LaurentSeries Ω) = w.hasseRootFn ^ (p - 1) := rfl

  have hK := (ModularCurve.IgusaCover.ramificationIndexAlong_incl_eq_of_ord_hasseRootFn_pow_igusaFunctionFieldX1C
    p M hM hpM Ω w hint b hb P).1
  show Place.ramificationIndexAlong (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC Ω M) w.hasseRootFn) P = 1
  apply hK

  set v : Place Ω ↥(ModularCurve.x1FunctionFieldC Ω M) := P.restrictAlong (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC Ω M) w.hasseRootFn) hint with hvdef
  have hvres : P.restrict ↥(ModularCurve.x1FunctionFieldC Ω M) = v := rfl
  have hrat : v.IsRational := ModularCurve.isRational_place_x1FunctionFieldC_of_isAlgClosed p M hM hpM Ω v

  obtain ⟨J, hJ, hJtr, -, -⟩ :=
    ModularCurve.exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC p M hM hpM Ω
  have hJIg : jIg = algebraMap ↥(ModularCurve.x1FunctionFieldC Ω M) ↥(ModularCurve.igusaFunctionFieldX1C Ω M w) J := Subtype.ext (hjIg.trans hJ.symm)

  have hjr : ∀ r : Ω, ModularCurve.jqModC Ω - algebraMap Ω (LaurentSeries Ω) r ≠ 0 := fun r h0 =>
    X_sub_C_ne_zero r (transcendental_iff.mp (transcendental_jqModC Ω) (X - C r)
      (by rw [map_sub, aeval_X, aeval_C]; exact h0))
  have hJc : ∀ a : Ω, J - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) a ≠ 0 := by
    intro a h0
    have h1 := congrArg (fun z : ↥(ModularCurve.x1FunctionFieldC Ω M) => (z : LaurentSeries Ω)) h0
    simp only [AddSubgroupClass.coe_sub, ZeroMemClass.coe_zero] at h1
    apply hjr a
    rw [← hJ]
    exact h1
  have hJ0 : J ≠ 0 := by have := hJc 0; rwa [map_zero, sub_zero] at this

  have hv : ¬ ((J : ↥(ModularCurve.x1FunctionFieldC Ω M)) ∈ v.toValuationSubring ∧ v.evalAt J ∈ ModularCurve.ssJSet p Ω) := by
    rintro ⟨hJv, hss⟩
    apply hP
    refine ⟨?_, ?_⟩
    · rw [hJIg]; rw [← hvres] at hJv; exact (Place.mem_restrict_iff P).mp hJv
    · rw [hJIg]
      rw [← hvres] at hJv hss hrat
      rw [AlgebraicCurve.Place.evalAt_algebraMap_eq_evalAt_restrict P hrat hJv]
      exact hss

  have hb0 : b ≠ 0 := by
    intro h0
    have := congrArg (fun z : ↥(ModularCurve.x1FunctionFieldC Ω M) => (z : LaurentSeries Ω)) h0
    simp only [ZeroMemClass.coe_zero] at this
    rw [hb] at this
    exact pow_ne_zero _ w.hasseRootFn_ne_zero this

  by_cases hp2 : p = 2
  · subst hp2
    have h1 : ((2 - 1 : ℕ) : ℤ) = 1 := by norm_num
    rw [h1]; exact one_dvd _

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
  have hT0 : T ≠ 0 := by
    intro h0
    have := congrArg (fun z : ↥(ModularCurve.x1FunctionFieldC Ω M) => (z : LaurentSeries Ω)) h0
    simp only [ZeroMemClass.coe_zero] at this
    rw [hT] at this
    exact div_ne_zero (by rw [intSeriesC_pow]; exact pow_ne_zero _ hw0) hΔ this

  rcases lt_or_ge (v.ord J) 0 with hneg | hnn
  ·
    obtain ⟨t, ht⟩ := ModularCurve.twelve_dvd_ord_sub_ord_of_coe_eq_div_of_ord_neg_x1FunctionFieldC p Ω M hM hpM w J hJ T hT v hneg
    by_cases hp3 : p = 3
    · subst hp3

      have hjΔ : jqModC Ω * intSeriesC Ω (PowerSeries.X * dedekindEtaUnit) = 1 := by
        rw [jqModC_mul_delta Ω, intSeriesC_pow, intSeriesC_eisenstein4_eq_one Ω, one_pow]
      have hbTJ : b ^ 6 * T = J := by
        apply Subtype.ext
        show (b : LaurentSeries Ω) ^ 6 * (intSeriesC Ω (w.series ^ 12) / intSeriesC Ω (PowerSeries.X * dedekindEtaUnit)) = (J : LaurentSeries Ω)
        rw [hb, hJ, IntegralWeightOneForm.hasseRootFn, ← pow_mul, show (3 - 1) * 6 = 12 from rfl, intSeriesC_pow, inv_pow,
          div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hw0), one_mul, eq_inv_of_mul_eq_one_left hjΔ]
      have hord : 6 * v.ord b + v.ord T = v.ord J := by
        rw [← hbTJ, Place.ord_mul _ (pow_ne_zero _ hb0) hT0, ← zpow_natCast, Place.ord_zpow]
        push_cast; ring
      refine ⟨-t, ?_⟩
      have h2 : ((3 - 1 : ℕ) : ℤ) = 2 := by norm_num
      rw [h2]
      show v.ord b = 2 * -t
      omega
    ·
      have hp5 : 5 ≤ p := by
        have h2 := hp.two_le
        have h4 : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
        omega
      obtain ⟨m, e₄, e₆, S, hS⟩ := ModularCurve.exists_separable_thetaL_jqModC_pow_mul_aeval_eq p hp5 Ω
      have hPT := ModularCurve.pow_twelve_mul_pow_sub_one_eq_of_coe_eq_hasseRootFn_pow p hp5 Ω M (by omega) hpM w m e₄ e₆ S hS J hJ b hb T hT
      obtain ⟨hm, he₄, he₆, hSmonic, hSsep, hSdeg, hS0, hS1728, -⟩ := hS
      have hJ1728 : J - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) 1728 ≠ 0 := hJc 1728
      have hSJ : aeval J S ≠ 0 := fun h0 => hSmonic.ne_zero (transcendental_iff.mp hJtr S h0)

      have hL : v.ord (b ^ 12 * T ^ (p - 1)) = 12 * v.ord b + (p - 1 : ℕ) * v.ord T := by
        rw [Place.ord_mul _ (pow_ne_zero _ hb0) (pow_ne_zero _ hT0), ord_pow', ord_pow']; push_cast; ring
      have hR : v.ord (J ^ (4 * e₄) * (J - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) 1728) ^ (6 * e₆) * (aeval J S) ^ 12) =
          (4 * e₄ + 6 * e₆ + 12 * m : ℕ) * v.ord J := by
        rw [Place.ord_mul _ (mul_ne_zero (pow_ne_zero _ hJ0) (pow_ne_zero _ hJ1728)) (pow_ne_zero _ hSJ),
          Place.ord_mul _ (pow_ne_zero _ hJ0) (pow_ne_zero _ hJ1728), ord_pow', ord_pow', ord_pow',
          ord_sub_algebraMap_eq_of_ord_neg v hJ0 hneg, ord_aeval_eq_mul_of_ord_neg v hJ0 hneg hJc hSmonic, hSdeg]
        push_cast; ring
      have hEq : 12 * v.ord b + (p - 1 : ℕ) * v.ord T = (4 * e₄ + 6 * e₆ + 12 * m : ℕ) * v.ord J := by
        rw [← hL, ← hR, hPT]
      have hm' : (4 * e₄ + 6 * e₆ + 12 * m : ℕ) = p - 1 := by omega
      rw [hm'] at hEq

      refine ⟨-t, ?_⟩
      have h12 : (12 : ℤ) * v.ord b = 12 * (((p - 1 : ℕ) : ℤ) * (-t)) := by
        linear_combination hEq - ((p - 1 : ℕ) : ℤ) * ht
      exact mul_left_cancel₀ (by norm_num : (12 : ℤ) ≠ 0) h12
  ·
    have hJv : J ∈ v.toValuationSubring := (mem_iff_ord_nonneg' v hJ0).mpr hnn
    set c : Ω := v.evalAt J with hcdef
    have hc : c ∉ ModularCurve.ssJSet p Ω := fun h => hv ⟨hJv, h⟩
    have hc1 : 1 ≤ v.ord (J - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) c) :=
      (AlgebraicCurve.Place.mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos v hrat J c (sub_ne_zero.mp (hJc c))).mp ⟨hJv, rfl⟩
    obtain ⟨t, ht⟩ := ModularCurve.twelve_dvd_ord_of_coe_eq_div_of_ord_nonneg_x1FunctionFieldC p Ω M hM hpM w J hJ T hT v hnn
    by_cases hp3 : p = 3
    · subst hp3
      have h0ss : (0 : Ω) ∈ ModularCurve.ssJSet 3 Ω := ModularCurve.zero_mem_ssJSet_of_lt_five (q := 3) (by norm_num)
      have hc0 : c ≠ 0 := fun h => hc (h ▸ h0ss)
      have hordJ : v.ord J = 0 := by
        have := ord_sub_algebraMap_eq_zero v hJc hc1 (r := 0) hc0.symm
        rwa [map_zero, sub_zero] at this
      have hjΔ : jqModC Ω * intSeriesC Ω (PowerSeries.X * dedekindEtaUnit) = 1 := by
        rw [jqModC_mul_delta Ω, intSeriesC_pow, intSeriesC_eisenstein4_eq_one Ω, one_pow]
      have hbTJ : b ^ 6 * T = J := by
        apply Subtype.ext
        show (b : LaurentSeries Ω) ^ 6 * (intSeriesC Ω (w.series ^ 12) / intSeriesC Ω (PowerSeries.X * dedekindEtaUnit)) = (J : LaurentSeries Ω)
        rw [hb, hJ, IntegralWeightOneForm.hasseRootFn, ← pow_mul, show (3 - 1) * 6 = 12 from rfl, intSeriesC_pow, inv_pow,
          div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hw0), one_mul, eq_inv_of_mul_eq_one_left hjΔ]
      have hord : 6 * v.ord b + v.ord T = v.ord J := by
        rw [← hbTJ, Place.ord_mul _ (pow_ne_zero _ hb0) hT0, ← zpow_natCast, Place.ord_zpow]
        push_cast; ring
      refine ⟨-t, ?_⟩
      have h2 : ((3 - 1 : ℕ) : ℤ) = 2 := by norm_num
      rw [h2]
      show v.ord b = 2 * -t
      omega
    ·
      have hp5 : 5 ≤ p := by
        have h2 := hp.two_le
        have h4 : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
        omega
      obtain ⟨m, e₄, e₆, S, hS⟩ := ModularCurve.exists_separable_thetaL_jqModC_pow_mul_aeval_eq p hp5 Ω
      have hbr := ModularCurve.mem_ssJSet_iff_eval_eq_zero_of_thetaL_pow_mul_aeval_eq p hp5 Ω m e₄ e₆ S hS
      have hPT := ModularCurve.pow_twelve_mul_pow_sub_one_eq_of_coe_eq_hasseRootFn_pow p hp5 Ω M (by omega) hpM w m e₄ e₆ S hS J hJ b hb T hT
      obtain ⟨hm, he₄, he₆, hSmonic, hSsep, hSdeg, hS0, hS1728, -⟩ := hS
      have hJ1728 : J - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) 1728 ≠ 0 := hJc 1728
      have hSJ : aeval J S ≠ 0 := fun h0 => hSmonic.ne_zero (transcendental_iff.mp hJtr S h0)

      have hcroot : Polynomial.eval c (X ^ e₄ * (X - C (1728 : Ω)) ^ e₆ * S) ≠ 0 := fun h => hc ((hbr c).mpr h)
      rw [eval_mul, eval_mul, eval_pow, eval_pow, eval_X, eval_sub, eval_X, eval_C] at hcroot
      have hSc : S.eval c ≠ 0 := fun h => hcroot (by rw [h, mul_zero])
      have h4 : (4 * e₄ : ℤ) * v.ord J = 0 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he₄ with h | h
        · subst h; simp
        · subst h
          have hc0 : c ≠ 0 := fun h0 => hcroot (by rw [h0]; simp)
          have : v.ord J = 0 := by
            have := ord_sub_algebraMap_eq_zero v hJc hc1 (r := 0) hc0.symm
            rwa [map_zero, sub_zero] at this
          rw [this, mul_zero]
      have h6 : (6 * e₆ : ℤ) * v.ord (J - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) 1728) = 0 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he₆ with h | h
        · subst h; simp
        · subst h
          have hc1728 : c ≠ 1728 := fun h0 => hcroot (by rw [h0]; simp)
          rw [ord_sub_algebraMap_eq_zero v hJc hc1 hc1728.symm, mul_zero]
      have h12 : v.ord (aeval J S) = 0 := ord_aeval_eq_zero v hJc hc1 hSmonic hSc
      have hL : v.ord (b ^ 12 * T ^ (p - 1)) = 12 * v.ord b + (p - 1 : ℕ) * v.ord T := by
        rw [Place.ord_mul _ (pow_ne_zero _ hb0) (pow_ne_zero _ hT0), ord_pow', ord_pow']; push_cast; ring
      have h4' : ((4 * e₄ : ℕ) : ℤ) * v.ord J = 0 := by push_cast; exact h4
      have h6' : ((6 * e₆ : ℕ) : ℤ) * v.ord (J - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) 1728) = 0 := by push_cast; exact h6
      have hR : v.ord (J ^ (4 * e₄) * (J - algebraMap Ω ↥(ModularCurve.x1FunctionFieldC Ω M) 1728) ^ (6 * e₆) * (aeval J S) ^ 12) = 0 := by
        rw [Place.ord_mul _ (mul_ne_zero (pow_ne_zero _ hJ0) (pow_ne_zero _ hJ1728)) (pow_ne_zero _ hSJ),
          Place.ord_mul _ (pow_ne_zero _ hJ0) (pow_ne_zero _ hJ1728), ord_pow', ord_pow', ord_pow', h4', h6', h12]
        simp
      have hEq : 12 * v.ord b + (p - 1 : ℕ) * v.ord T = 0 := by rw [← hL, hPT, hR]
      refine ⟨-t, ?_⟩
      have hkey : (12 : ℤ) * v.ord b = 12 * (((p - 1 : ℕ) : ℤ) * (-t)) := by
        linear_combination hEq - ((p - 1 : ℕ) : ℤ) * ht
      exact mul_left_cancel₀ (by norm_num : (12 : ℤ) ≠ 0) hkey

end S_ModularCurve_ramificationIndex_igusaFunctionFieldX1C_eq_one_of_not_evalAt_mem_ssJSet
end P2MW
export P2MW.S_ModularCurve_ramificationIndex_igusaFunctionFieldX1C_eq_one_of_not_evalAt_mem_ssJSet (solution)
