-- Prove2me | solution 1 for ModularCurve.natCard_smul_valuationSubring_eq_and_forall_sub_mem_nonunits_le_three_of_ringEquiv_x1FunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/0cf73f57-1b0d-50ce-a1b5-384feea4d398

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ValuationSubring_smul_eq_and_forall_smul_sub_mem_nonunits_iff_mem_inertia_and_card_eq_ramificationIdxIn
import Theorems.Thm_ValuationSubring_exists_mulSemiringAction_integralClosure_inf_fixedPoints_of_isDiscreteValuationRing
import Theorems.Thm_Ideal_map_valuationSubring_eq_maximalIdeal_pow_ramificationIdx
import Theorems.Thm_ModularCurve_ord_sub_algebraMap_eq_jWidth_of_place_x1FunctionFieldC
import Theorems.Thm_ModularCurve_exists_ringHom_qExpFunctionFieldC_coe_eq_coeffMap
import Theorems.Thm_LaurentSeries_exists_eq_C_of_isAlgebraic
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap_eq_ord_of_comap_eq_of_isSeparable_of_adjoin_eq_top
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_natCard_smul_valuationSubring_eq_and_forall_sub_mem_nonunits_le_three_of_ringEquiv_x1FunctionFieldC
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex"
p2m_attr_erase "instance" "TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg"
p2m_attr_erase "instance" "KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero"
p2m_attr_erase "simp" "ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero"
p2m_attr_erase "simp" "compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec"

set_option autoImplicit false

noncomputable section

open IsLocalRing
open scoped Pointwise
p2m_open "ModularCurve P2MW.S_ModularCurve_natCard_smul_valuationSubring_eq_and_forall_sub_mem_nonunits_le_three_of_ringEquiv_x1FunctionFieldC.ModularCurve AlgebraicCurve"
open scoped MatrixGroups IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "intSeriesC intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset x1FunctionFieldC ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single jqModC map_jqModC jWidth jWidth_eq_one_or ord_sub_algebraMap_eq_jWidth_of_place_x1FunctionFieldC exists_ringHom_qExpFunctionFieldC_coe_eq_coeffMap coeff_jqModC_neg_one jqModC_mem_intFormRatiosC exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap"
namespace T4Core
p2m_open "ModularCurve"

section ConstExt

variable (κ κ' : Type*) [Field κ] [Field κ'] [Algebra κ κ'] (M : ℕ)

omit [Algebra κ κ'] in

theorem coe_algebraMap_x1FunctionFieldC (c : κ) :
    ((algebraMap κ ↥(x1FunctionFieldC κ M) c : ↥(x1FunctionFieldC κ M)) : LaurentSeries κ) =
      algebraMap κ (LaurentSeries κ) c := rfl

theorem coeffMap_intSeriesC (p : PowerSeries ℤ) :
    coeffMap (algebraMap κ κ') (intSeriesC κ p) = intSeriesC κ' p := by
  ext n
  rw [coeffMap_coeff, intSeriesC, intSeriesC]
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]
  · rw [ofPowerSeries_coeff_of_neg _ hn, ofPowerSeries_coeff_of_neg _ hn, map_zero]

theorem exists_coeffMap_eq_of_mem_intFormRatiosC (Γ : Subgroup SL(2, ℤ)) {x' : LaurentSeries κ'}
    (hx' : x' ∈ intFormRatiosC κ' Γ) :
    ∃ x ∈ intFormRatiosC κ Γ, coeffMap (algebraMap κ κ') x = x' := by
  obtain ⟨w, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx'
  have hg0κ : intSeriesC κ pg ≠ 0 := by
    intro h
    apply hg0
    rw [← coeffMap_intSeriesC κ κ', h, map_zero]
  exact ⟨_, ⟨w, f, g, pf, pg, hf, hg, hg0κ, rfl⟩, by rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]⟩

theorem coeffMap_algebraMap_const (c : κ) :
    coeffMap (algebraMap κ κ') (algebraMap κ (LaurentSeries κ) c) =
      algebraMap κ' (LaurentSeries κ') (algebraMap κ κ' c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

def constExt : ↥(x1FunctionFieldC κ M) →+* ↥(x1FunctionFieldC κ' M) :=
  (ModularCurve.exists_ringHom_qExpFunctionFieldC_coe_eq_coeffMap (algebraMap κ κ')
    (CongruenceSubgroup.Gamma1 M)).choose

theorem coe_constExt (f : ↥(x1FunctionFieldC κ M)) :
    ((constExt κ κ' M f : ↥(x1FunctionFieldC κ' M)) : LaurentSeries κ') =
      coeffMap (algebraMap κ κ') (f : LaurentSeries κ) :=
  (ModularCurve.exists_ringHom_qExpFunctionFieldC_coe_eq_coeffMap (algebraMap κ κ')
    (CongruenceSubgroup.Gamma1 M)).choose_spec f

theorem constExt_eq_of_coe_eq_jqModC (J : ↥(x1FunctionFieldC κ M)) (J' : ↥(x1FunctionFieldC κ' M))
    (hJ : (J : LaurentSeries κ) = jqModC κ) (hJ' : (J' : LaurentSeries κ') = jqModC κ') :
    constExt κ κ' M J = J' := by
  apply Subtype.ext
  rw [coe_constExt, hJ, hJ']
  exact map_jqModC (algebraMap κ κ')

theorem constExt_algebraMap (c : κ) :
    constExt κ κ' M (algebraMap κ ↥(x1FunctionFieldC κ M) c) =
      algebraMap κ' ↥(x1FunctionFieldC κ' M) (algebraMap κ κ' c) := by
  apply Subtype.ext
  rw [coe_constExt, coe_algebraMap_x1FunctionFieldC, coe_algebraMap_x1FunctionFieldC, coeffMap_algebraMap_const]

@[reducible] def constExtAlgebra : Algebra ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC κ' M) :=
  (constExt κ κ' M).toAlgebra

theorem coe_algebraMap_constExtAlgebra (f : ↥(x1FunctionFieldC κ M)) :
    letI := constExtAlgebra κ κ' M
    ((algebraMap ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC κ' M) f : ↥(x1FunctionFieldC κ' M)) :
        LaurentSeries κ') = coeffMap (algebraMap κ κ') (f : LaurentSeries κ) :=
  coe_constExt κ κ' M f

variable [Algebra ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC κ' M)]
  (hι : ∀ f : ↥(x1FunctionFieldC κ M),
    ((algebraMap ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC κ' M) f : ↥(x1FunctionFieldC κ' M)) :
      LaurentSeries κ') = coeffMap (algebraMap κ κ') (f : LaurentSeries κ))

include hι in

theorem algebraMap_algebraMap_eq (c : κ) :
    algebraMap ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC κ' M) (algebraMap κ ↥(x1FunctionFieldC κ M) c) =
      algebraMap κ' ↥(x1FunctionFieldC κ' M) (algebraMap κ κ' c) := by
  apply Subtype.ext
  rw [hι, coe_algebraMap_x1FunctionFieldC, coe_algebraMap_x1FunctionFieldC, coeffMap_algebraMap_const]

include hι in
theorem algebraMap_comp_algebraMap_eq :
    (algebraMap ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC κ' M)).comp (algebraMap κ ↥(x1FunctionFieldC κ M)) =
      (algebraMap κ' ↥(x1FunctionFieldC κ' M)).comp (algebraMap κ κ') :=
  RingHom.ext (algebraMap_algebraMap_eq κ κ' M hι)

set_option synthInstance.maxHeartbeats 1600000 in
include hι in

theorem isScalarTower_of_coe_algebraMap_eq_coeffMap
    [Algebra κ ↥(x1FunctionFieldC κ' M)] [IsScalarTower κ κ' ↥(x1FunctionFieldC κ' M)] :
    IsScalarTower κ ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC κ' M) :=
  IsScalarTower.of_algebraMap_eq fun c =>
    ((algebraMap_algebraMap_eq κ κ' M hι c).trans
      (IsScalarTower.algebraMap_apply κ κ' ↥(x1FunctionFieldC κ' M) c).symm).symm

include hι in

theorem isIntegral_algebraMap_of_isAlgebraic [Algebra.IsAlgebraic κ κ'] (c : κ') :
    IsIntegral ↥(x1FunctionFieldC κ M) (algebraMap κ' ↥(x1FunctionFieldC κ' M) c) := by
  obtain ⟨P, hP0, hPc⟩ := Algebra.IsAlgebraic.isAlgebraic (R := κ) c
  have halg : IsAlgebraic ↥(x1FunctionFieldC κ M) (algebraMap κ' ↥(x1FunctionFieldC κ' M) c) := by
    refine ⟨P.map (algebraMap κ ↥(x1FunctionFieldC κ M)), ?_, ?_⟩
    · exact (Polynomial.map_ne_zero_iff (algebraMap κ ↥(x1FunctionFieldC κ M)).injective).mpr hP0
    · rw [Polynomial.aeval_def, Polynomial.eval₂_map, algebraMap_comp_algebraMap_eq κ κ' M hι,
        ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hPc, map_zero]
  exact halg.isIntegral

include hι in

theorem adjoin_range_algebraMap_eq_top [Algebra.IsAlgebraic κ κ'] :
    Algebra.adjoin ↥(x1FunctionFieldC κ M)
        (Set.range (algebraMap κ' ↥(x1FunctionFieldC κ' M))) = ⊤ := by
  classical

  have hSint : ∀ x ∈ Algebra.adjoin ↥(x1FunctionFieldC κ M) (Set.range (algebraMap κ' ↥(x1FunctionFieldC κ' M))),
      IsIntegral ↥(x1FunctionFieldC κ M) x := by
    intro x hx
    have hle : Algebra.adjoin ↥(x1FunctionFieldC κ M) (Set.range (algebraMap κ' ↥(x1FunctionFieldC κ' M))) ≤
        integralClosure ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC κ' M) := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨c, rfl⟩
      exact isIntegral_algebraMap_of_isAlgebraic κ κ' M hι c
    exact hle hx
  have hSinv : ∀ x ∈ Algebra.adjoin ↥(x1FunctionFieldC κ M) (Set.range (algebraMap κ' ↥(x1FunctionFieldC κ' M))),
      x⁻¹ ∈ Algebra.adjoin ↥(x1FunctionFieldC κ M) (Set.range (algebraMap κ' ↥(x1FunctionFieldC κ' M))) := by
    intro x hx
    have h := (hSint x hx).inv_mem_adjoin
    exact (Algebra.adjoin_le (Set.singleton_subset_iff.mpr hx) :
      Algebra.adjoin ↥(x1FunctionFieldC κ M) {x} ≤ _) h

  let SI : IntermediateField ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC κ' M) :=
    (Algebra.adjoin ↥(x1FunctionFieldC κ M) (Set.range (algebraMap κ' ↥(x1FunctionFieldC κ' M)))).toIntermediateField hSinv
  let T0 : Subfield (LaurentSeries κ') := SI.toSubfield.map (algebraMap ↥(x1FunctionFieldC κ' M) (LaurentSeries κ'))
  have hT0κ : ∀ c : κ', algebraMap κ' (LaurentSeries κ') c ∈ T0 := fun c =>
    ⟨algebraMap κ' ↥(x1FunctionFieldC κ' M) c, Algebra.subset_adjoin ⟨c, rfl⟩, rfl⟩
  let T : IntermediateField κ' (LaurentSeries κ') := T0.toIntermediateField hT0κ
  have hgenT : intFormRatiosC κ' (CongruenceSubgroup.Gamma1 M) ⊆ (T : Set (LaurentSeries κ')) := by
    intro x' hx'
    obtain ⟨x, hx, rfl⟩ := exists_coeffMap_eq_of_mem_intFormRatiosC κ κ' (CongruenceSubgroup.Gamma1 M) hx'
    have hxF : x ∈ x1FunctionFieldC κ M := intFormRatiosC_subset κ _ hx
    refine ⟨algebraMap ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC κ' M) ⟨x, hxF⟩, ?_, ?_⟩
    · exact Subalgebra.algebraMap_mem _ _
    · exact hι ⟨x, hxF⟩
  have hF'le : x1FunctionFieldC κ' M ≤ T := IntermediateField.adjoin_le_iff.mpr hgenT

  refine eq_top_iff.mpr fun y _ => ?_
  obtain ⟨s, hs, hsy⟩ := hF'le y.2
  have hsy' : s = y := Subtype.ext hsy
  rw [← hsy']
  exact hs

include hι in

theorem isIntegral_of_coe_algebraMap_eq_coeffMap [Algebra.IsAlgebraic κ κ'] :
    Algebra.IsIntegral ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC κ' M) := by
  refine ⟨fun y => ?_⟩
  have hy : y ∈ Algebra.adjoin ↥(x1FunctionFieldC κ M)
      (Set.range (algebraMap κ' ↥(x1FunctionFieldC κ' M))) := by
    rw [adjoin_range_algebraMap_eq_top κ κ' M hι]; trivial
  have hle : Algebra.adjoin ↥(x1FunctionFieldC κ M) (Set.range (algebraMap κ' ↥(x1FunctionFieldC κ' M))) ≤
      integralClosure ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC κ' M) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨c, rfl⟩
    exact isIntegral_algebraMap_of_isAlgebraic κ κ' M hι c
  exact hle hy

omit [Algebra κ κ'] [Algebra ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC κ' M)] in

theorem mem_range_algebraMap_of_isAlgebraic (y : ↥(x1FunctionFieldC κ M)) (hy : IsAlgebraic κ y) :
    y ∈ (algebraMap κ ↥(x1FunctionFieldC κ M)).range := by
  have hy' : IsAlgebraic κ (y : LaurentSeries κ) := IntermediateField.isAlgebraic_iff.mp hy
  obtain ⟨c, hc⟩ := LaurentSeries.exists_eq_C_of_isAlgebraic (y : LaurentSeries κ) hy'
  refine ⟨c, Subtype.ext ?_⟩
  rw [coe_algebraMap_x1FunctionFieldC, hc, HahnSeries.C_apply, algebraMap_laurentSeries_eq_single]

end ConstExt

section P6

variable (κ : Type*) [Field κ] (M : ℕ)

theorem transcendental_of_coe_eq_jqModC (J : ↥(x1FunctionFieldC κ M))
    (hJ : (J : LaurentSeries κ) = jqModC κ) : Transcendental κ J := by
  intro hJalg
  have hy' : IsAlgebraic κ (J : LaurentSeries κ) := IntermediateField.isAlgebraic_iff.mp hJalg
  obtain ⟨c, hc⟩ := LaurentSeries.exists_eq_C_of_isAlgebraic (J : LaurentSeries κ) hy'
  have h1 : (jqModC κ).coeff (-1 : ℤ) = 1 := coeff_jqModC_neg_one κ
  rw [← hJ, hc, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (by decide)] at h1
  exact zero_ne_one h1

theorem transcendental_coe_of_coe_eq_jqModC (J : ↥(x1FunctionFieldC κ M))
    (hJ : (J : LaurentSeries κ) = jqModC κ) : Transcendental κ (J : LaurentSeries κ) := fun h =>
  transcendental_of_coe_eq_jqModC κ M J hJ (IntermediateField.isAlgebraic_iff.mpr h)

end P6

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

theorem ord_coe_unit_mul_pow (v : Place k F) (u : (↥v.toValuationSubring)ˣ) {ϖ : ↥v.toValuationSubring}
    (hϖ : Irreducible ϖ) (n : ℕ) :
    v.ord (((u : ↥v.toValuationSubring) * ϖ ^ n : ↥v.toValuationSubring) : F) = n := by
  have := v.ord_unit_smul_zpow u hϖ (n : ℤ)
  rw [zpow_natCast] at this
  push_cast
  exact this

theorem ord_coe_eq_of_eq_unit_mul_pow (v : Place k F) {x : ↥v.toValuationSubring} {n : ℕ}
    {u : (↥v.toValuationSubring)ˣ} {ϖ : ↥v.toValuationSubring} (hϖ : Irreducible ϖ)
    (hx : x = u * ϖ ^ n) : v.ord (x : F) = n := by
  rw [hx]; exact ord_coe_unit_mul_pow v u hϖ n

theorem mem_toValuationSubring_iff_ord_nonneg (v : Place k F) {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥v.toValuationSubring
  constructor
  · intro hmem
    have hx0 : (⟨f, hmem⟩ : ↥v.toValuationSubring) ≠ 0 := fun h => hf (congrArg Subtype.val h)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    have := ord_coe_eq_of_eq_unit_mul_pow v hϖ hu
    simp only at this
    rw [this]; exact Int.natCast_nonneg n
  · intro h
    obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hϖ
    rw [hu]
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
    rw [hn, zpow_natCast]
    exact mul_mem (u : ↥v.toValuationSubring).2 (pow_mem ϖ.2 n)

theorem mem_nonunits_iff_one_le_ord (v : Place k F) {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring.nonunits ↔ 1 ≤ v.ord f := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥v.toValuationSubring
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  constructor
  · rintro ⟨hmem, hmax⟩
    have hx0 : (⟨f, hmem⟩ : ↥v.toValuationSubring) ≠ 0 := fun h => hf (congrArg Subtype.val h)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    have hord := ord_coe_eq_of_eq_unit_mul_pow v hϖ hu
    simp only at hord
    rw [hord]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso
      rw [pow_zero, mul_one] at hu
      exact (IsLocalRing.mem_maximalIdeal _ |>.mp hmax) (hu ▸ u.isUnit)
    · exact_mod_cast hn
  · intro h
    have h0 : 0 ≤ v.ord f := le_trans (by norm_num) h
    have hmem : f ∈ v.toValuationSubring := (mem_toValuationSubring_iff_ord_nonneg v hf).mpr h0
    refine ⟨hmem, ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have := v.ord_coe_unit hunit.unit
    simp only [IsUnit.unit_spec] at this
    rw [this] at h
    exact absurd h (by norm_num)

theorem span_singleton_eq_maximalIdeal_pow_iff_ord_eq (v : Place k F)
    (x : ↥v.toValuationSubring) (hx : x ≠ 0) (n : ℕ) :
    Ideal.span {x} = IsLocalRing.maximalIdeal ↥v.toValuationSubring ^ n ↔ v.ord (x : F) = n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥v.toValuationSubring
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  have hord : v.ord (x : F) = m := ord_coe_eq_of_eq_unit_mul_pow v hϖ hu
  have hmax : IsLocalRing.maximalIdeal ↥v.toValuationSubring = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hspan : Ideal.span ({x} : Set ↥v.toValuationSubring) = Ideal.span {ϖ ^ m} := by
    rw [hu, Ideal.span_singleton_eq_span_singleton]
    exact ⟨u⁻¹, by rw [mul_comm, ← mul_assoc, Units.inv_mul, one_mul]⟩
  rw [hord, hmax, Ideal.span_singleton_pow, hspan, Ideal.span_singleton_eq_span_singleton, Nat.cast_inj]
  constructor
  · rintro ⟨w, hw⟩

    have := IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ w 1 m n (by rw [Units.val_one, one_mul, ← hw, mul_comm])
    exact this
  · rintro rfl; exact Associated.refl _

theorem ord_prod_sub_algebraMap (W : Place k F) (J' : F) (hJ'W : J' ∈ W.toValuationSubring)
    (S : Finset k) (hne : ∀ β ∈ S, J' ≠ algebraMap k F β) :
    W.ord (∏ β ∈ S, (J' - algebraMap k F β)) = ∑ β ∈ S, W.ord (J' - algebraMap k F β) ∧
    (∀ β ∈ S, 0 ≤ W.ord (J' - algebraMap k F β)) ∧
    (∀ β₀ ∈ S, ∀ β₁ ∈ S, 1 ≤ W.ord (J' - algebraMap k F β₀) → 1 ≤ W.ord (J' - algebraMap k F β₁) → β₀ = β₁) := by
  classical
  have hne0 : ∀ β ∈ S, J' - algebraMap k F β ≠ 0 := fun β hβ h => hne β hβ (sub_eq_zero.mp h)
  have hmem : ∀ β : k, J' - algebraMap k F β ∈ W.toValuationSubring := fun β =>
    sub_mem hJ'W (W.algebraMap_mem' β)
  refine ⟨?_, fun β hβ => (mem_toValuationSubring_iff_ord_nonneg W (hne0 β hβ)).mp (hmem β), ?_⟩
  ·
    induction S using Finset.induction_on with
    | empty => simp [Place.ord_one]
    | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        W.ord_mul (hne0 a (Finset.mem_insert_self a S))
          (Finset.prod_ne_zero_iff.mpr (fun β hβ => hne0 β (Finset.mem_insert_of_mem hβ))),
        ih (fun β hβ => hne β (Finset.mem_insert_of_mem hβ)) (fun β hβ => hne0 β (Finset.mem_insert_of_mem hβ))]
  · intro β₀ hβ₀ β₁ hβ₁ h₀ h₁
    by_contra hb
    have hc0 : algebraMap k F (β₁ - β₀) ≠ 0 := by
      rw [map_ne_zero_iff _ (algebraMap k F).injective, sub_ne_zero]
      exact Ne.symm hb

    have hdiff : (J' - algebraMap k F β₀) - (J' - algebraMap k F β₁) = algebraMap k F (β₁ - β₀) := by
      rw [map_sub]; ring
    have hnu₀ := (mem_nonunits_iff_one_le_ord W (hne0 β₀ hβ₀)).mpr h₀
    have hnu₁ := (mem_nonunits_iff_one_le_ord W (hne0 β₁ hβ₁)).mpr h₁
    have hnu : algebraMap k F (β₁ - β₀) ∈ W.toValuationSubring.nonunits := by
      rw [← hdiff]
      exact sub_mem hnu₀ hnu₁
    have h1 : 1 ≤ W.ord (algebraMap k F (β₁ - β₀)) := (mem_nonunits_iff_one_le_ord W hc0).mp hnu
    rw [W.ord_algebraMap] at h1
    exact absurd h1 (by norm_num)

theorem exists_unique_ord_sub_algebraMap_pos (W : Place k F) (J' : F) (hJ'W : J' ∈ W.toValuationSubring)
    (S : Finset k) (hne : ∀ β ∈ S, J' ≠ algebraMap k F β) {n : ℤ} (hn : 1 ≤ n)
    (hprod : W.ord (∏ β ∈ S, (J' - algebraMap k F β)) = n) :
    ∃ β₀ ∈ S, W.ord (J' - algebraMap k F β₀) = n ∧
      ∀ β ∈ S, β ≠ β₀ → W.ord (J' - algebraMap k F β) = 0 := by
  classical
  obtain ⟨hsum, hnn, huniq⟩ := ord_prod_sub_algebraMap W J' hJ'W S hne
  rw [hsum] at hprod

  have hex : ∃ β₀ ∈ S, 1 ≤ W.ord (J' - algebraMap k F β₀) := by
    by_contra hno
    push_neg at hno
    have : ∑ β ∈ S, W.ord (J' - algebraMap k F β) ≤ 0 := by
      apply Finset.sum_nonpos
      intro β hβ
      have := hno β hβ
      omega
    omega
  obtain ⟨β₀, hβ₀, h₀⟩ := hex
  have hzero : ∀ β ∈ S, β ≠ β₀ → W.ord (J' - algebraMap k F β) = 0 := by
    intro β hβ hb
    have h := hnn β hβ
    by_contra hz
    have h1 : 1 ≤ W.ord (J' - algebraMap k F β) := by omega
    exact hb (huniq β hβ β₀ hβ₀ h1 h₀)
  refine ⟨β₀, hβ₀, ?_, hzero⟩
  rw [← hprod, ← Finset.add_sum_erase S _ hβ₀]
  have : ∑ β ∈ S.erase β₀, W.ord (J' - algebraMap k F β) = 0 :=
    Finset.sum_eq_zero (fun β hβ => hzero β (Finset.mem_of_mem_erase hβ) (Finset.ne_of_mem_erase hβ))
  rw [this, add_zero]

section OrdHelpers

variable {K : Type*} [Field K] {F' : Type*} [Field F'] [Algebra K F']

theorem Place.ord_nonneg_of_mem (v : Place K F') {f : F'} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  by_cases h0 : f = 0
  · rw [h0, Place.ord_zero]
  · exact (mem_toValuationSubring_iff_ord_nonneg v h0).mp hf

theorem Place.ord_eq_of_span_eq_pow (v : Place K F') {f : ↥v.toValuationSubring} {n : ℕ}
    (h : Ideal.span {f} = IsLocalRing.maximalIdeal ↥v.toValuationSubring ^ n) : v.ord (f : F') = n := by
  have hf : f ≠ 0 := by
    intro hf
    rw [hf, Ideal.span_singleton_zero] at h
    exact (pow_ne_zero n (IsDiscreteValuationRing.not_a_field ↥v.toValuationSubring)) h.symm
  exact (span_singleton_eq_maximalIdeal_pow_iff_ord_eq v f hf n).mp h

theorem Place.mem_maximalIdeal_of_ord_pos (v : Place K F') {f : ↥v.toValuationSubring}
    (h : 0 < v.ord (f : F')) : f ∈ IsLocalRing.maximalIdeal ↥v.toValuationSubring := by
  have hf : (f : F') ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h; exact lt_irrefl _ h
  have := (mem_nonunits_iff_one_le_ord v hf).mpr h
  exact (ValuationSubring.coe_mem_nonunits_iff).mp this

theorem Place.ord_eq_zero_of_isUnit (v : Place K F') {f : ↥v.toValuationSubring} (hu : IsUnit f) :
    v.ord (f : F') = 0 := by
  have := v.ord_coe_unit hu.unit
  simpa only [IsUnit.unit_spec] using this

theorem Place.ord_multiset_prod_sub_algebraMap (W : Place K F') (J' : F') (hJ'W : J' ∈ W.toValuationSubring)
    (hJ' : ∀ β : K, J' ≠ algebraMap K F' β) (S : Multiset K) (hS : S.Nodup) :
    (S.map fun β => W.ord (J' - algebraMap K F' β)).sum = W.ord ((S.map fun β => J' - algebraMap K F' β).prod) ∧
    (∀ β : K, 0 ≤ W.ord (J' - algebraMap K F' β)) ∧
    (∀ β₀ ∈ S, 0 < W.ord (J' - algebraMap K F' β₀) → ∀ β ∈ S, β ≠ β₀ → W.ord (J' - algebraMap K F' β) = 0) := by
  classical
  obtain ⟨hsum, hnn, huniq⟩ := ord_prod_sub_algebraMap W J' hJ'W S.toFinset (fun β _ => hJ' β)
  have hS' : S.toFinset.val = S := Multiset.toFinset_val _ |>.trans (Multiset.dedup_eq_self.mpr hS)
  refine ⟨?_, fun β => Place.ord_nonneg_of_mem W (sub_mem hJ'W (W.algebraMap_mem' β)), ?_⟩
  · have h1 : (S.map fun β => W.ord (J' - algebraMap K F' β)).sum = ∑ β ∈ S.toFinset, W.ord (J' - algebraMap K F' β) := by
      rw [Finset.sum_eq_multiset_sum, hS']
    have h2 : (S.map fun β => J' - algebraMap K F' β).prod = ∏ β ∈ S.toFinset, (J' - algebraMap K F' β) := by
      rw [Finset.prod_eq_multiset_prod, hS']
    rw [h1, h2, hsum]
  · intro β₀ hβ₀ h₀ β hβ hb
    have h := hnn β (Multiset.mem_toFinset.mpr hβ)
    by_contra hz
    have h1 : 1 ≤ W.ord (J' - algebraMap K F' β) := by omega
    exact hb (huniq β (Multiset.mem_toFinset.mpr hβ) β₀ (Multiset.mem_toFinset.mpr hβ₀) h1 (by omega))

end OrdHelpers

section Transport

variable {F F' : Type*} [Field F] [Field F'] (θ : F ≃+* F') (P : ValuationSubring F)

abbrev pushVS : ValuationSubring F' := P.comap θ.symm.toRingHom

theorem mem_pushVS_iff (y : F') : y ∈ pushVS θ P ↔ θ.symm y ∈ P := Iff.rfl

theorem apply_mem_pushVS_iff (x : F) : θ x ∈ pushVS θ P ↔ x ∈ P := by
  rw [mem_pushVS_iff]
  simp

def pushEquiv : ↥P ≃+* ↥(pushVS θ P) where
  toFun x := ⟨θ x, (apply_mem_pushVS_iff θ P x).mpr x.2⟩
  invFun y := ⟨θ.symm y, y.2⟩
  left_inv x := Subtype.ext (θ.symm_apply_apply x)
  right_inv y := Subtype.ext (θ.apply_symm_apply y)
  map_mul' a b := Subtype.ext (map_mul θ (a : F) (b : F))
  map_add' a b := Subtype.ext (map_add θ (a : F) (b : F))

@[scoped simp] theorem coe_pushEquiv (x : ↥P) : ((pushEquiv θ P x : ↥(pushVS θ P)) : F') = θ x := rfl

theorem pushVS_ne_top (h : P ≠ ⊤) : pushVS θ P ≠ ⊤ := by
  intro htop
  apply h
  refine eq_top_iff.mpr fun x _ => ?_
  have : θ x ∈ pushVS θ P := by rw [htop]; trivial
  exact (apply_mem_pushVS_iff θ P x).mp this

theorem isPrincipalIdealRing_pushVS (h : IsPrincipalIdealRing ↥P) : IsPrincipalIdealRing ↥(pushVS θ P) :=
  IsPrincipalIdealRing.of_surjective (pushEquiv θ P).toRingHom (pushEquiv θ P).surjective

def pushResidueEquiv : IsLocalRing.ResidueField ↥P ≃+* IsLocalRing.ResidueField ↥(pushVS θ P) :=
  IsLocalRing.ResidueField.mapEquiv (pushEquiv θ P)

theorem pushResidueEquiv_residue (x : ↥P) :
    pushResidueEquiv θ P (IsLocalRing.residue ↥P x) = IsLocalRing.residue ↥(pushVS θ P) (pushEquiv θ P x) := rfl

theorem finite_residueField_iff :
    Finite (IsLocalRing.ResidueField ↥(pushVS θ P)) ↔ Finite (IsLocalRing.ResidueField ↥P) :=
  ⟨fun _ => Finite.of_equiv _ (pushResidueEquiv θ P).symm.toEquiv,
   fun _ => Finite.of_equiv _ (pushResidueEquiv θ P).toEquiv⟩

theorem map_maximalIdeal_ringEquiv {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) : Ideal.map (e : R →+* S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S := by
  haveI : (Ideal.map (e : R →+* S) (IsLocalRing.maximalIdeal R)).IsMaximal := Ideal.map_isMaximal_of_equiv e
  exact IsLocalRing.eq_maximalIdeal inferInstance

end Transport

theorem transcendental_of_coe_eq_jqModC' (κ : Type*) [Field κ] (M : ℕ) (J : ↥(x1FunctionFieldC κ M))
    (hJ : (J : LaurentSeries κ) = jqModC κ) : Transcendental κ J := by
  intro hJalg
  have hy' : IsAlgebraic κ (J : LaurentSeries κ) := IntermediateField.isAlgebraic_iff.mp hJalg
  obtain ⟨c, hc⟩ := LaurentSeries.exists_eq_C_of_isAlgebraic (J : LaurentSeries κ) hy'
  have h1 : (jqModC κ).coeff (-1 : ℤ) = 1 := coeff_jqModC_neg_one κ
  rw [← hJ, hc, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (by decide)] at h1
  exact zero_ne_one h1

namespace Sep

section

variable (κ : Type) [Field κ] (M : ℕ)

def ι : ↥(x1FunctionFieldC κ M) →+* ↥(x1FunctionFieldC (AlgebraicClosure κ) M) :=
  (ModularCurve.exists_ringHom_qExpFunctionFieldC_coe_eq_coeffMap (algebraMap κ (AlgebraicClosure κ))
    (CongruenceSubgroup.Gamma1 M)).choose

theorem coe_ι (f : ↥(x1FunctionFieldC κ M)) :
    ((ι κ M f : ↥(x1FunctionFieldC (AlgebraicClosure κ) M)) : LaurentSeries (AlgebraicClosure κ)) =
      coeffMap (algebraMap κ (AlgebraicClosure κ)) (f : LaurentSeries κ) :=
  (ModularCurve.exists_ringHom_qExpFunctionFieldC_coe_eq_coeffMap (algebraMap κ (AlgebraicClosure κ))
    (CongruenceSubgroup.Gamma1 M)).choose_spec f

theorem ι_algebraMap (c : κ) :
    ι κ M (algebraMap κ ↥(x1FunctionFieldC κ M) c) =
      algebraMap (AlgebraicClosure κ) ↥(x1FunctionFieldC (AlgebraicClosure κ) M) (algebraMap κ (AlgebraicClosure κ) c) := by
  apply Subtype.ext
  rw [coe_ι]
  show coeffMap (algebraMap κ (AlgebraicClosure κ)) (algebraMap κ (LaurentSeries κ) c) =
    algebraMap (AlgebraicClosure κ) (LaurentSeries (AlgebraicClosure κ)) (algebraMap κ (AlgebraicClosure κ) c)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem transcendental_coe (J : ↥(x1FunctionFieldC κ M)) (hJ : (J : LaurentSeries κ) = jqModC κ) :
    Transcendental κ (J : LaurentSeries κ) := by
  intro hJalg
  obtain ⟨c, hc⟩ := LaurentSeries.exists_eq_C_of_isAlgebraic (J : LaurentSeries κ) hJalg
  have h1 : (jqModC κ).coeff (-1 : ℤ) = 1 := coeff_jqModC_neg_one κ
  rw [← hJ, hc, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (by decide)] at h1
  exact zero_ne_one h1

theorem transcendental (J : ↥(x1FunctionFieldC κ M)) (hJ : (J : LaurentSeries κ) = jqModC κ) :
    Transcendental κ J := fun h =>
  transcendental_coe κ M J hJ (IntermediateField.isAlgebraic_iff.mp h)

variable (p : ℕ) [Fact p.Prime] [CharP κ p] [NeZero M]

theorem charP_algClosure : CharP (AlgebraicClosure κ) p :=
  charP_of_injective_algebraMap (algebraMap κ (AlgebraicClosure κ)).injective p

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem finiteDimensional_and_isSeparable_adjoin [PerfectField κ] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (J : ↥(x1FunctionFieldC κ M)) (hJ : (J : LaurentSeries κ) = jqModC κ) :
    FiniteDimensional ↥κ⟮J⟯ ↥(x1FunctionFieldC κ M) ∧ Algebra.IsSeparable ↥κ⟮J⟯ ↥(x1FunctionFieldC κ M) := by
  classical
  haveI : CharP (AlgebraicClosure κ) p := charP_algClosure κ p
  obtain ⟨t, ht, -, hfin, hsep⟩ :=
    ModularCurve.exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC
      p M hM hpM (AlgebraicClosure κ)

  have hx : ((t : ↥(x1FunctionFieldC (AlgebraicClosure κ) M)) : LaurentSeries (AlgebraicClosure κ)) =
      coeffMap (algebraMap κ (AlgebraicClosure κ)) (J : LaurentSeries κ) := by
    rw [ht, hJ]; exact (map_jqModC (algebraMap κ (AlgebraicClosure κ))).symm
  haveI : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure κ)
        ({t} : Set ↥(qExpFunctionFieldC (AlgebraicClosure κ) (CongruenceSubgroup.Gamma1 M))))
      ↥(qExpFunctionFieldC (AlgebraicClosure κ) (CongruenceSubgroup.Gamma1 M)) := hfin
  have hfinκ : FiniteDimensional ↥κ⟮J⟯ ↥(x1FunctionFieldC κ M) :=
    (ModularCurve.finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
      (algebraMap κ (AlgebraicClosure κ)) (CongruenceSubgroup.Gamma1 M) J t (transcendental_coe κ M J hJ) hx).1
  refine ⟨hfinκ, ?_⟩

  have hιJ : ι κ M J = t := Subtype.ext (by rw [coe_ι, ← hx])
  letI algFF' : Algebra ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC (AlgebraicClosure κ) M) := (ι κ M).toAlgebra
  letI algEF' : Algebra ↥κ⟮J⟯ ↥(x1FunctionFieldC (AlgebraicClosure κ) M) :=
    ((algebraMap ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC (AlgebraicClosure κ) M)).comp
      (algebraMap ↥κ⟮J⟯ ↥(x1FunctionFieldC κ M))).toAlgebra
  haveI towEFF' : IsScalarTower ↥κ⟮J⟯ ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC (AlgebraicClosure κ) M) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl

  have hsq : (algebraMap ↥κ⟮J⟯ ↥(x1FunctionFieldC (AlgebraicClosure κ) M)).comp (algebraMap κ ↥κ⟮J⟯) =
      (algebraMap (AlgebraicClosure κ) ↥(x1FunctionFieldC (AlgebraicClosure κ) M)).comp
        (algebraMap κ (AlgebraicClosure κ)) := by
    refine RingHom.ext fun c => ?_
    show ι κ M (algebraMap ↥κ⟮J⟯ ↥(x1FunctionFieldC κ M) (algebraMap κ ↥κ⟮J⟯ c)) =
      algebraMap (AlgebraicClosure κ) ↥(x1FunctionFieldC (AlgebraicClosure κ) M) (algebraMap κ (AlgebraicClosure κ) c)
    rw [← IsScalarTower.algebraMap_apply κ ↥κ⟮J⟯ ↥(x1FunctionFieldC κ M), ι_algebraMap]

  haveI : Algebra.IsSeparable κ (AlgebraicClosure κ) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI hTsep : Algebra.IsSeparable ↥κ⟮J⟯
      ↥(IntermediateField.adjoin ↥κ⟮J⟯
        (Set.range (algebraMap (AlgebraicClosure κ) ↥(x1FunctionFieldC (AlgebraicClosure κ) M)))) := by
    refine (IntermediateField.isSeparable_adjoin_iff_isSeparable _ _).mpr ?_
    rintro _ ⟨c, rfl⟩

    have h0 : (minpoly κ c).Separable := Algebra.IsSeparable.isSeparable κ c
    have hPsep : ((minpoly κ c).map (algebraMap κ ↥κ⟮J⟯)).Separable := h0.map
    have hroot : Polynomial.aeval (algebraMap (AlgebraicClosure κ) ↥(x1FunctionFieldC (AlgebraicClosure κ) M) c)
        ((minpoly κ c).map (algebraMap κ ↥κ⟮J⟯)) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, hsq, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def,
        minpoly.aeval, map_zero]
    exact hPsep.of_dvd (minpoly.dvd _ _ hroot)

  have hle : (IntermediateField.adjoin (AlgebraicClosure κ) ({t} : Set ↥(x1FunctionFieldC (AlgebraicClosure κ) M))).toSubfield ≤
      (IntermediateField.adjoin ↥κ⟮J⟯
        (Set.range (algebraMap (AlgebraicClosure κ) ↥(x1FunctionFieldC (AlgebraicClosure κ) M)))).toSubfield := by
    rw [IntermediateField.adjoin_toSubfield]
    refine Subfield.closure_le.mpr ?_
    rintro z (⟨c, rfl⟩ | hz)
    · exact IntermediateField.subset_adjoin _ _ ⟨c, rfl⟩
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      have : (t : ↥(x1FunctionFieldC (AlgebraicClosure κ) M)) =
          algebraMap ↥κ⟮J⟯ ↥(x1FunctionFieldC (AlgebraicClosure κ) M) (IntermediateField.AdjoinSimple.gen κ J) := by
        rw [← hιJ]; rfl
      rw [this]
      exact IntermediateField.algebraMap_mem _ _
  letI algE'T : Algebra
      ↥(IntermediateField.adjoin (AlgebraicClosure κ) ({t} : Set ↥(x1FunctionFieldC (AlgebraicClosure κ) M)))
      ↥(IntermediateField.adjoin ↥κ⟮J⟯
        (Set.range (algebraMap (AlgebraicClosure κ) ↥(x1FunctionFieldC (AlgebraicClosure κ) M)))) :=
    (Subfield.inclusion hle).toAlgebra
  haveI : IsScalarTower
      ↥(IntermediateField.adjoin (AlgebraicClosure κ) ({t} : Set ↥(x1FunctionFieldC (AlgebraicClosure κ) M)))
      ↥(IntermediateField.adjoin ↥κ⟮J⟯
        (Set.range (algebraMap (AlgebraicClosure κ) ↥(x1FunctionFieldC (AlgebraicClosure κ) M))))
      ↥(x1FunctionFieldC (AlgebraicClosure κ) M) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl

  haveI := hsep
  refine ⟨fun α => ?_⟩
  have hβ : IsSeparable
      ↥(IntermediateField.adjoin (AlgebraicClosure κ) ({t} : Set ↥(x1FunctionFieldC (AlgebraicClosure κ) M)))
      (algebraMap ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC (AlgebraicClosure κ) M) α) :=
    Algebra.IsSeparable.isSeparable _ _
  have hβT : IsSeparable
      ↥(IntermediateField.adjoin ↥κ⟮J⟯
        (Set.range (algebraMap (AlgebraicClosure κ) ↥(x1FunctionFieldC (AlgebraicClosure κ) M))))
      (algebraMap ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC (AlgebraicClosure κ) M) α) :=
    IsSeparable.tower_top _ hβ
  have hβE : IsSeparable ↥κ⟮J⟯
      (algebraMap ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC (AlgebraicClosure κ) M) α) :=
    @IsSeparable.of_algebra_isSeparable_of_isSeparable ↥κ⟮J⟯
      ↥(IntermediateField.adjoin ↥κ⟮J⟯
        (Set.range (algebraMap (AlgebraicClosure κ) ↥(x1FunctionFieldC (AlgebraicClosure κ) M))))
      _ _ _ ↥(x1FunctionFieldC (AlgebraicClosure κ) M) _ _ _
      (IsScalarTower.of_algebraMap_eq fun _ => rfl) hTsep _ hβT

  let ιE : ↥(x1FunctionFieldC κ M) →ₐ[↥κ⟮J⟯] ↥(x1FunctionFieldC (AlgebraicClosure κ) M) :=
    { ι κ M with commutes' := fun _ => rfl }
  have hmin := minpoly.algHom_eq ιE (ι κ M).injective α
  unfold IsSeparable at hβE ⊢
  have hco : (algebraMap ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC (AlgebraicClosure κ) M) α) = ιE α := rfl
  rw [hco, hmin] at hβE
  exact hβE

set_option synthInstance.maxHeartbeats 1600000 in

theorem isCurveOver_x1FunctionFieldC [PerfectField κ] (hM : 5 ≤ M) (hpM : ¬ p ∣ M) :
    AlgebraicCurve.IsCurveOver κ ↥(x1FunctionFieldC κ M) := by
  let J : ↥(x1FunctionFieldC κ M) := ⟨jqModC κ,
    intFormRatiosC_subset κ _ (jqModC_mem_intFormRatiosC κ (CongruenceSubgroup.Gamma1 M))⟩
  have hJ : (J : LaurentSeries κ) = jqModC κ := rfl
  obtain ⟨hfin, hsep⟩ := finiteDimensional_and_isSeparable_adjoin κ M p hM hpM J hJ
  exact AlgebraicCurve.isCurveOver_of_transcendental (transcendental κ M J hJ) hfin hsep

end

set_option synthInstance.maxHeartbeats 1600000 in

theorem finite_residueField_of_valuationSubring_x1FunctionFieldC
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (κ : Type) [Field κ] [CharP κ p] [Finite κ]
    (P : ValuationSubring ↥(x1FunctionFieldC κ M))
    (hPκ : ∀ a : κ, algebraMap κ ↥(x1FunctionFieldC κ M) a ∈ P) (hPtop : P ≠ ⊤)
    (hPpir : IsPrincipalIdealRing ↥P) :
    Finite (IsLocalRing.ResidueField ↥P) := by
  haveI : PerfectField κ := PerfectField.ofFinite
  haveI := isCurveOver_x1FunctionFieldC κ M p hM hpM
  obtain ⟨v, hv⟩ : ∃ v : AlgebraicCurve.Place κ ↥(x1FunctionFieldC κ M), v.toValuationSubring = P :=
    ⟨⟨P, hPκ, hPtop, hPpir⟩, rfl⟩
  subst hv
  have hmf : Module.Finite κ v.ResidueField := AlgebraicCurve.IsCurveOver.finite_residueField v
  have hf : Finite v.ResidueField := Module.finite_of_finite κ
  exact hf

end Sep

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem span_aeval_minpoly_eq_pow_le_three_x1
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (κ : Type) [Field κ] [CharP κ p] [DecidableEq κ] [Finite κ]
    (J : ↥(x1FunctionFieldC κ M)) (hJ : (J : LaurentSeries κ) = jqModC κ)
    (hJt : Transcendental κ J)
    (P : ValuationSubring ↥(x1FunctionFieldC κ M))
    (hPκ : ∀ a : κ, algebraMap κ ↥(x1FunctionFieldC κ M) a ∈ P) (hPtop : P ≠ ⊤)
    (hPpir : IsPrincipalIdealRing ↥P) (hJP : J ∈ P)
    (halg : letI : Algebra κ ↥P := ((algebraMap κ ↥(x1FunctionFieldC κ M)).codRestrict P.toSubring hPκ).toAlgebra
      IsAlgebraic κ (IsLocalRing.residue ↥P ⟨J, hJP⟩)) :
    letI : Algebra κ ↥P := ((algebraMap κ ↥(x1FunctionFieldC κ M)).codRestrict P.toSubring hPκ).toAlgebra
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 3 ∧
      Ideal.span {Polynomial.aeval (⟨J, hJP⟩ : ↥P) (minpoly κ (IsLocalRing.residue ↥P ⟨J, hJP⟩))}
        = IsLocalRing.maximalIdeal ↥P ^ n := by
  classical
  letI algκP : Algebra κ ↥P := ((algebraMap κ ↥(x1FunctionFieldC κ M)).codRestrict P.toSubring hPκ).toAlgebra
  haveI : IsScalarTower κ ↥P ↥(x1FunctionFieldC κ M) := IsScalarTower.of_algebraMap_eq (fun a => rfl)

  let Pl : AlgebraicCurve.Place κ ↥(x1FunctionFieldC κ M) := ⟨P, hPκ, hPtop, hPpir⟩
  haveI : IsPrincipalIdealRing ↥P := hPpir
  haveI : IsDiscreteValuationRing ↥P :=
    { toIsPrincipalIdealRing := hPpir
      toIsLocalRing := inferInstance
      not_a_field' := by
        rw [ne_eq, ← IsLocalRing.isField_iff_maximalIdeal_eq]
        exact ValuationSubring.not_isField_of_ne_top _ hPtop }
  set j₀ := IsLocalRing.residue ↥P ⟨J, hJP⟩ with hj₀
  set m : Polynomial κ := minpoly κ j₀ with hm
  set xP : ↥P := Polynomial.aeval (⟨J, hJP⟩ : ↥P) m with hxP
  have hm0 : m ≠ 0 := minpoly.ne_zero halg.isIntegral
  have hmmonic : m.Monic := minpoly.monic halg.isIntegral

  have hxmax : xP ∈ IsLocalRing.maximalIdeal ↥P := by
    rw [← IsLocalRing.residue_eq_zero_iff, hxP]
    show Ideal.Quotient.mkₐ κ (IsLocalRing.maximalIdeal ↥P) (Polynomial.aeval (⟨J, hJP⟩ : ↥P) m) = 0
    rw [← Polynomial.aeval_algHom_apply]
    exact minpoly.aeval κ j₀

  have hx0 : xP ≠ 0 := by
    intro h0
    apply hJt
    refine ⟨m, hm0, ?_⟩
    have : ((xP : ↥P) : ↥(x1FunctionFieldC κ M)) = Polynomial.aeval J m := by
      rw [hxP]; exact (Polynomial.aeval_algebraMap_apply ↥(x1FunctionFieldC κ M) (⟨J, hJP⟩ : ↥P) m).symm
    rw [← this, h0]; rfl

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥P
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (show Ideal.span {xP} ≠ ⊥ by simpa [Ideal.span_singleton_eq_bot] using hx0) hϖ
  have hmaxeq : IsLocalRing.maximalIdeal ↥P = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hspan : Ideal.span {xP} = IsLocalRing.maximalIdeal ↥P ^ n := by
    rw [hn, hmaxeq, Ideal.span_singleton_pow]
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso
      rw [h0, pow_zero, Ideal.one_eq_top, Ideal.span_singleton_eq_top] at hspan
      exact (IsLocalRing.mem_maximalIdeal _).1 hxmax hspan
    · exact hpos

  have hord : Pl.ord (xP : ↥(x1FunctionFieldC κ M)) = n := Place.ord_eq_of_span_eq_pow Pl hspan
  refine ⟨n, hn1, ?_, hspan⟩

  let κ' : Type := AlgebraicClosure κ
  let F' : Type := ↥(x1FunctionFieldC κ' M)
  letI : Algebra ↥(x1FunctionFieldC κ M) F' := constExtAlgebra κ κ' M
  letI algκF' : Algebra κ F' := ((algebraMap κ' F').comp (algebraMap κ κ')).toAlgebra
  haveI : IsScalarTower κ κ' F' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower κ ↥(x1FunctionFieldC κ M) F' :=
    isScalarTower_of_coe_algebraMap_eq_coeffMap κ κ' M (coe_constExt κ κ' M)
  haveI : Algebra.IsIntegral ↥(x1FunctionFieldC κ M) F' :=
    isIntegral_of_coe_algebraMap_eq_coeffMap κ κ' M (coe_constExt κ κ' M)
  have hgen := adjoin_range_algebraMap_eq_top κ κ' M (coe_constExt κ κ' M)
  have hconst : ∀ y : ↥(x1FunctionFieldC κ M), IsAlgebraic κ y → y ∈ (algebraMap κ ↥(x1FunctionFieldC κ M)).range :=
    fun y hy => mem_range_algebraMap_of_isAlgebraic κ M y hy
  haveI : PerfectField κ := PerfectField.ofFinite
  haveI : Algebra.IsSeparable κ κ' := Algebra.IsAlgebraic.isSeparable_of_perfectField

  obtain ⟨W, hW⟩ :=
    AlgebraicCurve.Place.exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
      (K := κ) (K' := κ') (F := ↥(x1FunctionFieldC κ M)) (F' := F') hgen hconst (M := ↥(x1FunctionFieldC κ M)) Pl
  have hWcomap : W.toValuationSubring.comap (algebraMap ↥(x1FunctionFieldC κ M) F') = Pl.toValuationSubring := by
    rw [← hW]; rfl
  have hordW : ∀ f : ↥(x1FunctionFieldC κ M), W.ord (algebraMap _ F' f) = Pl.ord f :=
    AlgebraicCurve.Place.ord_algebraMap_eq_ord_of_comap_eq_of_isSeparable_of_adjoin_eq_top hgen Pl W hWcomap

  set J' : F' := algebraMap ↥(x1FunctionFieldC κ M) F' J with hJ'def
  have hJ'coe : ((J' : F') : LaurentSeries κ') = jqModC κ' := by
    rw [hJ'def]
    show ((constExt κ κ' M J : F') : LaurentSeries κ') = _
    rw [coe_constExt, hJ]; exact map_jqModC (algebraMap κ κ')
  have hJ'W : J' ∈ W.toValuationSubring := by
    have : J ∈ Pl.toValuationSubring := hJP
    rw [← hWcomap, ValuationSubring.mem_comap] at this; exact this
  have hordJ' : 0 ≤ W.ord J' := Place.ord_nonneg_of_mem W hJ'W

  have hm'split : (m.map (algebraMap κ κ')).Splits := IsAlgClosed.splits _
  have hm'monic : (m.map (algebraMap κ κ')).Monic := hmmonic.map _
  have hmirr : Irreducible m := minpoly.irreducible halg.isIntegral
  have hm'sep : (m.map (algebraMap κ κ')).Separable := (PerfectField.separable_of_irreducible hmirr).map
  have hnodup : (m.map (algebraMap κ κ')).roots.Nodup := Polynomial.nodup_roots hm'sep
  set S : Multiset κ' := (m.map (algebraMap κ κ')).roots with hSdef
  have hprod : m.map (algebraMap κ κ') = (S.map fun a => Polynomial.X - Polynomial.C a).prod := by
    first
      | exact Polynomial.Splits.eq_prod_roots_of_monic hm'monic hm'split
      | exact Polynomial.Splits.eq_prod_roots_of_monic hm'split hm'monic
      | exact hm'split.eq_prod_roots_of_monic hm'monic
      | (conv_lhs => rw [Polynomial.Splits.eq_prod_roots hm'split]); simp [hm'monic.leadingCoeff]
  have hximg : algebraMap ↥(x1FunctionFieldC κ M) F' (xP : ↥(x1FunctionFieldC κ M))
      = (S.map fun β => J' - algebraMap κ' F' β).prod := by
    have hx' : ((xP : ↥P) : ↥(x1FunctionFieldC κ M)) = Polynomial.aeval J m := by
      rw [hxP]; exact (Polynomial.aeval_algebraMap_apply ↥(x1FunctionFieldC κ M) (⟨J, hJP⟩ : ↥P) m).symm
    rw [hx', ← Polynomial.aeval_algebraMap_apply F' J m, ← hJ'def, ← Polynomial.aeval_map_algebraMap κ' J' m,
      hprod, map_multiset_prod, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun β _ => ?_
    simp

  have hfac_mem : ∀ β : κ', J' - algebraMap κ' F' β ∈ W.toValuationSubring :=
    fun β => sub_mem hJ'W (W.algebraMap_mem' β)
  have hfac_nonneg : ∀ β : κ', 0 ≤ W.ord (J' - algebraMap κ' F' β) :=
    fun β => Place.ord_nonneg_of_mem W (hfac_mem β)
  have hJ'trans : Transcendental κ' J' := by
    have := transcendental_of_coe_eq_jqModC κ' M ⟨J', J'.2⟩ hJ'coe
    simpa using this
  have hfac_ne : ∀ β : κ', J' - algebraMap κ' F' β ≠ 0 := by
    intro β h
    apply hJ'trans
    rw [sub_eq_zero] at h
    rw [h]; exact isAlgebraic_algebraMap β

  obtain ⟨hsum', hnn, huniq⟩ := Place.ord_multiset_prod_sub_algebraMap W J' hJ'W
    (fun β h => hfac_ne β (sub_eq_zero.2 h)) S hnodup
  have hsum : (S.map fun β => W.ord (J' - algebraMap κ' F' β)).sum = n := by
    rw [hsum', ← hximg, hordW, hord]

  obtain ⟨β₀, hβ₀S, hβ₀pos⟩ : ∃ β₀ ∈ S, 0 < W.ord (J' - algebraMap κ' F' β₀) := by
    by_contra h
    push_neg at h
    have : (S.map fun β => W.ord (J' - algebraMap κ' F' β)).sum = 0 := by
      refine Multiset.sum_eq_zero fun x hx => ?_
      obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.1 hx
      exact le_antisymm (h β hβ) (hnn β)
    omega
  have hothers : ∀ β ∈ S, β ≠ β₀ → W.ord (J' - algebraMap κ' F' β) = 0 := huniq β₀ hβ₀S hβ₀pos

  have hn_eq : (n : ℤ) = W.ord (J' - algebraMap κ' F' β₀) := by
    rw [← hsum]
    have hS' : S = β₀ ::ₘ S.erase β₀ := (Multiset.cons_erase hβ₀S).symm
    rw [hS', Multiset.map_cons, Multiset.sum_cons]
    have : ((S.erase β₀).map fun β => W.ord (J' - algebraMap κ' F' β)).sum = 0 := by
      refine Multiset.sum_eq_zero fun x hx => ?_
      obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.1 hx
      have hβS : β ∈ S := Multiset.mem_of_mem_erase hβ
      have hne : β ≠ β₀ := ((hnodup.mem_erase_iff).1 hβ).1
      exact hothers β hβS hne
    rw [this, add_zero]
  have hfine := ModularCurve.ord_sub_algebraMap_eq_jWidth_of_place_x1FunctionFieldC p hp5 κ' M hM hpM
    ⟨J', J'.2⟩ (by simpa using hJ'coe) W (by simpa using hordJ') β₀ (by first | exact hβ₀pos | simpa using hβ₀pos | exact Int.add_one_le_iff.mpr hβ₀pos)
  have h3 : (ModularCurve.jWidth β₀ : ℤ) ≤ 3 := by
    rcases ModularCurve.jWidth_eq_one_or β₀ with h | h | h <;> simp [h]
  have hfine' : W.ord (J' - algebraMap κ' F' β₀) = (ModularCurve.jWidth β₀ : ℤ) := by
    simpa using hfine
  have : (n : ℤ) ≤ 3 := by rw [hn_eq, hfine']; exact h3
  exact_mod_cast this

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem span_aeval_minpoly_eq_pow_le_three
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (κ : Type) [Field κ] [CharP κ p] [DecidableEq κ] [Finite κ]
    (F : Type) [Field F] [Algebra κ F]
    (θ : F ≃+* ↥(ModularCurve.x1FunctionFieldC κ M))
    (hθ : ∀ a : κ, θ (algebraMap κ F a) = algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) a)
    (J : F) (hJ : ((θ J : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ) = ModularCurve.jqModC κ)
    (P : ValuationSubring F) (hPκ : ∀ a : κ, algebraMap κ F a ∈ P) (hPtop : P ≠ ⊤)
    (hPpir : IsPrincipalIdealRing ↥P) (hJP : J ∈ P)
    (hfinres : Finite (IsLocalRing.ResidueField ↥P)) :
    letI : Algebra κ ↥P := ((algebraMap κ F).codRestrict P.toSubring hPκ).toAlgebra
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 3 ∧
      Ideal.span {Polynomial.aeval (⟨J, hJP⟩ : ↥P) (minpoly κ (IsLocalRing.residue ↥P ⟨J, hJP⟩))}
        = IsLocalRing.maximalIdeal ↥P ^ n := by
  classical
  letI algP : Algebra κ ↥P := ((algebraMap κ F).codRestrict P.toSubring hPκ).toAlgebra

  set J₀ : ↥(x1FunctionFieldC κ M) := θ J with hJ₀def
  have hPκ₀ : ∀ a : κ, algebraMap κ ↥(x1FunctionFieldC κ M) a ∈ pushVS θ P := fun a => by
    rw [← hθ, apply_mem_pushVS_iff]; exact hPκ a
  have hJP₀ : J₀ ∈ pushVS θ P := (apply_mem_pushVS_iff θ P J).mpr hJP
  letI algP₀ : Algebra κ ↥(pushVS θ P) :=
    ((algebraMap κ ↥(x1FunctionFieldC κ M)).codRestrict (pushVS θ P).toSubring hPκ₀).toAlgebra

  have hcompat : ∀ a : κ, pushEquiv θ P (algebraMap κ ↥P a) = algebraMap κ ↥(pushVS θ P) a :=
    fun a => Subtype.ext (hθ a)
  let eA : ↥P ≃ₐ[κ] ↥(pushVS θ P) := AlgEquiv.ofRingEquiv (f := pushEquiv θ P) hcompat
  have hres_compat : ∀ a : κ, pushResidueEquiv θ P (algebraMap κ (IsLocalRing.ResidueField ↥P) a) =
      algebraMap κ (IsLocalRing.ResidueField ↥(pushVS θ P)) a := by
    intro a
    show pushResidueEquiv θ P (IsLocalRing.residue ↥P (algebraMap κ ↥P a)) =
      IsLocalRing.residue ↥(pushVS θ P) (algebraMap κ ↥(pushVS θ P) a)
    rw [pushResidueEquiv_residue, hcompat]
  let eR : IsLocalRing.ResidueField ↥P ≃ₐ[κ] IsLocalRing.ResidueField ↥(pushVS θ P) :=
    AlgEquiv.ofRingEquiv (f := pushResidueEquiv θ P) hres_compat
  have hJJ : pushEquiv θ P ⟨J, hJP⟩ = ⟨J₀, hJP₀⟩ := Subtype.ext rfl
  have hresJ : eR (IsLocalRing.residue ↥P ⟨J, hJP⟩) = IsLocalRing.residue ↥(pushVS θ P) ⟨J₀, hJP₀⟩ := by
    show pushResidueEquiv θ P (IsLocalRing.residue ↥P ⟨J, hJP⟩) = _
    rw [pushResidueEquiv_residue, hJJ]

  haveI : Finite (IsLocalRing.ResidueField ↥(pushVS θ P)) := (finite_residueField_iff θ P).mpr hfinres
  haveI : Module.Finite κ (IsLocalRing.ResidueField ↥(pushVS θ P)) := Module.Finite.of_finite
  have halg₀ : IsAlgebraic κ (IsLocalRing.residue ↥(pushVS θ P) ⟨J₀, hJP₀⟩) :=
    Algebra.IsAlgebraic.isAlgebraic _

  obtain ⟨n, hn1, hn3, hspan₀⟩ :=
    span_aeval_minpoly_eq_pow_le_three_x1 p hp5 M hM hpM κ J₀ hJ
      (transcendental_of_coe_eq_jqModC' κ M J₀ hJ) (pushVS θ P) hPκ₀ (pushVS_ne_top θ P hPtop)
      (isPrincipalIdealRing_pushVS θ P hPpir) hJP₀ halg₀
  refine ⟨n, hn1, hn3, ?_⟩

  have hmin : minpoly κ (IsLocalRing.residue ↥(pushVS θ P) ⟨J₀, hJP₀⟩) =
      minpoly κ (IsLocalRing.residue ↥P ⟨J, hJP⟩) := by
    rw [← hresJ]; exact minpoly.algEquiv_eq eR _
  rw [hmin] at hspan₀

  have haeval : eA (Polynomial.aeval (⟨J, hJP⟩ : ↥P) (minpoly κ (IsLocalRing.residue ↥P ⟨J, hJP⟩))) =
      Polynomial.aeval (⟨J₀, hJP₀⟩ : ↥(pushVS θ P)) (minpoly κ (IsLocalRing.residue ↥P ⟨J, hJP⟩)) := by
    rw [← Polynomial.aeval_algHom_apply]
    congr 1

  have hmap := congrArg (Ideal.map ((pushEquiv θ P).symm : ↥(pushVS θ P) →+* ↥P)) hspan₀
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_pow, map_maximalIdeal_ringEquiv] at hmap
  have hx : ((pushEquiv θ P).symm : ↥(pushVS θ P) →+* ↥P)
      (Polynomial.aeval (⟨J₀, hJP₀⟩ : ↥(pushVS θ P)) (minpoly κ (IsLocalRing.residue ↥P ⟨J, hJP⟩))) =
      Polynomial.aeval (⟨J, hJP⟩ : ↥P) (minpoly κ (IsLocalRing.residue ↥P ⟨J, hJP⟩)) := by
    rw [← haeval]
    exact (pushEquiv θ P).symm_apply_apply _
  rw [hx] at hmap
  exact hmap

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem exists_card_placeInertia_eq_and_span_eq_pow_mul
    (F : Type) [Field F]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G F] [FaithfulSMul G F]
    (P : ValuationSubring F) (hPtop : P ≠ ⊤) (hPpir : IsPrincipalIdealRing ↥P)
    (hfin : Finite (IsLocalRing.ResidueField ↥P)) :
    ∃ e : ℕ, 0 < e ∧
      Nat.card {g : G // g • P = P ∧ ∀ x : ↥P, g • (x : F) - x ∈ P.nonunits} = e ∧
      ∀ (x : F) (hx : x ∈ P), x ≠ 0 → (∀ g : G, g • x = x) →
        ∃ k : ℕ, Ideal.span {(⟨x, hx⟩ : ↥P)} = IsLocalRing.maximalIdeal ↥P ^ (e * k) := by
  classical
  haveI : IsPrincipalIdealRing ↥P := hPpir
  haveI : IsDiscreteValuationRing ↥P :=
    { toIsPrincipalIdealRing := hPpir
      toIsLocalRing := inferInstance
      not_a_field' := by
        rw [ne_eq, ← IsLocalRing.isField_iff_maximalIdeal_eq]
        exact ValuationSubring.not_isField_of_ne_top F hPtop }

  obtain ⟨instGS, 𝔓, hGSF, hRdvr, hRded, hRfrac, hSded, hSfin, hStf, hSfr, hGal, hSP, h𝔓max, hpmax, hpne,
    hpcent, hcent, hfrac⟩ :=
    ValuationSubring.exists_mulSemiringAction_integralClosure_inf_fixedPoints_of_isDiscreteValuationRing (G := G) P
  letI := instGS
  haveI := hRdvr; haveI := hRded; haveI := hSded; haveI := hSfin; haveI := hStf; haveI := hSfr; haveI := hGal
  haveI := h𝔓max
  set R : Type _ := ↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring) with hRdef
  set S : Type _ := ↥(integralClosure (↥(P.toSubring ⊓ (FixedPoints.subfield G F).toSubring)) F) with hSdef
  set p : Ideal R := 𝔓.comap (algebraMap R S) with hpdef
  haveI hlies : 𝔓.LiesOver p := ⟨rfl⟩
  haveI : p.IsMaximal := hpmax

  let ψ : S →+* ↥P := (algebraMap S F).codRestrict P.toSubring (fun s => hSP s)
  have hψker : ∀ s : S, IsLocalRing.residue ↥P (ψ s) = 0 ↔ s ∈ 𝔓 := by
    intro s
    rw [IsLocalRing.residue_eq_zero_iff, ← hcent s, ← ValuationSubring.coe_mem_nonunits_iff]
    rfl
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI : Field (S ⧸ 𝔓) := Ideal.Quotient.field 𝔓
  haveI : Finite (S ⧸ 𝔓) := by
    let τ : S ⧸ 𝔓 →+* IsLocalRing.ResidueField ↥P :=
      Ideal.Quotient.lift 𝔓 ((IsLocalRing.residue ↥P).comp ψ) (fun s hs => (hψker s).2 hs)
    exact Finite.of_injective τ τ.injective
  haveI : Finite (R ⧸ p) :=
    Finite.of_injective (Ideal.quotientMap 𝔓 (algebraMap R S) le_rfl) (Ideal.quotientMap_injective)
  haveI : PerfectField (R ⧸ p) := PerfectField.ofFinite
  haveI : Algebra.IsAlgebraic (R ⧸ p) (S ⧸ 𝔓) := Algebra.IsAlgebraic.of_finite (R ⧸ p) (S ⧸ 𝔓)
  haveI : Algebra.IsSeparable (R ⧸ p) (S ⧸ 𝔓) := Algebra.IsAlgebraic.isSeparable_of_perfectField

  obtain ⟨-, hcard⟩ :=
    ValuationSubring.smul_eq_and_forall_smul_sub_mem_nonunits_iff_mem_inertia_and_card_eq_ramificationIdxIn
      (R := R) (S := S) (F := F) (G := G) hGSF 𝔓 P hSP hcent hfrac
  have hcard' := hcard p hpne
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p 𝔓 G, ← Ideal.ramificationIdx'_eq_ramificationIdx p 𝔓 hpne] at hcard'
  set e : ℕ := p.ramificationIdx' 𝔓 with hedef

  let φ : R →+* ↥P := ψ.comp (algebraMap R S)
  have hφ : ∀ r : R, ((φ r : ↥P) : F) = algebraMap S F (algebraMap R S r) := fun r => rfl
  have hbridge : Ideal.map φ p = IsLocalRing.maximalIdeal ↥P ^ e :=
    Ideal.map_valuationSubring_eq_maximalIdeal_pow_ramificationIdx p hpne 𝔓 P hSP hcent hfrac φ hφ
  refine ⟨e, ?_, hcard', ?_⟩
  ·
    rw [← hcard']
    haveI : Finite {g : G // g • P = P ∧ ∀ x : ↥P, g • (x : F) - x ∈ P.nonunits} := Subtype.finite
    haveI : Nonempty {g : G // g • P = P ∧ ∀ x : ↥P, g • (x : F) - x ∈ P.nonunits} :=
      ⟨⟨1, one_smul _ _, fun x => by simp⟩⟩
    exact Nat.card_pos
  · intro x hx hx0 hGx

    have hxR : x ∈ P.toSubring ⊓ (FixedPoints.subfield G F).toSubring := ⟨hx, fun g => hGx g⟩
    set r : R := ⟨x, hxR⟩ with hrdef
    have hr0 : r ≠ 0 := fun h => hx0 (congrArg Subtype.val h)

    have hpm : p = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hpmax
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
      (show Ideal.span {r} ≠ ⊥ by simpa [Ideal.span_singleton_eq_bot] using hr0) hϖ
    have hmax : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
    refine ⟨k, ?_⟩
    have h1 : Ideal.map φ (Ideal.span {r}) = Ideal.span {(⟨x, hx⟩ : ↥P)} := by
      rw [Ideal.map_span, Set.image_singleton]
      congr 1
    rw [← h1, hk, ← Ideal.span_singleton_pow, Ideal.map_pow, ← hmax, ← hpm, hbridge, ← pow_mul]

theorem card_placeInertia_le_three
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (κ : Type) [Field κ] [CharP κ p] [DecidableEq κ] [Finite κ]
    (F : Type) [Field F] [Algebra κ F]
    (θ : F ≃+* ↥(ModularCurve.x1FunctionFieldC κ M))
    (hθ : ∀ a : κ, θ (algebraMap κ F a) = algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) a)
    (J : F) (hJ : ((θ J : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ) = ModularCurve.jqModC κ)
    (G : Type) [Group G] [Finite G] [MulSemiringAction G F] [FaithfulSMul G F]
    (hGκ : ∀ (g : G) (a : κ), g • algebraMap κ F a = algebraMap κ F a) (hGJ : ∀ g : G, g • J = J)
    (P : ValuationSubring F) (hPκ : ∀ a : κ, algebraMap κ F a ∈ P) (hPtop : P ≠ ⊤)
    (hPpir : IsPrincipalIdealRing ↥P) (hJP : J ∈ P) :
    Nat.card {g : G // g • P = P ∧ ∀ e : ↥P, g • (e : F) - e ∈ P.nonunits} ≤ 3 := by
  classical
  have hPκ₀ : ∀ a : κ, algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) a ∈ pushVS θ P := fun a => by
    rw [← hθ, apply_mem_pushVS_iff]; exact hPκ a
  have hfin : Finite (IsLocalRing.ResidueField ↥P) :=
    (finite_residueField_iff θ P).mp
      (Sep.finite_residueField_of_valuationSubring_x1FunctionFieldC p M hM hpM κ (pushVS θ P) hPκ₀
        (pushVS_ne_top θ P hPtop) (isPrincipalIdealRing_pushVS θ P hPpir))
  obtain ⟨e, hepos, hcard, hdiv⟩ :=
    exists_card_placeInertia_eq_and_span_eq_pow_mul F G P hPtop hPpir hfin
  obtain ⟨n, hn1, hn3, hspan⟩ :=
    span_aeval_minpoly_eq_pow_le_three p hp5 M hM hpM κ F θ hθ J hJ P hPκ hPtop hPpir hJP hfin

  haveI : IsPrincipalIdealRing ↥P := hPpir
  haveI : IsDiscreteValuationRing ↥P :=
    { toIsPrincipalIdealRing := hPpir
      toIsLocalRing := inferInstance
      not_a_field' := by
        rw [ne_eq, ← IsLocalRing.isField_iff_maximalIdeal_eq]
        exact ValuationSubring.not_isField_of_ne_top F hPtop }

  letI : Algebra κ ↥P := ((algebraMap κ F).codRestrict P.toSubring hPκ).toAlgebra
  haveI : IsScalarTower κ ↥P F := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  set xP : ↥P := Polynomial.aeval (⟨J, hJP⟩ : ↥P) (minpoly κ (IsLocalRing.residue ↥P ⟨J, hJP⟩)) with hxPdef
  have hxval : (xP : F) = Polynomial.aeval J (minpoly κ (IsLocalRing.residue ↥P ⟨J, hJP⟩)) := by
    rw [hxPdef]
    exact (Polynomial.aeval_algebraMap_apply F (⟨J, hJP⟩ : ↥P) _).symm

  have hx0 : (xP : F) ≠ 0 := by
    intro h0
    haveI : Module.Finite κ (IsLocalRing.ResidueField ↥P) := Module.Finite.of_finite
    have hm0 : minpoly κ (IsLocalRing.residue ↥P ⟨J, hJP⟩) ≠ 0 :=
      minpoly.ne_zero (Algebra.IsIntegral.isIntegral _)
    apply transcendental_of_coe_eq_jqModC κ M (θ J) hJ
    refine ⟨minpoly κ (IsLocalRing.residue ↥P ⟨J, hJP⟩), hm0, ?_⟩
    have hcomp : (θ : F →+* ↥(ModularCurve.x1FunctionFieldC κ M)).comp (algebraMap κ F)
        = algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) := RingHom.ext fun a => hθ a
    have : Polynomial.aeval (θ J) (minpoly κ (IsLocalRing.residue ↥P ⟨J, hJP⟩))
        = θ (Polynomial.aeval J (minpoly κ (IsLocalRing.residue ↥P ⟨J, hJP⟩))) := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def, ← RingEquiv.coe_toRingHom, Polynomial.hom_eval₂, hcomp]
    rw [this, ← hxval, h0, map_zero]

  have hGx : ∀ g : G, g • (xP : F) = (xP : F) := by
    intro g
    rw [hxval, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    set m₀ : Polynomial F := (minpoly κ (IsLocalRing.residue ↥P ⟨J, hJP⟩)).map (algebraMap κ F) with hm₀
    have hmap : g • m₀ = m₀ := by
      ext i
      simp [hm₀, Polynomial.coeff_smul, Polynomial.coeff_map, hGκ]
    calc g • Polynomial.eval J m₀ = Polynomial.eval (g • J) (g • m₀) := by rw [Polynomial.smul_eval_smul]
      _ = Polynomial.eval J m₀ := by rw [hmap, hGJ]
  obtain ⟨k, hk⟩ := hdiv (xP : F) xP.2 hx0 hGx
  have hk' : Ideal.span {xP} = IsLocalRing.maximalIdeal ↥P ^ (e * k) := by
    convert hk using 3
  have hpow : IsLocalRing.maximalIdeal ↥P ^ (e * k) = IsLocalRing.maximalIdeal ↥P ^ n := hk'.symm.trans hspan
  have hmb : IsLocalRing.maximalIdeal ↥P ≠ ⊥ := IsDiscreteValuationRing.not_a_field ↥P
  have hmt : IsLocalRing.maximalIdeal ↥P ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  have hek : e * k = n := (Ideal.pow_right_strictAnti _ hmb hmt).injective hpow
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, mul_zero] at hek; omega
    · exact hpos
  calc Nat.card {g : G // g • P = P ∧ ∀ e : ↥P, g • (e : F) - e ∈ P.nonunits} = e := hcard
    _ ≤ e * k := Nat.le_mul_of_pos_right e hk1
    _ = n := hek
    _ ≤ 3 := hn3

end ModularCurve.T4Core
p2m_reactivate "P2MW.S_ModularCurve_natCard_smul_valuationSubring_eq_and_forall_sub_mem_nonunits_le_three_of_ringEquiv_x1FunctionFieldC.ModularCurve P2MW.S_ModularCurve_natCard_smul_valuationSubring_eq_and_forall_sub_mem_nonunits_le_three_of_ringEquiv_x1FunctionFieldC.ModularCurve.T4Core"
p2m_reactivate "P2MW.S_ModularCurve_natCard_smul_valuationSubring_eq_and_forall_sub_mem_nonunits_le_three_of_ringEquiv_x1FunctionFieldC.ModularCurve"

open ModularCurve.T4Core in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (κ : Type) [Field κ] [CharP κ p] [Finite κ]
    (F : Type) [Field F] [Algebra κ F]
    (θ : F ≃+* ↥(ModularCurve.x1FunctionFieldC κ M))
    (hθ : ∀ a : κ, θ (algebraMap κ F a) = algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) a)
    (J : F) (hJ : ((θ J : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ) = ModularCurve.jqModC κ)
    (G : Type) [Group G] [Finite G] [MulSemiringAction G F] [FaithfulSMul G F]
    (hGκ : ∀ (g : G) (a : κ), g • algebraMap κ F a = algebraMap κ F a) (hGJ : ∀ g : G, g • J = J)
    (P : ValuationSubring F) (hPκ : ∀ a : κ, algebraMap κ F a ∈ P) (hPtop : P ≠ ⊤)
    (hPpir : IsPrincipalIdealRing ↥P) (hJP : J ∈ P) :
    Nat.card {g : G // g • P = P ∧ ∀ e : ↥P, g • (e : F) - e ∈ P.nonunits} ≤ 3 := by
  classical
  exact card_placeInertia_le_three p hp5 M hM hpM κ F θ hθ J hJ G hGκ hGJ P hPκ hPtop hPpir hJP

end
end S_ModularCurve_natCard_smul_valuationSubring_eq_and_forall_sub_mem_nonunits_le_three_of_ringEquiv_x1FunctionFieldC
end P2MW
export P2MW.S_ModularCurve_natCard_smul_valuationSubring_eq_and_forall_sub_mem_nonunits_le_three_of_ringEquiv_x1FunctionFieldC (solution)
