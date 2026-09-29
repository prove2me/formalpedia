-- Prove2me | solution 1 for ModularCurve.IgusaCover.ramificationIndexAlong_incl_eq_of_ord_hasseRootFn_pow_igusaFunctionFieldX1C
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/d19a5e9f-519d-5ace-b0ed-ed55e331deef

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_eq_one_of_pow_eq_of_mem_of_inv_mem
import Theorems.Thm_ModularCurve_hasseRootFn_pow_mem_and_finite_and_isSeparable_igusaFunctionFieldX1C
import Theorems.Thm_ModularCurve_finrank_x1FunctionFieldC_igusaFunctionFieldX1C_eq_sub_one
import Theorems.Thm_ModularCurve_exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_igusaFunctionFieldX1C
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable
import Theorems.Thm_ModularCurve_isRational_place_x1FunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_eq_of_pow_eq_of_isCoprime_ord
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaCover_ramificationIndexAlong_incl_eq_of_ord_hasseRootFn_pow_igusaFunctionFieldX1C
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex"
p2m_attr_erase "instance" "CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg"
p2m_attr_erase "instance" "KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
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

open CongruenceSubgroup AlgebraicCurve
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "x1FunctionFieldC IntegralWeightOneForm igusaFunctionFieldX1C IgusaCover.igusaFunctionField IgusaCover.incl hasseRootFn_pow_mem_and_finite_and_isSeparable_igusaFunctionFieldX1C finrank_x1FunctionFieldC_igusaFunctionFieldX1C_eq_sub_one exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_igusaFunctionFieldX1C isRational_place_x1FunctionFieldC_of_isAlgClosed"
namespace IgusaCover
p2m_export "ModularCurve.IgusaCover" "igusaFunctionField mem_igusaFunctionField incl coe_incl"
namespace KummerAsm
p2m_open "ModularCurve.IgusaCover ModularCurve"

theorem pow_rescale {K L : Type*} [Field K] [Field L] (φ : K →+* L) (aI : L) (b u π : K) (n : ℕ) (t : ℤ)
    (hπ : π ≠ 0) (haIn : φ b = aI ^ n) (hbu : b = u * π ^ ((n : ℤ) * t)) :
    φ u = (aI * (φ π) ^ (-t)) ^ n := by
  have hφπ : φ π ≠ 0 := (map_ne_zero φ).mpr hπ
  have hu : u = b * π ^ (-((n : ℤ) * t)) := by
    rw [hbu, mul_assoc, ← zpow_add₀ hπ, add_neg_cancel, zpow_zero, mul_one]
  rw [hu, map_mul, map_zpow₀, haIn, mul_pow, ← zpow_natCast ((φ π) ^ (-t)) n, ← zpow_mul]
  congr 1
  congr 1
  ring

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

theorem closure_range_incl_union_eq_top (K₀ : IntermediateField k Ω) (a : Ω) (c : ↥(igusaFunctionField K₀ a)) (y : ↥K₀) (t : ℤ)
    (hc : (⟨a, mem_igusaFunctionField K₀ a⟩ : ↥(igusaFunctionField K₀ a)) = c * (incl K₀ a y) ^ t) :
    Subfield.closure (Set.range (incl K₀ a) ∪ {c}) = ⊤ := by
  set T := Subfield.closure (Set.range (incl K₀ a) ∪ {c}) with hT
  have hφT : ∀ x, incl K₀ a x ∈ T := fun x => Subfield.subset_closure (Or.inl ⟨x, rfl⟩)
  have hcT : c ∈ T := Subfield.subset_closure (Or.inr rfl)
  have haIT : (⟨a, mem_igusaFunctionField K₀ a⟩ : ↥(igusaFunctionField K₀ a)) ∈ T := by
    rw [hc]; exact mul_mem hcT (zpow_mem (hφT _) t)

  let f : ↥(igusaFunctionField K₀ a) →+* Ω := (igusaFunctionField K₀ a).toSubfield.subtype
  have hf : ∀ x : ↥(igusaFunctionField K₀ a), f x = (x : Ω) := fun _ => rfl
  have hLle : (igusaFunctionField K₀ a).toSubfield ≤ T.map f := by
    have h1 : (igusaFunctionField K₀ a).toSubfield = Subfield.closure (Set.range (algebraMap k Ω) ∪ ((K₀ : Set Ω) ∪ {a})) := rfl
    rw [h1, Subfield.closure_le]
    have hK : ∀ z : Ω, ∀ hz : z ∈ K₀, z ∈ (T.map f : Set Ω) := fun z hz =>
      ⟨incl K₀ a ⟨z, hz⟩, hφT _, by rw [hf, coe_incl]⟩
    rintro z (⟨r, rfl⟩ | hz | hz)
    · exact hK _ (K₀.algebraMap_mem r)
    · exact hK _ hz
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact ⟨_, haIT, by rw [hf]⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨z, hzT, hz⟩ := hLle x.2
  rw [hf] at hz
  have : z = x := Subtype.ext hz
  rw [← this]; exact hzT

end ModularCurve.IgusaCover.KummerAsm

p2m_open "ModularCurve P2MW.S_ModularCurve_IgusaCover_ramificationIndexAlong_incl_eq_of_ord_hasseRootFn_pow_igusaFunctionFieldX1C.ModularCurve ModularCurve.IgusaCover P2MW.S_ModularCurve_IgusaCover_ramificationIndexAlong_incl_eq_of_ord_hasseRootFn_pow_igusaFunctionFieldX1C.ModularCurve.IgusaCover"

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (w : ModularCurve.IntegralWeightOneForm k M)
    (hint : (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn).toRingHom.IsIntegral)
    (b : ↥(ModularCurve.x1FunctionFieldC k M)) (hb : (b : LaurentSeries k) = w.hasseRootFn ^ (p - 1))
    (P : Place k ↥(ModularCurve.IgusaCover.igusaFunctionField (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn)) :
    ((((p - 1 : ℕ) : ℤ) ∣
        (P.restrictAlong (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn) hint).ord b) →
      Place.ramificationIndexAlong
        (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn) P = 1) ∧
    (IsCoprime
        ((P.restrictAlong (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn) hint).ord b)
        ((p - 1 : ℕ) : ℤ) →
      Place.ramificationIndexAlong
        (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn) P = p - 1) := by
  classical
  have hp : p.Prime := Fact.out
  have ha0 : w.hasseRootFn ≠ 0 := w.hasseRootFn_ne_zero

  have haIn : (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn) b = (⟨w.hasseRootFn, mem_igusaFunctionField _ _⟩ : ↥(igusaFunctionField (x1FunctionFieldC k M) w.hasseRootFn)) ^ (p - 1) := by
    apply Subtype.ext
    rw [coe_incl, hb, SubmonoidClass.coe_pow]
  have hb0 : b ≠ 0 := by
    intro h
    have : ((b : ↥(x1FunctionFieldC k M)) : LaurentSeries k) = 0 := by rw [h]; rfl
    rw [hb] at this
    exact pow_ne_zero _ ha0 this

  obtain ⟨-, hfin, hsep⟩ := ModularCurve.hasseRootFn_pow_mem_and_finite_and_isSeparable_igusaFunctionFieldX1C p M hM hpM k w
  have hdeg := ModularCurve.finrank_x1FunctionFieldC_igusaFunctionFieldX1C_eq_sub_one p M hM hpM k w
  obtain ⟨tj, -, htr, hfinT, hsepT⟩ :=
    ModularCurve.exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_igusaFunctionFieldX1C p M hM hpM k w
  haveI hCO : AlgebraicCurve.IsCurveOver k ↥(igusaFunctionField (x1FunctionFieldC k M) w.hasseRootFn) :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable k _ tj htr hfinT hsepT
  haveI hPD : AlgebraicCurve.HasPrincipalDivisors k ↥(igusaFunctionField (x1FunctionFieldC k M) w.hasseRootFn) := hCO.toHasPrincipalDivisors
  refine ⟨fun hdvd => ?_, fun hcop => ?_⟩
  swap

  · exact @AlgebraicCurve.Place.ramificationIndexAlong_eq_of_pow_eq_of_isCoprime_ord k _ _ _ _ _ _ _ hPD (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn) hint hfin hsep (p - 1) hdeg _ b haIn P hcop

  · obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (P.restrictAlong (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn) hint).toValuationSubring
    have hπ0 : (π : ↥(x1FunctionFieldC k M)) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
    obtain ⟨u₁, hu₁⟩ := (P.restrictAlong (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn) hint).exists_unit_mul_zpow hb0 hπ
    obtain ⟨t, ht⟩ := hdvd
    have hφπ0 : (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn) (π : ↥(x1FunctionFieldC k M)) ≠ 0 := fun h =>
      hπ0 ((ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn).toRingHom.injective (by rw [map_zero]; exact h))
    rw [ht] at hu₁

    have hcu := KummerAsm.pow_rescale (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn).toRingHom _ b _ _ (p - 1) t hπ0 haIn hu₁
    have huP : ((u₁ : (P.restrictAlong (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn) hint).toValuationSubring) : ↥(x1FunctionFieldC k M)) ∈ (P.restrictAlong (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn) hint).toValuationSubring ∧
        ((u₁ : (P.restrictAlong (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn) hint).toValuationSubring) : ↥(x1FunctionFieldC k M))⁻¹ ∈ (P.restrictAlong (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn) hint).toValuationSubring := by
      refine ⟨(u₁ : (P.restrictAlong (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn) hint).toValuationSubring).2, ?_⟩
      have hinv : ((u₁ : (P.restrictAlong (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn) hint).toValuationSubring) : ↥(x1FunctionFieldC k M))⁻¹ =
          (((u₁⁻¹ : ((P.restrictAlong (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn) hint).toValuationSubring)ˣ) : (P.restrictAlong (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn) hint).toValuationSubring) : ↥(x1FunctionFieldC k M)) := by
        apply inv_eq_of_mul_eq_one_right
        rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
      rw [hinv]; exact (((u₁⁻¹ : ((P.restrictAlong (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn) hint).toValuationSubring)ˣ) : (P.restrictAlong (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn) hint).toValuationSubring)).2
    have hgen := KummerAsm.closure_range_incl_union_eq_top (x1FunctionFieldC k M) w.hasseRootFn
      ((⟨w.hasseRootFn, mem_igusaFunctionField _ _⟩ : ↥(igusaFunctionField (x1FunctionFieldC k M) w.hasseRootFn)) * ((ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn) (π : ↥(x1FunctionFieldC k M))) ^ (-t))
      π t (by rw [mul_assoc, ← zpow_add₀ hφπ0, neg_add_cancel, zpow_zero, mul_one])
    have hrat : (P.restrictAlong (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn) hint).IsRational :=
      ModularCurve.isRational_place_x1FunctionFieldC_of_isAlgClosed p M hM hpM k _
    have hnk : ((p - 1 : ℕ) : k) ≠ 0 := by
      rw [Nat.cast_sub hp.one_le, Nat.cast_one, CharP.cast_eq_zero k p, zero_sub]
      exact neg_ne_zero.mpr one_ne_zero
    exact AlgebraicCurve.Place.ramificationIndexAlong_eq_one_of_pow_eq_of_mem_of_inv_mem (ModularCurve.IgusaCover.incl (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn) hint (p - 1) hnk _ hgen _ hcu P hrat huP

end S_ModularCurve_IgusaCover_ramificationIndexAlong_incl_eq_of_ord_hasseRootFn_pow_igusaFunctionFieldX1C
end P2MW
export P2MW.S_ModularCurve_IgusaCover_ramificationIndexAlong_incl_eq_of_ord_hasseRootFn_pow_igusaFunctionFieldX1C (solution)
