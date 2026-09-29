-- Prove2me | solution 1 for ModularCurve.exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/bf419bc9-c670-5405-992e-6efb14dce2e5

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_exists_curveModel_iso_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_readChart_of_not_dvd
import Theorems.Thm_ModularCurve_exists_curveModel_qExpFunctionFieldC_iso_pullback_germ_eq_coeffMap_of_ringHom
import Theorems.Thm_ValuationSubring_exists_ratLocalizedAt_ringHom_of_liesOverPrime
import Theorems.Thm_ValuationSubring_exists_dvd_pow_of_mem_maximalIdeal
import Theorems.Thm_ValuationSubring_charP_residueField_of_liesOverPrime
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd"
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "simp" "CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq"
p2m_attr_erase "simp" "CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one"
p2m_attr_erase "simp" "AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ"
p2m_attr_erase "simp" "ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst"

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open scoped MatrixGroups
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve P2MW.S_ModularCurve_exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom.ModularCurve IsLocalRing TopologicalSpace Opposite"

universe u

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel.chartAlgFin TwoChartIntegralModel.chartAlgInf TwoChartIntegralModel TwoChartIntegralModel.ιFin TwoChartIntegralModel.ιInf TwoChartIntegralModel.toBase CurveModel"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "j_ne_zero chartAlg chartAlg_mono coe_chartIncl exists_pow_mul_mem_chartAlg chartAlgFin chartAlgInf chartAlgMid jChartFin coe_jChartFin inclFin inclInf isLocalization_away_inclFin XMid fFin fInf ιFin ιInf glue_condition toBase fibre"
namespace ReadCharts
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

local notation "𝕏" => AlgebraicCurve.TwoChartIntegralModel R F j

def secFin (b : chartAlgFin R F j) : Γ(𝕏, (ιFin R F j) ''ᵁ ⊤) :=
  ((ιFin R F j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of (chartAlgFin R F j))).inv b)

def secInf (b : chartAlgInf R F j) : Γ(𝕏, (ιInf R F j) ''ᵁ ⊤) :=
  ((ιInf R F j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of (chartAlgInf R F j))).inv b)

abbrev gMid : XMid R F j ⟶ 𝕏 := fFin R F j ≫ ιFin R F j

theorem gMid_eq : gMid R F j = fInf R F j ≫ ιInf R F j := glue_condition R F j

abbrev W : (𝕏).Opens := (gMid R F j) ''ᵁ ⊤

theorem W_le_fin : W R F j ≤ (ιFin R F j) ''ᵁ ⊤ := by
  rw [W, Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_comp,
    Scheme.Hom.image_top_eq_opensRange]
  exact Scheme.Hom.image_le_opensRange _ _

theorem image_congr {X' Y' : Scheme.{u}} {f g : X' ⟶ Y'} [IsOpenImmersion f] [IsOpenImmersion g]
    (e : f = g) (U : X'.Opens) : f ''ᵁ U = g ''ᵁ U := by
  subst e; rfl

theorem W_le_inf : W R F j ≤ (ιInf R F j) ''ᵁ ⊤ := by
  rw [W, image_congr (gMid_eq R F j), Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_comp,
    Scheme.Hom.image_top_eq_opensRange]
  exact Scheme.Hom.image_le_opensRange _ _

theorem opensRange_fFin : (fFin R F j).opensRange = PrimeSpectrum.basicOpen (jChartFin R F j) := by
  letI := (inclFin R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R F j
  apply TopologicalSpace.Opens.ext
  rw [Scheme.Hom.coe_opensRange]
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid R F j) (jChartFin R F j)

theorem basicOpen_secFin_jChartFin : (𝕏).basicOpen (secFin R F j (jChartFin R F j)) = W R F j := by
  rw [secFin, ← Scheme.image_basicOpen, basicOpen_eq_of_affine, ← opensRange_fFin, W,
    Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_comp]

theorem appIso_hom_map_appIso_inv {U' V' : Scheme.{u}} (h : U' ⟶ V') (ι : V' ⟶ 𝕏)
    [IsOpenImmersion h] [IsOpenImmersion ι] (g : U' ⟶ 𝕏) [IsOpenImmersion g] (hg : g = h ≫ ι)
    (le : g ''ᵁ ⊤ ≤ ι ''ᵁ ⊤) (r : Γ(V', ⊤)) :
    (g.appIso ⊤).hom ((𝕏).presheaf.map (homOfLE le).op ((ι.appIso ⊤).inv r)) = h.appTop r := by
  subst hg
  have e₁ : ⊤ ≤ ι ⁻¹ᵁ ι ''ᵁ ⊤ := (ι.preimage_image_eq ⊤).ge
  have e₂ : (⊤ : U'.Opens) ≤ h ⁻¹ᵁ ⊤ := le_top
  rw [Scheme.Hom.appIso_hom', ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
    ← Scheme.Hom.appLE_comp_appLE h ι (ι ''ᵁ ⊤) ⊤ ⊤ e₁ e₂, CommRingCat.comp_apply,
    ← Scheme.Hom.appIso_hom', Iso.inv_hom_id_apply]
  change (h.appLE ⊤ (h ⁻¹ᵁ ⊤) le_rfl) r = h.appTop r
  rw [Scheme.Hom.appLE_eq_app]
  rfl

theorem appIso_hom_map_secFin (b : chartAlgFin R F j) :
    ((gMid R F j).appIso ⊤).hom ((𝕏).presheaf.map (homOfLE (W_le_fin R F j)).op (secFin R F j b)) =
      (Scheme.ΓSpecIso (CommRingCat.of (chartAlgMid R F j))).inv (inclFin R F j b) := by
  rw [secFin, appIso_hom_map_appIso_inv R F j (fFin R F j) (ιFin R F j) (gMid R F j) rfl,
    ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  rfl

theorem appIso_hom_map_secInf (b : chartAlgInf R F j) :
    ((gMid R F j).appIso ⊤).hom ((𝕏).presheaf.map (homOfLE (W_le_inf R F j)).op (secInf R F j b)) =
      (Scheme.ΓSpecIso (CommRingCat.of (chartAlgMid R F j))).inv (inclInf R F j b) := by
  rw [secInf, appIso_hom_map_appIso_inv R F j (fInf R F j) (ιInf R F j) (gMid R F j) (gMid_eq R F j),
    ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  rfl

theorem map_secFin_eq_pow_mul (b : chartAlgInf R F j) (c : chartAlgFin R F j) (n : ℕ)
    (hc : (c : F) = j ^ n * b) :
    (𝕏).presheaf.map (homOfLE (W_le_fin R F j)).op (secFin R F j c) =
      (𝕏).presheaf.map (homOfLE (W_le_fin R F j)).op (secFin R F j (jChartFin R F j)) ^ n *
        (𝕏).presheaf.map (homOfLE (W_le_inf R F j)).op (secInf R F j b) := by
  apply ((gMid R F j).appIso ⊤).commRingCatIsoToRingEquiv.injective
  change ((gMid R F j).appIso ⊤).hom _ = ((gMid R F j).appIso ⊤).hom _
  rw [map_mul, map_pow, appIso_hom_map_secFin, appIso_hom_map_secFin, appIso_hom_map_secInf, ← map_pow,
    ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, coe_chartIncl, coe_jChartFin]
  exact hc

theorem germToFunctionField_app_congr {Y X : Scheme.{u}} [IsIntegral Y] {φ₁ φ₂ : Y ⟶ X} (e : φ₁ = φ₂)
    (U : X.Opens) [Nonempty (Scheme.Opens.toScheme (φ₁ ⁻¹ᵁ U))] [Nonempty (Scheme.Opens.toScheme (φ₂ ⁻¹ᵁ U))]
    (s : Γ(X, U)) :
    Y.germToFunctionField (φ₁ ⁻¹ᵁ U) ((φ₁.app U).hom s) =
      Y.germToFunctionField (φ₂ ⁻¹ᵁ U) ((φ₂.app U).hom s) := by
  subst e; rfl

theorem germToFunctionField_app_map {Y X : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ X) {U V : X.Opens}
    (le : V ≤ U) [Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ U))] [Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ V))]
    (s : Γ(X, U)) :
    Y.germToFunctionField (f ⁻¹ᵁ V) ((f.app V).hom (X.presheaf.map (homOfLE le).op s)) =
      Y.germToFunctionField (f ⁻¹ᵁ U) ((f.app U).hom s) := by
  have h1 : (f.app V).hom (X.presheaf.map (homOfLE le).op s) =
      (Y.presheaf.map (homOfLE (f.preimage_mono le)).op) ((f.app U).hom s) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, f.naturality]
    rfl
  rw [h1]
  exact TopCat.Presheaf.germ_res_apply Y.presheaf _ _ _ _

theorem nonempty_and_germ_secFin_eq {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ 𝕏)
    [hF : Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ ((ιFin R F j) ''ᵁ ⊤)))]
    (hj : Y.germToFunctionField (f ⁻¹ᵁ ((ιFin R F j) ''ᵁ ⊤))
      ((f.app ((ιFin R F j) ''ᵁ ⊤)).hom (secFin R F j (jChartFin R F j))) ≠ 0) :
    Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ ((ιInf R F j) ''ᵁ ⊤))) ∧
    ∀ [Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ ((ιInf R F j) ''ᵁ ⊤)))]
      (b : chartAlgInf R F j) (c : chartAlgFin R F j) (n : ℕ), (c : F) = j ^ n * b →
      Y.germToFunctionField (f ⁻¹ᵁ ((ιFin R F j) ''ᵁ ⊤)) ((f.app ((ιFin R F j) ''ᵁ ⊤)).hom (secFin R F j c)) =
        Y.germToFunctionField (f ⁻¹ᵁ ((ιFin R F j) ''ᵁ ⊤))
            ((f.app ((ιFin R F j) ''ᵁ ⊤)).hom (secFin R F j (jChartFin R F j))) ^ n *
          Y.germToFunctionField (f ⁻¹ᵁ ((ιInf R F j) ''ᵁ ⊤)) ((f.app ((ιInf R F j) ''ᵁ ⊤)).hom (secInf R F j b)) := by

  set ξ := genericPoint Y with hξ
  have hξF : ξ ∈ f ⁻¹ᵁ ((ιFin R F j) ''ᵁ ⊤) :=
    ((genericPoint_spec Y).mem_open_set_iff (f ⁻¹ᵁ ((ιFin R F j) ''ᵁ ⊤)).isOpen).mpr
      (by simpa using hF)
  have hξW : ξ ∈ f ⁻¹ᵁ (W R F j) := by
    rw [← basicOpen_secFin_jChartFin, Scheme.preimage_basicOpen]
    exact (Y.mem_basicOpen _ ξ hξF).mpr (isUnit_iff_ne_zero.mpr hj)
  haveI hW : Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ (W R F j))) := ⟨⟨ξ, hξW⟩⟩
  have hξI : ξ ∈ f ⁻¹ᵁ ((ιInf R F j) ''ᵁ ⊤) := f.preimage_mono (W_le_inf R F j) hξW
  refine ⟨⟨⟨ξ, hξI⟩⟩, ?_⟩
  intro _ b c n hc
  have key := congrArg (fun t => Y.germToFunctionField (f ⁻¹ᵁ (W R F j)) ((f.app (W R F j)).hom t))
    (map_secFin_eq_pow_mul R F j b c n hc)
  simp only [map_mul, map_pow] at key
  rw [germToFunctionField_app_map, germToFunctionField_app_map, germToFunctionField_app_map] at key
  exact key

end AlgebraicCurve.TwoChartIntegralModel.ReadCharts

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC x1FunctionFieldC x1FunctionField constantCoeff_jNum coeffMap coeffMap_coeffMap coeffEmb jqModC map_jqModC exists_curveModel_iso_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_readChart_of_not_dvd exists_curveModel_qExpFunctionFieldC_iso_pullback_germ_eq_coeffMap_of_ringHom coeffMap_jqModC"
namespace FibresReadCharts
p2m_open "ModularCurve"

p2m_open "AlgebraicCurve.TwoChartIntegralModel P2MW.S_ModularCurve_exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom.AlgebraicCurve.TwoChartIntegralModel P2MW.S_ModularCurve_exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom.AlgebraicCurve.TwoChartIntegralModel.ReadCharts"

theorem jqModC_ne_zero (K : Type*) [CommRing K] [Nontrivial K] : jqModC K ≠ 0 := by
  intro h
  have h1 : (jqModC K).coeff (-1) = 1 := by
    rw [jqModC, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, neg_add_cancel,
      show ((0 : ℤ)) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum, map_one]
  rw [h] at h1
  simp at h1

theorem coeffMap_jqModC {K K' : Type*} [CommRing K] [CommRing K'] (f : K →+* K') :
    coeffMap f (jqModC K) = jqModC K' :=
  map_jqModC f

theorem apply_eq_zero_of_mem_maximalIdeal (p : ℕ) [Fact p.Prime] (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (hPl : Pl.LiesOverPrime p) {k : Type*} [Field k] [CharP k p] (πk : ↥Pl →+* k)
    (x : ↥Pl) (hx : x ∈ maximalIdeal ↥Pl) : πk x = 0 := by
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]
  have hp0 : ((p : ℕ) : ↥Pl) ≠ 0 := by
    intro h
    have : ((p : ℕ) : AlgebraicClosure ℚ) = 0 := by exact_mod_cast congrArg (Subtype.val) h
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) this
  obtain ⟨N, hN⟩ := ValuationSubring.exists_dvd_pow_of_mem_maximalIdeal Pl (q := p) hPl _ hp0 x hx hx0
  obtain ⟨t, ht⟩ := hN
  have h2 : πk x ^ N = 0 := by
    rw [← map_pow, ht, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]
  exact pow_eq_zero_iff'.mp h2 |>.1

theorem exists_residueField_lift (p : ℕ) [Fact p.Prime] (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (hPl : Pl.LiesOverPrime p) {k : Type*} [Field k] [CharP k p] (πk : ↥Pl →+* k) :
    ∃ ι : ResidueField ↥Pl →+* k, ι.comp (residue ↥Pl) = πk := by
  refine ⟨Ideal.Quotient.lift (maximalIdeal ↥Pl) πk (apply_eq_zero_of_mem_maximalIdeal p Pl hPl πk), ?_⟩
  ext x
  rfl

theorem nonempty_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] (U : Y.Opens)
    [h : Nonempty (Scheme.Opens.toScheme U)] : Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ U)) := by
  obtain ⟨⟨y, hy⟩⟩ := h
  obtain ⟨x, rfl⟩ := f.surjective y
  exact ⟨⟨x, hy⟩⟩

scoped instance surjective_specMap_of_field {κ k : Type u} [Field κ] [Field k] (ι : κ →+* k) :
    Surjective (Spec.map (CommRingCat.ofHom ι)) :=
  ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩

end ModularCurve.FibresReadCharts
p2m_reactivate "P2MW.S_ModularCurve_exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom.ModularCurve P2MW.S_ModularCurve_exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom.ModularCurve.FibresReadCharts"
p2m_reactivate "P2MW.S_ModularCurve_exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC x1FunctionFieldC x1FunctionField constantCoeff_jNum coeffMap coeffMap_coeffMap coeffEmb jqModC map_jqModC exists_curveModel_iso_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_readChart_of_not_dvd exists_curveModel_qExpFunctionFieldC_iso_pullback_germ_eq_coeffMap_of_ringHom coeffMap_jqModC"
namespace FibresReadCharts
p2m_open "ModularCurve"

p2m_open "AlgebraicCurve.TwoChartIntegralModel P2MW.S_ModularCurve_exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom.AlgebraicCurve.TwoChartIntegralModel P2MW.S_ModularCurve_exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom.AlgebraicCurve.TwoChartIntegralModel.ReadCharts"

variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
  (j : ↥(ModularCurve.x1FunctionField M)) [Fact (j ≠ 0)]
  (Pl : ValuationSubring (AlgebraicClosure ℚ))

set_option quotPrecheck false in
local notation "ℤp" => ↥(GaloisRep.ratLocalizedAt p)
set_option quotPrecheck false in
local notation "F₁" => ↥(ModularCurve.x1FunctionField M)

theorem infRead_of_finRead
    (hj : ((j : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) = ModularCurve.jqModC ℚ)
    {K : Type} [Field K] (τ : ↥Pl →+* K)
    (N : CurveModel K ↥(ModularCurve.x1FunctionFieldC K M))
    (φ : N.C ⟶ TwoChartIntegralModel ℤp F₁ j)
    [hne : Nonempty (Scheme.Opens.toScheme (φ ⁻¹ᵁ ((ιFin ℤp F₁ j) ''ᵁ ⊤)))]
    (hfin : ∀ (b : ↥(chartAlgFin ℤp F₁ j)) (y : LaurentSeries ↥Pl),
      coeffMap Pl.subtype y = coeffEmb (AlgebraicClosure ℚ) ((b : F₁) : LaurentSeries ℚ) →
      ((N.ffEquiv.symm (N.C.germToFunctionField (φ ⁻¹ᵁ ((ιFin ℤp F₁ j) ''ᵁ ⊤))
        ((φ.app ((ιFin ℤp F₁ j) ''ᵁ ⊤)).hom (secFin ℤp F₁ j b))) : ↥(ModularCurve.x1FunctionFieldC K M)) :
          LaurentSeries K) = coeffMap τ y) :
    Nonempty (Scheme.Opens.toScheme (φ ⁻¹ᵁ ((ιInf ℤp F₁ j) ''ᵁ ⊤))) ∧
    ∀ [Nonempty (Scheme.Opens.toScheme (φ ⁻¹ᵁ ((ιInf ℤp F₁ j) ''ᵁ ⊤)))]
      (b : ↥(chartAlgInf ℤp F₁ j)) (y : LaurentSeries ↥Pl),
      coeffMap Pl.subtype y = coeffEmb (AlgebraicClosure ℚ) ((b : F₁) : LaurentSeries ℚ) →
      ((N.ffEquiv.symm (N.C.germToFunctionField (φ ⁻¹ᵁ ((ιInf ℤp F₁ j) ''ᵁ ⊤))
        ((φ.app ((ιInf ℤp F₁ j) ''ᵁ ⊤)).hom (secInf ℤp F₁ j b))) : ↥(ModularCurve.x1FunctionFieldC K M)) :
          LaurentSeries K) = coeffMap τ y := by

  have hyj : coeffMap Pl.subtype (jqModC ↥Pl) =
      coeffEmb (AlgebraicClosure ℚ) (((jChartFin ℤp F₁ j : ↥(chartAlgFin ℤp F₁ j)) : F₁) : LaurentSeries ℚ) := by
    rw [coeffMap_jqModC, coe_jChartFin, hj, coeffEmb, coeffMap_jqModC]
  have hreadj := hfin (jChartFin ℤp F₁ j) (jqModC ↥Pl) hyj
  rw [coeffMap_jqModC] at hreadj
  have hj0 : N.C.germToFunctionField (φ ⁻¹ᵁ ((ιFin ℤp F₁ j) ''ᵁ ⊤))
      ((φ.app ((ιFin ℤp F₁ j) ''ᵁ ⊤)).hom (secFin ℤp F₁ j (jChartFin ℤp F₁ j))) ≠ 0 := by
    intro h0
    rw [h0, map_zero, ZeroMemClass.coe_zero] at hreadj
    exact jqModC_ne_zero K hreadj.symm
  obtain ⟨hneI, hrel⟩ := nonempty_and_germ_secFin_eq ℤp F₁ j φ hj0
  refine ⟨hneI, ?_⟩
  intro _ b y hy

  have hbmem : (b : F₁) ∈ chartAlg ℤp F₁ (insert j⁻¹ {j}) :=
    chartAlg_mono ℤp F₁ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) b.2
  obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartAlg (R := ℤp) (Set.mem_singleton j) (j_ne_zero j) hbmem
  set c : ↥(chartAlgFin ℤp F₁ j) := ⟨j ^ n * b, hn⟩ with hc
  have hcF : (c : F₁) = j ^ n * b := rfl

  have hyc : coeffMap Pl.subtype (jqModC ↥Pl ^ n * y) =
      coeffEmb (AlgebraicClosure ℚ) ((c : F₁) : LaurentSeries ℚ) := by
    rw [map_mul, map_pow, hy, coeffMap_jqModC, hcF]
    push_cast
    rw [map_mul, map_pow, hj, coeffEmb, coeffMap_jqModC]
  have hreadc := hfin c (jqModC ↥Pl ^ n * y) hyc
  rw [map_mul, map_pow, coeffMap_jqModC, hrel b c n hcF, map_mul, map_pow] at hreadc
  push_cast at hreadc
  rw [hreadj] at hreadc
  exact mul_left_cancel₀ (pow_ne_zero n (jqModC_ne_zero K)) hreadc

end ModularCurve.FibresReadCharts
p2m_reactivate "P2MW.S_ModularCurve_exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom.ModularCurve P2MW.S_ModularCurve_exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom.ModularCurve.FibresReadCharts"
p2m_reactivate "P2MW.S_ModularCurve_exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom.ModularCurve P2MW.S_ModularCurve_exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom.ModularCurve.FibresReadCharts"

p2m_open "AlgebraicCurve.TwoChartIntegralModel P2MW.S_ModularCurve_exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom.AlgebraicCurve.TwoChartIntegralModel P2MW.S_ModularCurve_exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom.AlgebraicCurve.TwoChartIntegralModel.ReadCharts P2MW.S_ModularCurve_exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom.ModularCurve.FibresReadCharts"

set_option hygiene false in
set_option quotPrecheck false in
local notation "ℤp" => ↥(GaloisRep.ratLocalizedAt p)
set_option hygiene false in
set_option quotPrecheck false in
local notation "F₁" => ↥(ModularCurve.x1FunctionField M)

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (j : ↥(ModularCurve.x1FunctionField M)) [Fact (j ≠ 0)] (hj : ((j : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) = ModularCurve.jqModC ℚ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (πk : ↥Pl →+* k) :
    ∃ (ρ₀ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥Pl) (_ : Pl.subtype.comp ρ₀ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
      (ι : (IsLocalRing.ResidueField ↥Pl) →+* k) (_ : ι.comp (IsLocalRing.residue ↥Pl) = πk)

      (M₀ : CurveModel (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M))
      (e₀ : M₀.C ⟶ pullback (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ₀))))
      (_ : IsIso e₀) (_ : e₀ ≫ pullback.snd _ _ = M₀.toBase)
      (hne₀ : Nonempty (Scheme.Opens.toScheme ((e₀ ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))))
      (_ : ∀ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j)) (y : LaurentSeries ↥Pl),
        ModularCurve.coeffMap Pl.subtype y = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) →
        (((M₀.ffEquiv.symm
            (M₀.C.germToFunctionField ((e₀ ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))
              (((e₀ ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ₀)))).app ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤)).hom
                (((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j))).inv b))))) : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M)) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
          ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y)
      (hne₀Inf : Nonempty (Scheme.Opens.toScheme ((e₀ ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))))
      (_ : ∀ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j)) (y : LaurentSeries ↥Pl),
        ModularCurve.coeffMap Pl.subtype y = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) →
        (((M₀.ffEquiv.symm
            (M₀.C.germToFunctionField ((e₀ ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))
              (((e₀ ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ₀)))).app ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤)).hom
                (((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j))).inv b))))) : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M)) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
          ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y)

      (Mk : CurveModel k ↥(ModularCurve.x1FunctionFieldC k M))
      (ek : Mk.C ⟶ pullback (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀))))
      (_ : IsIso ek) (_ : ek ≫ pullback.snd _ _ = Mk.toBase)
      (hnek : Nonempty (Scheme.Opens.toScheme ((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))))
      (_ : ∀ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j)) (y : LaurentSeries ↥Pl),
        ModularCurve.coeffMap Pl.subtype y = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) →
        (((Mk.ffEquiv.symm
            (Mk.C.germToFunctionField ((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))
              (((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))).app ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤)).hom
                (((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j))).inv b))))) : ↥(ModularCurve.x1FunctionFieldC k M)) : LaurentSeries k) = ModularCurve.coeffMap πk y)
      (hnekInf : Nonempty (Scheme.Opens.toScheme ((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))))
      (_ : ∀ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j)) (y : LaurentSeries ↥Pl),
        ModularCurve.coeffMap Pl.subtype y = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) →
        (((Mk.ffEquiv.symm
            (Mk.C.germToFunctionField ((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))
              (((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))).app ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤)).hom
                (((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j))).inv b))))) : ↥(ModularCurve.x1FunctionFieldC k M)) : LaurentSeries k) = ModularCurve.coeffMap πk y)

      (g : Mk.C ≅ pullback M₀.toBase (Spec.map (CommRingCat.ofHom ι)))
      (_ : g.hom ≫ pullback.snd M₀.toBase (Spec.map (CommRingCat.ofHom ι)) = Mk.toBase)
      (_ : (g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))) ≫ (e₀ ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ₀)))) = (ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))))

      (ψ : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M) →+* ↥(ModularCurve.x1FunctionFieldC k M))
      (_ : ∀ f : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M), ((ψ f : ↥(ModularCurve.x1FunctionFieldC k M)) : LaurentSeries k) = ModularCurve.coeffMap ι ((f : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M)) : LaurentSeries (IsLocalRing.ResidueField ↥Pl))),
      ∀ (U : M₀.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
        [Nonempty (Scheme.Opens.toScheme ((g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))) ⁻¹ᵁ U))] (s : Γ(M₀.C, U)),
        Mk.ffEquiv.symm (Mk.C.germToFunctionField ((g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))) ⁻¹ᵁ U) (((g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))).app U).hom s)) =
          ψ (M₀.ffEquiv.symm (M₀.C.germToFunctionField U s)) := by
  classical

  haveI : CharP (ResidueField ↥Pl) p := ValuationSubring.charP_residueField_of_liesOverPrime p Pl hPl
  haveI : IsAlgClosed (ResidueField ↥Pl) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat Pl

  have hρ := ValuationSubring.exists_ratLocalizedAt_ringHom_of_liesOverPrime p Pl hPl
  choose ρ₀ hρ₀ using hρ
  let ι : ResidueField ↥Pl →+* k :=
    Ideal.Quotient.lift (maximalIdeal ↥Pl) πk (apply_eq_zero_of_mem_maximalIdeal p Pl hPl πk)
  have hι : ι.comp (residue ↥Pl) = πk := RingHom.ext fun x => rfl

  have hA : ∃ (Mfib : CurveModel (ResidueField ↥Pl) ↥(x1FunctionFieldC (ResidueField ↥Pl) M))
      (efib : Mfib.C ⟶ pullback (toBase ℤp F₁ j) (Spec.map (CommRingCat.ofHom ((residue ↥Pl).comp ρ₀))))
      (_ : IsIso efib)
      (_ : Nonempty (Scheme.Opens.toScheme
        ((efib ≫ pullback.fst (toBase ℤp F₁ j) (Spec.map (CommRingCat.ofHom ((residue ↥Pl).comp ρ₀)))) ⁻¹ᵁ
          ((ιFin ℤp F₁ j) ''ᵁ ⊤)))),
      efib ≫ pullback.snd (toBase ℤp F₁ j) (Spec.map (CommRingCat.ofHom ((residue ↥Pl).comp ρ₀))) = Mfib.toBase ∧
      ∀ (b : ↥(chartAlgFin ℤp F₁ j)) (y : LaurentSeries ↥Pl),
        coeffMap Pl.subtype y = coeffEmb (AlgebraicClosure ℚ) ((b : F₁) : LaurentSeries ℚ) →
        ((Mfib.ffEquiv.symm
            (Mfib.C.germToFunctionField
              ((efib ≫ pullback.fst (toBase ℤp F₁ j) (Spec.map (CommRingCat.ofHom ((residue ↥Pl).comp ρ₀)))) ⁻¹ᵁ
                ((ιFin ℤp F₁ j) ''ᵁ ⊤))
              (((efib ≫ pullback.fst (toBase ℤp F₁ j) (Spec.map (CommRingCat.ofHom ((residue ↥Pl).comp ρ₀)))).app
                ((ιFin ℤp F₁ j) ''ᵁ ⊤)).hom (secFin ℤp F₁ j b)))
          : ↥(x1FunctionFieldC (ResidueField ↥Pl) M)) : LaurentSeries (ResidueField ↥Pl)) =
          coeffMap (residue ↥Pl) y :=
    @ModularCurve.exists_curveModel_iso_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_readChart_of_not_dvd
      M _ (CongruenceSubgroup.Gamma1 M) le_rfl (CongruenceSubgroup.Gamma1_in_Gamma0 M) p _ hpM j ‹Fact (j ≠ 0)› hj
      Pl hPl _ _ ρ₀ hρ₀
  choose M₀ e₀ hiso₀ hne₀ hsnd₀ hfin₀ using hA

  have hB := @infRead_of_finRead p _ M _ j ‹Fact (j ≠ 0)› Pl hj _ _ (residue ↥Pl) M₀
    (e₀ ≫ pullback.fst (toBase ℤp F₁ j) _) hne₀ hfin₀
  have hne₀I := hB.1
  have hinf₀ := @hB.2 hne₀I

  have hC : ∃ (Mk : CurveModel k ↥(x1FunctionFieldC k M))
      (g : Mk.C ≅ pullback M₀.toBase (Spec.map (CommRingCat.ofHom ι)))
      (_ : g.hom ≫ pullback.snd M₀.toBase (Spec.map (CommRingCat.ofHom ι)) = Mk.toBase)
      (ψ : ↥(x1FunctionFieldC (ResidueField ↥Pl) M) →+* ↥(x1FunctionFieldC k M))
      (_ : ∀ f : ↥(x1FunctionFieldC (ResidueField ↥Pl) M),
        ((ψ f : ↥(x1FunctionFieldC k M)) : LaurentSeries k) =
          coeffMap ι ((f : ↥(x1FunctionFieldC (ResidueField ↥Pl) M)) : LaurentSeries (ResidueField ↥Pl))),
      ∀ (U : M₀.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
        [Nonempty (Scheme.Opens.toScheme
          ((g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))) ⁻¹ᵁ U))]
        (s : Γ(M₀.C, U)),
        Mk.ffEquiv.symm
            (Mk.C.germToFunctionField
              ((g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))) ⁻¹ᵁ U)
              (((g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))).app U).hom s)) =
          ψ (M₀.ffEquiv.symm (M₀.C.germToFunctionField U s)) :=
    ModularCurve.exists_curveModel_qExpFunctionFieldC_iso_pullback_germ_eq_coeffMap_of_ringHom
      ι (CongruenceSubgroup.Gamma1 M) M₀
  choose Mk g hg ψ hψ hsq using hC

  have hSpec : Spec.map (CommRingCat.ofHom ι) ≫ Spec.map (CommRingCat.ofHom ((residue ↥Pl).comp ρ₀)) =
      Spec.map (CommRingCat.ofHom (πk.comp ρ₀)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hι]
  let Φ : pullback M₀.toBase (Spec.map (CommRingCat.ofHom ι)) ≅
      pullback (toBase ℤp F₁ j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀))) :=
    pullback.congrHom hsnd₀.symm rfl ≪≫
      asIso (pullback.map (e₀ ≫ pullback.snd (toBase ℤp F₁ j) (Spec.map (CommRingCat.ofHom ((residue ↥Pl).comp ρ₀)))) (Spec.map (CommRingCat.ofHom ι))
        (pullback.snd (toBase ℤp F₁ j) (Spec.map (CommRingCat.ofHom ((residue ↥Pl).comp ρ₀)))) (Spec.map (CommRingCat.ofHom ι)) e₀ (𝟙 _) (𝟙 _)
        (by simp) (by simp)) ≪≫
      pullbackLeftPullbackSndIso (toBase ℤp F₁ j) (Spec.map (CommRingCat.ofHom ((residue ↥Pl).comp ρ₀))) (Spec.map (CommRingCat.ofHom ι)) ≪≫
      pullback.congrHom rfl hSpec
  have hΦfst : Φ.hom ≫ pullback.fst (toBase ℤp F₁ j) _ =
      pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι)) ≫ e₀ ≫ pullback.fst (toBase ℤp F₁ j) _ := by
    simp only [Φ, Iso.trans_hom, asIso_hom, pullback.congrHom, Category.assoc, pullback.lift_fst,
      pullback.lift_fst_assoc, pullbackLeftPullbackSndIso_hom_fst_assoc, pullbackLeftPullbackSndIso_hom_fst,
      Category.comp_id, Category.id_comp]
  have hΦsnd : Φ.hom ≫ pullback.snd (toBase ℤp F₁ j) _ = pullback.snd M₀.toBase (Spec.map (CommRingCat.ofHom ι)) := by
    simp only [Φ, Iso.trans_hom, asIso_hom, pullback.congrHom, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc, pullbackLeftPullbackSndIso_hom_snd_assoc, pullbackLeftPullbackSndIso_hom_snd,
      Category.comp_id, Category.id_comp]
  have hek_iso : IsIso (g.hom ≫ Φ.hom) := inferInstance
  have hek_snd : (g.hom ≫ Φ.hom) ≫ pullback.snd (toBase ℤp F₁ j) _ = Mk.toBase := by
    rw [Category.assoc, hΦsnd, hg]
  have hek_fst : (g.hom ≫ Φ.hom) ≫ pullback.fst (toBase ℤp F₁ j) _ =
      (g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))) ≫ (e₀ ≫ pullback.fst (toBase ℤp F₁ j) _) := by
    rw [Category.assoc, hΦfst, Category.assoc]

  haveI : Surjective (g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))) := inferInstance
  haveI hnekF' : Nonempty (Scheme.Opens.toScheme (((g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))) ≫
      (e₀ ≫ pullback.fst (toBase ℤp F₁ j) _)) ⁻¹ᵁ ((ιFin ℤp F₁ j) ''ᵁ ⊤))) :=
    nonempty_preimage (g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι)))
      ((e₀ ≫ pullback.fst (toBase ℤp F₁ j) _) ⁻¹ᵁ ((ιFin ℤp F₁ j) ''ᵁ ⊤))
  haveI hnekI' : Nonempty (Scheme.Opens.toScheme (((g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))) ≫
      (e₀ ≫ pullback.fst (toBase ℤp F₁ j) _)) ⁻¹ᵁ ((ιInf ℤp F₁ j) ''ᵁ ⊤))) :=
    nonempty_preimage (g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι)))
      ((e₀ ≫ pullback.fst (toBase ℤp F₁ j) _) ⁻¹ᵁ ((ιInf ℤp F₁ j) ''ᵁ ⊤))
  haveI hnekF : Nonempty (Scheme.Opens.toScheme (((g.hom ≫ Φ.hom) ≫ pullback.fst (toBase ℤp F₁ j) _) ⁻¹ᵁ ((ιFin ℤp F₁ j) ''ᵁ ⊤))) := by
    rw [hek_fst]; exact hnekF'
  haveI hnekI : Nonempty (Scheme.Opens.toScheme (((g.hom ≫ Φ.hom) ≫ pullback.fst (toBase ℤp F₁ j) _) ⁻¹ᵁ ((ιInf ℤp F₁ j) ''ᵁ ⊤))) := by
    rw [hek_fst]; exact hnekI'

  have hread : ∀ (U : (TwoChartIntegralModel ℤp F₁ j).Opens)
      [Nonempty (Scheme.Opens.toScheme ((e₀ ≫ pullback.fst (toBase ℤp F₁ j) _) ⁻¹ᵁ U))]
      [Nonempty (Scheme.Opens.toScheme (((g.hom ≫ Φ.hom) ≫ pullback.fst (toBase ℤp F₁ j) _) ⁻¹ᵁ U))]
      [Nonempty (Scheme.Opens.toScheme (((g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))) ≫
        (e₀ ≫ pullback.fst (toBase ℤp F₁ j) _)) ⁻¹ᵁ U))]
      (s : Γ(TwoChartIntegralModel ℤp F₁ j, U)) (y : LaurentSeries ↥Pl),
      ((M₀.ffEquiv.symm (M₀.C.germToFunctionField ((e₀ ≫ pullback.fst (toBase ℤp F₁ j) _) ⁻¹ᵁ U)
        (((e₀ ≫ pullback.fst (toBase ℤp F₁ j) _).app U).hom s)) : ↥(x1FunctionFieldC (ResidueField ↥Pl) M)) :
          LaurentSeries (ResidueField ↥Pl)) = coeffMap (residue ↥Pl) y →
      ((Mk.ffEquiv.symm (Mk.C.germToFunctionField (((g.hom ≫ Φ.hom) ≫ pullback.fst (toBase ℤp F₁ j) _) ⁻¹ᵁ U)
        ((((g.hom ≫ Φ.hom) ≫ pullback.fst (toBase ℤp F₁ j) _).app U).hom s)) : ↥(x1FunctionFieldC k M)) : LaurentSeries k) =
        coeffMap πk y := by
    intro U _ _ hU3 s y hs
    haveI : Nonempty (Scheme.Opens.toScheme ((g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))) ⁻¹ᵁ
        ((e₀ ≫ pullback.fst (toBase ℤp F₁ j) _) ⁻¹ᵁ U))) := hU3
    rw [germToFunctionField_app_congr hek_fst U s]
    have h1 := hsq ((e₀ ≫ pullback.fst (toBase ℤp F₁ j) _) ⁻¹ᵁ U) (((e₀ ≫ pullback.fst (toBase ℤp F₁ j) _).app U).hom s)
    change Mk.ffEquiv.symm (Mk.C.germToFunctionField _ _) = _ at h1
    erw [h1, hψ, hs, coeffMap_coeffMap, hι]
  refine ⟨ρ₀, hρ₀, ι, hι, M₀, e₀, hiso₀, hsnd₀, hne₀, hfin₀, hne₀I, hinf₀, Mk, g.hom ≫ Φ.hom, hek_iso, hek_snd, hnekF,
    ?_, hnekI, ?_, g, hg, hek_fst.symm, ψ, hψ, ?_⟩
  · intro b y hy
    exact hread _ (secFin ℤp F₁ j b) y (hfin₀ b y hy)
  · intro b y hy
    exact hread _ (secInf ℤp F₁ j b) y (hinf₀ b y hy)
  · intro U _ _ s
    exact hsq U s

end
p2m_reactivate "P2MW.S_ModularCurve_exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom.ModularCurve P2MW.S_ModularCurve_exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom.ModularCurve.FibresReadCharts"

end S_ModularCurve_exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom
end P2MW
export P2MW.S_ModularCurve_exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom (solution)
