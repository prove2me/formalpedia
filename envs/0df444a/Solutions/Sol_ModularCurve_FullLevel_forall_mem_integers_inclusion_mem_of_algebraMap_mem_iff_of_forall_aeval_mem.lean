-- Prove2me | solution 1 for ModularCurve.FullLevel.forall_mem_integers_inclusion_mem_of_algebraMap_mem_iff_of_forall_aeval_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/70589a09-5954-5475-ab49-7cb186a04c2a

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_valuationSubring_unique_laurentBaseChange_gamma0_of_not_dvd
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_of_liesOverPrime
import Theorems.Thm_ModularCurve_FullLevel_aeval_jq_mem_integers_and_inv_mem_of_map_residue_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_forall_mem_integers_inclusion_mem_of_algebraMap_mem_iff_of_forall_aeval_mem
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "instance" "ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces CohCarrier.frickeH1L_apply"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP"
p2m_attr_erase "simp" "ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one"
p2m_attr_erase "simp" "compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 12800000

p2m_open "ModularCurve~coeffMap_injective"

namespace L1BExh

theorem coeffMap_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (x : LaurentSeries R) : coeffMap g (coeffMap f x) = coeffMap (g.comp f) x := by
  ext k; rfl

theorem coeffMap_coeffEmb {L L' : Type*} [Field L] [Field L'] [Algebra ℚ L] [Algebra ℚ L']
    (φ : L →+* L') (hφ : ∀ r : ℚ, φ (algebraMap ℚ L r) = algebraMap ℚ L' r) (x : LaurentSeries ℚ) :
    coeffMap φ (coeffEmb L x) = coeffEmb L' x := by
  ext k
  show φ (algebraMap ℚ L (x.coeff k)) = algebraMap ℚ L' (x.coeff k)
  exact hφ _

theorem coeffMap_algebraMap' {L L' : Type*} [Field L] [Field L'] (φ : L →+* L') (c : L) :
    coeffMap φ (algebraMap L (LaurentSeries L) c) = algebraMap L' (LaurentSeries L') (φ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  exact hf (by have := congrArg (fun z : LaurentSeries S => z.coeff k) h; exact this)

theorem coeffMap_mem_laurentBaseChange_of_mem {L L' : Type*} [Field L] [Field L'] [Algebra ℚ L] [Algebra ℚ L']
    (φ : L →+* L') (hφ : ∀ r : ℚ, φ (algebraMap ℚ L r) = algebraMap ℚ L' r)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) {x : LaurentSeries L} (hx : x ∈ laurentBaseChange L F₀) :
    coeffMap φ x ∈ laurentBaseChange L' F₀ := by
  rw [mem_laurentBaseChange_iff] at hx ⊢
  induction hx using Subfield.closure_induction with
  | mem y hy =>
    rcases hy with ⟨c, rfl⟩ | ⟨z, hz, rfl⟩
    · rw [coeffMap_algebraMap']
      exact Subfield.subset_closure (Or.inl ⟨φ c, rfl⟩)
    · rw [coeffMap_coeffEmb φ hφ]
      exact Subfield.subset_closure (Or.inr ⟨z, hz, rfl⟩)
  | one => rw [map_one]; exact Subfield.one_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Subfield.add_mem _ ha hb
  | neg a _ ha => rw [map_neg]; exact Subfield.neg_mem _ ha
  | inv a _ ha => rw [map_inv₀]; exact Subfield.inv_mem _ ha
  | mul a b _ _ ha hb => rw [map_mul]; exact Subfield.mul_mem _ ha hb

theorem exists_finiteDimensional_mem_laurentBaseChange (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (f : LaurentSeries (AlgebraicClosure ℚ)) (hf : f ∈ laurentBaseChange (AlgebraicClosure ℚ) F₀) :
    ∃ (K₂ : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ ↥K₂) (g : LaurentSeries ↥K₂),
      g ∈ laurentBaseChange ↥K₂ F₀ ∧ coeffMap (algebraMap ↥K₂ (AlgebraicClosure ℚ)) g = f := by
  classical
  rw [mem_laurentBaseChange_iff] at hf

  have lift : ∀ (K₂ K₃ : IntermediateField ℚ (AlgebraicClosure ℚ)) (h : K₂ ≤ K₃) (g : LaurentSeries ↥K₂),
      g ∈ laurentBaseChange ↥K₂ F₀ →
      coeffMap (IntermediateField.inclusion h).toRingHom g ∈ laurentBaseChange ↥K₃ F₀ ∧
        coeffMap (algebraMap ↥K₃ (AlgebraicClosure ℚ)) (coeffMap (IntermediateField.inclusion h).toRingHom g) =
          coeffMap (algebraMap ↥K₂ (AlgebraicClosure ℚ)) g := by
    intro K₂ K₃ h g hg
    refine ⟨coeffMap_mem_laurentBaseChange_of_mem _ (fun r => ?_) F₀ hg, ?_⟩
    · apply Subtype.ext; simp
    · rw [coeffMap_comp]; rfl
  induction hf using Subfield.closure_induction with
  | mem y hy =>
    rcases hy with ⟨c, rfl⟩ | ⟨z, hz, rfl⟩
    ·
      haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
      let K₂ : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {c}
      let c' : ↥K₂ := ⟨c, IntermediateField.mem_adjoin_simple_self ℚ c⟩
      refine ⟨K₂, IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral c),
        algebraMap ↥K₂ (LaurentSeries ↥K₂) c', ?_, ?_⟩
      · exact (laurentBaseChange ↥K₂ F₀).algebraMap_mem _
      · rw [coeffMap_algebraMap']; rfl
    ·
      refine ⟨⊥, inferInstance, coeffEmb _ z, coeffEmb_mem_laurentBaseChange _ hz, ?_⟩
      exact coeffMap_coeffEmb _ (fun r => rfl) z
  | one => exact ⟨⊥, inferInstance, 1, Subfield.one_mem _, map_one _⟩
  | add a b _ _ ha hb =>
    obtain ⟨K₂, hK₂, g, hg, rfl⟩ := ha
    obtain ⟨K₃, hK₃, g', hg', rfl⟩ := hb
    haveI := hK₂; haveI := hK₃
    obtain ⟨h1, e1⟩ := lift K₂ (K₂ ⊔ K₃) le_sup_left g hg
    obtain ⟨h2, e2⟩ := lift K₃ (K₂ ⊔ K₃) le_sup_right g' hg'
    exact ⟨K₂ ⊔ K₃, IntermediateField.finiteDimensional_sup K₂ K₃, _, Subfield.add_mem _ h1 h2, by rw [map_add, e1, e2]⟩
  | neg a _ ha =>
    obtain ⟨K₂, hK₂, g, hg, rfl⟩ := ha
    exact ⟨K₂, hK₂, -g, Subfield.neg_mem _ hg, map_neg _ _⟩
  | inv a _ ha =>
    obtain ⟨K₂, hK₂, g, hg, rfl⟩ := ha
    exact ⟨K₂, hK₂, g⁻¹, Subfield.inv_mem _ hg, map_inv₀ _ _⟩
  | mul a b _ _ ha hb =>
    obtain ⟨K₂, hK₂, g, hg, rfl⟩ := ha
    obtain ⟨K₃, hK₃, g', hg', rfl⟩ := hb
    haveI := hK₂; haveI := hK₃
    obtain ⟨h1, e1⟩ := lift K₂ (K₂ ⊔ K₃) le_sup_left g hg
    obtain ⟨h2, e2⟩ := lift K₃ (K₂ ⊔ K₃) le_sup_right g' hg'
    exact ⟨K₂ ⊔ K₃, IntermediateField.finiteDimensional_sup K₂ K₃, _, Subfield.mul_mem _ h1 h2, by rw [map_mul, e1, e2]⟩

theorem coeffMap_inclusion_mem_and_eq (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (K₂ K₃ : IntermediateField ℚ (AlgebraicClosure ℚ)) (h : K₂ ≤ K₃) (g : LaurentSeries ↥K₂)
    (hg : g ∈ laurentBaseChange ↥K₂ F₀) :
    coeffMap (IntermediateField.inclusion h).toRingHom g ∈ laurentBaseChange ↥K₃ F₀ ∧
      coeffMap (algebraMap ↥K₃ (AlgebraicClosure ℚ)) (coeffMap (IntermediateField.inclusion h).toRingHom g) =
        coeffMap (algebraMap ↥K₂ (AlgebraicClosure ℚ)) g := by
  refine ⟨coeffMap_mem_laurentBaseChange_of_mem _ (fun r => ?_) F₀ hg, ?_⟩
  · apply Subtype.ext; simp
  · rw [coeffMap_comp]; rfl

end L1BExh

p2m_open "AlgebraicCurve ModularCurve~coeffMap_injective ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

namespace L1BE2

noncomputable abbrev floor (M' : ℕ) [NeZero M'] (K₂ : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    IntermediateField ↥K₂ (LaurentSeries ↥K₂) :=
  laurentBaseChange ↥K₂ (qExpFunctionFieldC ℚ (Gamma0 M'))

theorem floor_eq (M' : ℕ) [NeZero M'] (K₂ : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    floor M' K₂ = laurentBaseChange ↥K₂ (modularFunctionFieldFull M') := by
  rw [floor, ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]

theorem coeffMap_mem_modularFunctionFieldBar (M' : ℕ) [NeZero M'] (K₂ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (x : ↥(floor M' K₂)) :
    coeffMap (algebraMap ↥K₂ (AlgebraicClosure ℚ)) (x : LaurentSeries ↥K₂) ∈ modularFunctionFieldBar M' := by
  have hx : (x : LaurentSeries ↥K₂) ∈ laurentBaseChange ↥K₂ (modularFunctionFieldFull M') := by
    rw [← floor_eq]; exact x.2
  exact L1BExh.coeffMap_mem_laurentBaseChange_of_mem _ (fun r => by simp) _ hx

noncomputable def φ' (M' : ℕ) [NeZero M'] (K₂ : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    ↥(floor M' K₂) →+* ↥(modularFunctionFieldBar M') :=
  ((coeffMap (algebraMap ↥K₂ (AlgebraicClosure ℚ))).comp (floor M' K₂).toSubfield.subtype).codRestrict
    (modularFunctionFieldBar M') (fun x => coeffMap_mem_modularFunctionFieldBar M' K₂ x)

theorem coe_φ' (M' : ℕ) [NeZero M'] (K₂ : IntermediateField ℚ (AlgebraicClosure ℚ)) (x : ↥(floor M' K₂)) :
    ((φ' M' K₂ x : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap (algebraMap ↥K₂ (AlgebraicClosure ℚ)) (x : LaurentSeries ↥K₂) := rfl

theorem φ'_algebraMap (M' : ℕ) [NeZero M'] (K₂ : IntermediateField ℚ (AlgebraicClosure ℚ)) (c : ↥K₂) :
    φ' M' K₂ (algebraMap ↥K₂ ↥(floor M' K₂) c) =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (c : AlgebraicClosure ℚ) := by
  apply Subtype.ext
  rw [coe_φ']
  show coeffMap _ (algebraMap ↥K₂ (LaurentSeries ↥K₂) c) = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ)
  rw [L1BExh.coeffMap_algebraMap']; rfl

end L1BE2

p2m_open "AlgebraicCurve ModularCurve~coeffMap_injective ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))

    (O : ValuationSubring (fieldBar q M'))
    (hOA : ∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ O ↔ x ∈ A)
    (hOj : ∀ P : Polynomial ↥A, P.map (IsLocalRing.residue ↥A) ≠ 0 →
      Polynomial.aeval (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') P ∈ O ∧
      (Polynomial.aeval (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') P)⁻¹ ∈ O) :
    ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers → (IntermediateField.inclusion hle f : fieldBar q M') ∈ O := by
  classical
  intro f hfR

  obtain ⟨K₂, hK₂, g, hg, hgf⟩ :=
    L1BExh.exists_finiteDimensional_mem_laurentBaseChange (modularFunctionFieldFull M') (f : LaurentSeries (AlgebraicClosure ℚ)) f.2
  haveI := hK₂
  let gK : ↥(L1BE2.floor M' K₂) := ⟨g, by rw [L1BE2.floor_eq]; exact hg⟩
  have hφg : L1BE2.φ' M' K₂ gK = f := Subtype.ext hgf

  let A₂ : ValuationSubring ↥K₂ := A.comap (algebraMap ↥K₂ (AlgebraicClosure ℚ))
  haveI : IsDiscreteValuationRing ↥A₂ :=
    ValuationSubring.isDiscreteValuationRing_comap_of_liesOverPrime K₂ A (Fact.out : q.Prime) hA
  let ι₂ : ↥A₂ →+* ↥A :=
    { toFun := fun a => ⟨((a : ↥K₂) : AlgebraicClosure ℚ), a.2⟩
      map_one' := Subtype.ext (by simp), map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp), map_add' := fun a b => Subtype.ext (by simp) }
  have hι₂ : ∀ a : ↥A₂, ((ι₂ a : ↥A) : AlgebraicClosure ℚ) = ((a : ↥K₂) : AlgebraicClosure ℚ) := fun a => rfl

  have hunit : ∀ a : ↥A₂, a ∈ maximalIdeal ↥A₂ ↔ ι₂ a ∈ maximalIdeal ↥A := by
    intro a
    rw [← ValuationSubring.coe_mem_nonunits_iff, ← ValuationSubring.coe_mem_nonunits_iff, hι₂,
      ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or]
    have hinvA : (a : ↥K₂)⁻¹ ∈ A₂ ↔ ((a : ↥K₂) : AlgebraicClosure ℚ)⁻¹ ∈ A := by
      show algebraMap ↥K₂ (AlgebraicClosure ℚ) ((a : ↥K₂)⁻¹) ∈ A ↔ _
      rw [map_inv₀]; rfl
    have h0 : (a : ↥K₂) = 0 ↔ ((a : ↥K₂) : AlgebraicClosure ℚ) = 0 := by
      rw [← map_eq_zero_iff (algebraMap ↥K₂ (AlgebraicClosure ℚ)) (algebraMap ↥K₂ (AlgebraicClosure ℚ)).injective]; rfl
    rw [h0, hinvA]
  have hAq : ((q : ↥A₂)) ∈ maximalIdeal ↥A₂ := by
    rw [hunit, ← ValuationSubring.coe_mem_nonunits_iff]
    have : ((ι₂ (q : ↥A₂) : ↥A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := by rw [hι₂]; simp
    rw [this]; exact hA

  have hjq : jq ∈ qExpFunctionFieldC ℚ (Gamma0 M') := by
    rw [ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]; exact jq_mem_full M'
  let j₀ : ↥(L1BE2.floor M' K₂) := ⟨coeffEmb ↥K₂ jq, coeffEmb_mem_laurentBaseChange ↥K₂ hjq⟩
  let jM : ↥(modularFunctionFieldBar M') := ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩
  have hφj : L1BE2.φ' M' K₂ j₀ = jM := by
    apply Subtype.ext; rw [L1BE2.coe_φ']
    exact L1BExh.coeffMap_coeffEmb _ (fun r => by simp) jq

  let φ := (IntermediateField.inclusion hle).toRingHom.comp (L1BE2.φ' M' K₂)
  let V : ValuationSubring ↥(L1BE2.floor M' K₂) := O.comap φ
  let V' : ValuationSubring ↥(L1BE2.floor M' K₂) := R₀.integers.comap (L1BE2.φ' M' K₂)

  have hconst' : ∀ a : ↥A₂, L1BE2.φ' M' K₂ (algebraMap ↥K₂ _ (algebraMap ↥A₂ ↥K₂ a)) =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') ((ι₂ a : ↥A) : AlgebraicClosure ℚ) := by
    intro a; rw [L1BE2.φ'_algebraMap]; rfl
  have hconst : ∀ a : ↥A₂, φ (algebraMap ↥K₂ _ (algebraMap ↥A₂ ↥K₂ a)) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι₂ a : ↥A) : AlgebraicClosure ℚ) := by
    intro a
    show IntermediateField.inclusion hle (L1BE2.φ' M' K₂ _) = _
    rw [hconst']
    apply Subtype.ext; rfl

  have hPmap : ∀ P : Polynomial ↥A₂, P.map (IsLocalRing.residue ↥A₂) ≠ 0 → (P.map ι₂).map (IsLocalRing.residue ↥A) ≠ 0 := by
    intro P hP h0
    apply hP
    ext n
    have := congrArg (fun Q : Polynomial (ResidueField ↥A) => Q.coeff n) h0
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at this ⊢
    rw [IsLocalRing.residue_eq_zero_iff] at this ⊢
    exact (hunit _).mpr this
  have haeval' : ∀ P : Polynomial ↥A₂,
      L1BE2.φ' M' K₂ (Polynomial.aeval j₀ (P.map (algebraMap ↥A₂ ↥K₂))) = Polynomial.aeval jM (P.map ι₂) := by
    intro P
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂, hφj, Polynomial.aeval_def, Polynomial.eval₂_map]
    congr 1
    refine RingHom.ext fun a => ?_
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [hconst']
    apply Subtype.ext; rfl
  have haeval : ∀ P : Polynomial ↥A₂,
      φ (Polynomial.aeval j₀ (P.map (algebraMap ↥A₂ ↥K₂))) = Polynomial.aeval (IntermediateField.inclusion hle jM) (P.map ι₂) := by
    intro P
    show (IntermediateField.inclusion hle).toRingHom (L1BE2.φ' M' K₂ _) = _
    rw [haeval', Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
    congr 1

  have hV : (∀ a : ↥A₂, algebraMap ↥K₂ ↥(L1BE2.floor M' K₂) (algebraMap ↥A₂ ↥K₂ a) ∈ V) ∧
      (∀ a ∈ maximalIdeal ↥A₂, algebraMap ↥K₂ ↥(L1BE2.floor M' K₂) (algebraMap ↥A₂ ↥K₂ a) ∈ V.nonunits) ∧
      (∀ P : Polynomial ↥A₂, P.map (IsLocalRing.residue ↥A₂) ≠ 0 →
        Polynomial.aeval j₀ (P.map (algebraMap ↥A₂ ↥K₂)) ∈ V ∧ (Polynomial.aeval j₀ (P.map (algebraMap ↥A₂ ↥K₂)))⁻¹ ∈ V) := by
    refine ⟨fun a => ?_, fun a ha => ?_, fun P hP => ?_⟩
    · show φ _ ∈ O
      rw [hconst]; exact (hOA _).mpr (ι₂ a).2
    ·
      have hιa : ((ι₂ a : ↥A) : AlgebraicClosure ℚ) ∈ A.nonunits :=
        ValuationSubring.coe_mem_nonunits_iff.mpr ((hunit a).mp ha)
      rw [ValuationSubring.mem_nonunits_iff_or] at hιa ⊢
      rcases hιa with h0 | hinv
      · left
        have : algebraMap ↥A₂ ↥K₂ a = 0 := by
          apply Subtype.ext
          show ((a : ↥K₂) : AlgebraicClosure ℚ) = 0
          exact h0
        rw [this, map_zero]
      · right
        intro hmem
        apply hinv
        have : φ ((algebraMap ↥K₂ ↥(L1BE2.floor M' K₂) (algebraMap ↥A₂ ↥K₂ a))⁻¹) ∈ O := hmem
        rw [map_inv₀, hconst, ← map_inv₀] at this
        exact (hOA _).mp this
    · obtain ⟨h1, h2⟩ := hOj (P.map ι₂) (hPmap P hP)
      refine ⟨?_, ?_⟩
      · show φ _ ∈ O; rw [haeval]; exact h1
      · show φ _ ∈ O; rw [map_inv₀, haeval]; exact h2

  have hV' : (∀ a : ↥A₂, algebraMap ↥K₂ ↥(L1BE2.floor M' K₂) (algebraMap ↥A₂ ↥K₂ a) ∈ V') ∧
      (∀ a ∈ maximalIdeal ↥A₂, algebraMap ↥K₂ ↥(L1BE2.floor M' K₂) (algebraMap ↥A₂ ↥K₂ a) ∈ V'.nonunits) ∧
      (∀ P : Polynomial ↥A₂, P.map (IsLocalRing.residue ↥A₂) ≠ 0 →
        Polynomial.aeval j₀ (P.map (algebraMap ↥A₂ ↥K₂)) ∈ V' ∧ (Polynomial.aeval j₀ (P.map (algebraMap ↥A₂ ↥K₂)))⁻¹ ∈ V') := by
    refine ⟨fun a => ?_, fun a ha => ?_, fun P hP => ?_⟩
    · show L1BE2.φ' M' K₂ _ ∈ R₀.integers
      rw [hconst']; exact (R₀.algebraMap_mem_iff _).mpr (ι₂ a).2
    · have hιa : ((ι₂ a : ↥A) : AlgebraicClosure ℚ) ∈ A.nonunits :=
        ValuationSubring.coe_mem_nonunits_iff.mpr ((hunit a).mp ha)
      rw [ValuationSubring.mem_nonunits_iff_or] at hιa ⊢
      rcases hιa with h0 | hinv
      · left
        have : algebraMap ↥A₂ ↥K₂ a = 0 := by
          apply Subtype.ext
          show ((a : ↥K₂) : AlgebraicClosure ℚ) = 0
          exact h0
        rw [this, map_zero]
      · right
        intro hmem
        apply hinv
        have : L1BE2.φ' M' K₂ ((algebraMap ↥K₂ ↥(L1BE2.floor M' K₂) (algebraMap ↥A₂ ↥K₂ a))⁻¹) ∈ R₀.integers := hmem
        rw [map_inv₀, hconst', ← map_inv₀] at this
        exact (R₀.algebraMap_mem_iff _).mp this
    · obtain ⟨h1, h2⟩ := ModularCurve.FullLevel.aeval_jq_mem_integers_and_inv_mem_of_map_residue_ne_zero
        q hq M' hqM' A hA R₀ hR₀ (P.map ι₂) (hPmap P hP)
      refine ⟨?_, ?_⟩
      · show L1BE2.φ' M' K₂ _ ∈ R₀.integers; rw [haeval']; exact h1
      · show L1BE2.φ' M' K₂ _ ∈ R₀.integers; rw [map_inv₀, haeval']; exact h2

  have hVV : V = V' :=
    ModularCurve.valuationSubring_unique_laurentBaseChange_gamma0_of_not_dvd q M' hqM' ↥K₂ (L1BE2.floor M' K₂) rfl
      ↥A₂ hAq j₀ rfl V V' hV hV'
  have hgV' : gK ∈ V' := by
    show L1BE2.φ' M' K₂ gK ∈ R₀.integers
    rw [hφg]; exact hfR
  have hgV : gK ∈ V := by rw [hVV]; exact hgV'
  have hφgK : φ gK = IntermediateField.inclusion hle f := by
    show IntermediateField.inclusion hle (L1BE2.φ' M' K₂ gK) = _
    rw [hφg]
  rw [← hφgK]
  exact hgV

end S_ModularCurve_FullLevel_forall_mem_integers_inclusion_mem_of_algebraMap_mem_iff_of_forall_aeval_mem
end P2MW
export P2MW.S_ModularCurve_FullLevel_forall_mem_integers_inclusion_mem_of_algebraMap_mem_iff_of_forall_aeval_mem (solution)
