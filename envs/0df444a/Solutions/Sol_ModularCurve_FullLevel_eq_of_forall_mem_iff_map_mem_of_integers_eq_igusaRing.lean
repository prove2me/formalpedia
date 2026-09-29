-- Prove2me | solution 1 for ModularCurve.FullLevel.eq_of_forall_mem_iff_map_mem_of_integers_eq_igusaRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/3357dd0a-154a-58a2-b862-4d9a1ba28efb

import Theorems.Thm_ModularCurve_FullLevel_exists_igusaValuationSubrings
import Theorems.Thm_ModularCurve_FullLevel_existsUnique_place_restrictAlong_eq_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_FullLevel_exists_coe_levelAutBar_apply_eq_qTwist_of_not_dvd_of_mem_laurentBaseChange_gamma0
import Theorems.Thm_ModularCurve_FullLevel_isKummerGenerator_eisensteinRatio_and_igusaFunctionField_eq_xHFunctionFieldC_levelH
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_FullLevel_existsUnique_place_forall_mem_iff_mem_of_coe_eq_qExpand_sq_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_eq_of_forall_mem_iff_map_mem_of_integers_eq_igusaRing
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms"
p2m_attr_erase "instance" "CuspForm.GammaH_finiteIndex"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe"
p2m_attr_erase "simp" "AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U"
p2m_attr_erase "simp" "CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply"

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace IgNodeAux
open ModularCurve

theorem coeffMap_qTwist {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u : Rˣ) (x : LaurentSeries R) :
    coeffMap f (qTwist u x) = qTwist (Units.map (f : R →* S) u) (coeffMap f x) := by
  ext k
  rw [coeffMap_coeff, qTwist_coeff, qTwist_coeff, coeffMap_coeff, map_mul, ← map_zpow (Units.map (f : R →* S)) u k,
    Units.coe_map]
  rfl

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N]
    (x : LaurentSeries R) : coeffMap f (qExpand R N x) = qExpand S N (coeffMap f x) := by
  ext k
  by_cases h : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd (hk := h), qExpand_coeff_of_not_dvd (hk := h), map_zero]

theorem coeffMap_jqModC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    coeffMap f (jqModC R) = jqModC S := by
  rw [jqModC_eq_map_intCast R, jqModC_eq_map_intCast S]
  ext k
  simp [coeffMap_coeff]

theorem coeffMap_jqNModC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N] :
    coeffMap f (jqNModC R N) = jqNModC S N := by
  show coeffMap f (qExpand R N (jqModC R)) = qExpand S N (jqModC S)
  rw [coeffMap_qExpand, coeffMap_jqModC]

theorem residue_eq_one_of_pow_eq_one {L : Type*} [Field L] (q : ℕ) [hq : Fact q.Prime]
    (A : ValuationSubring L) (hA : A.LiesOverPrime q) (z : A) (hz : z ^ q = 1) :
    IsLocalRing.residue A z = 1 := by
  have hq' : q.Prime := hq.out
  have h0 : ((q : A) : L) ∈ A.nonunits := by
    have : ((q : A) : L) = (q : L) := by simp
    rw [this]; exact hA
  rw [ValuationSubring.coe_mem_nonunits_iff] at h0
  haveI : CharP (IsLocalRing.ResidueField A) q := (CharP.charP_iff_prime_eq_zero hq').2 (by
    rw [← map_natCast (IsLocalRing.residue A) q]
    exact (IsLocalRing.residue_eq_zero_iff _).2 h0)
  have h1 : (IsLocalRing.residue A z) ^ q = 1 := by rw [← map_pow, hz, map_one]
  have h2 : (IsLocalRing.residue A z - 1) ^ q = 0 := by rw [sub_pow_char, h1, one_pow, sub_self]
  exact sub_eq_zero.1 ((pow_eq_zero_iff hq'.ne_zero).1 h2)

theorem mem_of_pow_eq_one {L : Type*} [Field L] (A : ValuationSubring L) {z : L} {n : ℕ} (hn : n ≠ 0)
    (hz : z ^ n = 1) : z ∈ A := by
  rcases ValuationSubring.mem_or_inv_mem A z with h | h
  · exact h
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz
    have : z = z⁻¹ ^ m := by
      rw [pow_succ] at hz
      rw [inv_pow]
      exact eq_inv_of_mul_eq_one_right hz
    rw [this]; exact pow_mem h m

theorem isIntegral_inclusion_of_isKummerGenerator {κ Ω : Type*} [Field κ] [Field Ω] [Algebra κ Ω]
    (S₀ : Set Ω) {e : Ω} {n : ℕ} {E : IntermediateField κ Ω}
    (hK : ModularCurve.IgusaCover.IsKummerGenerator n (IntermediateField.adjoin κ S₀) e)
    (hE : ModularCurve.IgusaCover.igusaFunctionField (IntermediateField.adjoin κ S₀) e = E)
    (hle : IntermediateField.adjoin κ S₀ ≤ E) :
    (IntermediateField.inclusion hle).toRingHom.IsIntegral := by
  have heint : IsIntegral ↥(IntermediateField.adjoin κ S₀) e := by
    refine ⟨Polynomial.X ^ n - Polynomial.C (⟨e ^ n, hK.pow_mem⟩ : ↥(IntermediateField.adjoin κ S₀)),
      Polynomial.monic_X_pow_sub_C _ (Nat.pos_iff_ne_zero.1 hK.pos), ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
    exact sub_eq_zero.2 rfl
  haveI : FiniteDimensional ↥(IntermediateField.adjoin κ S₀)
      ↥(IntermediateField.adjoin ↥(IntermediateField.adjoin κ S₀) ({e} : Set Ω)) :=
    IntermediateField.adjoin.finiteDimensional heint
  have hsub : ∀ y : Ω, y ∈ E → y ∈ IntermediateField.adjoin ↥(IntermediateField.adjoin κ S₀) ({e} : Set Ω) := by
    intro y hy
    change y ∈ (IntermediateField.adjoin ↥(IntermediateField.adjoin κ S₀) ({e} : Set Ω)).restrictScalars κ
    rw [IntermediateField.adjoin_adjoin_left, IntermediateField.adjoin_union]
    rw [← hE, ModularCurve.IgusaCover.igusaFunctionField_eq_sup] at hy
    exact hy
  intro x
  have hx : IsIntegral ↥(IntermediateField.adjoin κ S₀)
      (⟨(x : Ω), hsub x x.2⟩ : ↥(IntermediateField.adjoin ↥(IntermediateField.adjoin κ S₀) ({e} : Set Ω))) :=
    Algebra.IsIntegral.isIntegral _
  have hxΩ : IsIntegral ↥(IntermediateField.adjoin κ S₀) (x : Ω) :=
    hx.map (IntermediateField.val (IntermediateField.adjoin ↥(IntermediateField.adjoin κ S₀) ({e} : Set Ω)))
  obtain ⟨p, hp, hpx⟩ := hxΩ
  refine ⟨p, hp, ?_⟩
  apply Subtype.ext
  have h := Polynomial.hom_eval₂ p (IntermediateField.inclusion hle).toRingHom E.val.toRingHom x
  rw [show (E.val.toRingHom.comp (IntermediateField.inclusion hle).toRingHom) =
      algebraMap ↥(IntermediateField.adjoin κ S₀) Ω from RingHom.ext fun _ => rfl] at h
  exact h.trans hpx

theorem qExpand_algebraMap {K : Type*} [Field K] (N : ℕ) [NeZero N] (c : K) :
    qExpand K N (algebraMap K (LaurentSeries K) c) = algebraMap K (LaurentSeries K) c := by
  have h : algebraMap K (LaurentSeries K) c = HahnSeries.single 0 c := by
    have h1 : algebraMap K (PowerSeries K) c = PowerSeries.C c := by simp
    rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
    rfl
  rw [h, qExpand_single, mul_zero]

end IgNodeAux

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem IgNode.eq_of_not_dvd
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
    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)

    (ℓ : CuspidalType.ProjLine q)
    {FI : Type} [Field FI] [Algebra (ResidueField A) FI]
    (Rg : RegularProlongation A (fieldBar q M') FI) (hRg : Rg.integers = OIg ℓ)
    (j : modularFunctionFieldC (ResidueField A) M' →+* FI)
    (hj : ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ Rg.integers,
        Rg.residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩))
    (s : ↥W) (b₁ b₂ : Place (ResidueField A) FI)
    (hb₁ : ∀ g : modularFunctionFieldC (ResidueField A) M',
      g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔ j g ∈ b₁.toValuationSubring)
    (hb₂ : ∀ g : modularFunctionFieldC (ResidueField A) M',
      g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔ j g ∈ b₂.toValuationSubring)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M')
    (hγO : OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (ha : ¬ (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0) : b₁ = b₂ := by

  obtain ⟨hKum, hE, -⟩ :=
    isKummerGenerator_eisensteinRatio_and_igusaFunctionField_eq_xHFunctionFieldC_levelH q hq M' hqM' A hA
  have hleE : modularFunctionFieldC (ResidueField A) M' ≤ xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M') := by
    rw [← hE]; exact ModularCurve.IgusaCover.le_igusaFunctionField _ _
  have hint : (IntermediateField.inclusion hleE).toRingHom.IsIntegral :=
    IgNodeAux.isIntegral_inclusion_of_isKummerGenerator _ hKum hE hleE

  obtain ⟨OIg', R, hRint, hpres', hres', -, -, -⟩ := exists_igusaValuationSubrings q hq M' hqM' A hA ζ
  have hO : OIg (lineInfty q) = OIg' (lineInfty q) := by
    ext f; rw [hIg_inf, hpres']
  set L := levelAutBar q M' ζ γ with hL
  have hmemℓ : ∀ f : ↥(fieldBar q M'), f ∈ Rg.integers ↔ L f ∈ R.integers := by
    intro f; rw [hRg, hγO, ValuationSubring.mem_comap, hRint, ← hO]; rfl

  let ψ : ↥Rg.integers ≃+* ↥R.integers :=
    { toFun := fun x => ⟨L x, (hmemℓ x).1 x.2⟩
      invFun := fun y => ⟨L.symm y, (hmemℓ _).2 (by rw [AlgEquiv.apply_symm_apply]; exact y.2)⟩
      left_inv := fun x => Subtype.ext (L.symm_apply_apply (x : ↥(fieldBar q M')))
      right_inv := fun y => Subtype.ext (L.apply_symm_apply (y : ↥(fieldBar q M')))
      map_mul' := fun x y => Subtype.ext (map_mul L _ _)
      map_add' := fun x y => Subtype.ext (map_add L _ _) }
  have hψ : ∀ x : ↥Rg.integers, ((ψ x : ↥R.integers) : ↥(fieldBar q M')) = L x := fun _ => rfl
  let φ : ↥Rg.integers →+* ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) := R.residue.comp ψ.toRingHom
  have hφ : ∀ x, φ x = R.residue (ψ x) := fun _ => rfl
  have hφsurj : Function.Surjective φ := R.residue_surjective.comp ψ.surjective
  have hker : RingHom.ker Rg.residue = RingHom.ker φ := by
    rw [Rg.ker_residue]; ext x
    rw [RingHom.mem_ker, hφ, ← RingHom.mem_ker, R.ker_residue, IsLocalRing.mem_maximalIdeal,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
    exact (MulEquiv.isUnit_map ψ.toMulEquiv (x := x)).not.symm

  let Θr : FI ≃+* ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) :=
    (RingHom.quotientKerEquivOfSurjective Rg.residue_surjective).symm.trans
      ((Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hφsurj))
  have hΘr : ∀ x : ↥Rg.integers, Θr (Rg.residue x) = φ x := by
    intro x
    simp only [Θr, RingEquiv.trans_apply, RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
  have hΘalg : ∀ c : ResidueField A, Θr (algebraMap (ResidueField A) FI c) = algebraMap (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) c := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    rw [← Rg.residue_algebraMap a, hΘr, hφ, ← R.residue_algebraMap a]
    congr 1
    exact Subtype.ext (by rw [hψ]; exact L.commutes (a : AlgebraicClosure ℚ))
  let Θ : FI ≃ₐ[ResidueField A] ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) := AlgEquiv.ofRingEquiv (f := Θr) hΘalg
  have hΘ : ∀ x : ↥Rg.integers, Θ (Rg.residue x) = R.residue (ψ x) := fun x => hΘr x

  have hΘint : (Θ.symm.toAlgHom : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) →ₐ[ResidueField A] FI).toRingHom.IsIntegral := by
    intro x
    have hx : x = (Θ.symm.toAlgHom : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) →ₐ[ResidueField A] FI).toRingHom (Θ x) := (Θ.symm_apply_apply x).symm
    rw [hx]; exact RingHom.isIntegralElem_map _
  let bE : Place (ResidueField A) FI → Place (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) := fun b =>
    b.restrictAlong (Θ.symm.toAlgHom) hΘint
  have hbE : ∀ (b : Place (ResidueField A) FI) (x : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))),
      x ∈ (bE b).toValuationSubring ↔ Θ.symm x ∈ b.toValuationSubring := fun b x => Iff.rfl
  have hbEinj : ∀ b c, bE b = bE c → b = c := by
    intro b c h
    ext x
    rw [← Θ.symm_apply_apply x, ← hbE, ← hbE, h]

  have hcomp : ∀ g : ↥(modularFunctionFieldC (ResidueField A) M'),
      Θ (j g) = IntermediateField.inclusion hleE g := by
    have hq' : q.Prime := Fact.out

    have hζq : ζ.val ^ q = 1 := ζ.isPrimitiveRoot.pow_eq_one
    obtain ⟨u, hu⟩ : ∃ u : (AlgebraicClosure ℚ)ˣ, (u : AlgebraicClosure ℚ) = ζ.val :=
      ⟨(ζ.isPrimitiveRoot.isUnit hq'.ne_zero).unit, IsUnit.unit_spec _⟩
    have hζA : ζ.val ∈ A := IgNodeAux.mem_of_pow_eq_one A hq'.ne_zero hζq
    have hζAq : (⟨ζ.val, hζA⟩ : ↥A) ^ q = 1 := Subtype.ext (by simpa using hζq)
    have hζAu : IsUnit (⟨ζ.val, hζA⟩ : ↥A) := IsUnit.of_pow_eq_one hζAq hq'.ne_zero
    set uA : (↥A)ˣ := hζAu.unit with huAdef
    have huA : Units.map (A.subtype : ↥A →* AlgebraicClosure ℚ) uA = u :=
      Units.ext (by rw [Units.coe_map, huAdef, IsUnit.unit_spec, hu]; rfl)
    have huA1 : Units.map (IsLocalRing.residue ↥A : ↥A →* ResidueField A) uA = 1 :=
      Units.ext (by rw [Units.coe_map, huAdef, IsUnit.unit_spec, Units.val_one];
                     exact IgNodeAux.residue_eq_one_of_pow_eq_one q A hA _ hζAq)

    obtain ⟨k, hk⟩ := exists_coe_levelAutBar_apply_eq_qTwist_of_not_dvd_of_mem_laurentBaseChange_gamma0
      q M' hqM' ζ γ hγ ha u hu
    have hmono : ∀ {x : LaurentSeries (AlgebraicClosure ℚ)}, x ∈ modularFunctionFieldBar M' →
        x ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) := by
      intro x hx
      refine IntermediateField.adjoin.mono _ _ _ (Set.image_mono ?_) hx
      intro z hz
      exact modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ M' (by rw [modularFunctionFieldFullC_rat]; exact hz)

    let f₁ : ↥(modularFunctionFieldC (ResidueField A) M') →+* LaurentSeries (ResidueField A) :=
      (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')).val.toRingHom.comp
        ((Θ.toAlgHom.toRingHom).comp j)
    let f₂ : ↥(modularFunctionFieldC (ResidueField A) M') →+* LaurentSeries (ResidueField A) :=
      (modularFunctionFieldC (ResidueField A) M').val.toRingHom
    have hf₁ : ∀ g, f₁ g = ((Θ (j g) : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) := fun _ => rfl
    have hf₂ : ∀ g, f₂ g = (g : LaurentSeries (ResidueField A)) := fun _ => rfl
    let f₀ : ↥(modularFunctionFieldC (ResidueField A) M') →+* LaurentSeries (ResidueField A) :=
      (modularFunctionFieldC (ResidueField A) M').val.toRingHom
    suffices H : ∀ g, f₁ g = f₂ g by
      intro g; apply Subtype.ext; have := H g; rw [hf₁, hf₂] at this
      rw [this, IntermediateField.coe_inclusion]

    have hgen : ∀ (y : LaurentSeries ↥A) (hyQ : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
        ∃ hI : (⟨coeffMap A.subtype y, hyQ⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
          ((R₀.residue ⟨_, hI⟩ : ↥(modularFunctionFieldC (ResidueField A) M')) : LaurentSeries (ResidueField A)) =
              coeffMap (IsLocalRing.residue ↥A) y ∧
          f₁ (R₀.residue ⟨_, hI⟩) = coeffMap (IsLocalRing.residue ↥A) y := by
      intro y hyQ
      obtain ⟨hI, hresI⟩ := hR₀ y hyQ
      refine ⟨hI, hresI, ?_⟩
      obtain ⟨hC, hjC⟩ := hj ⟨coeffMap A.subtype y, hyQ⟩ hI
      rw [hf₁, ← hjC, hΘ]
      have hLy : ((L (IntermediateField.inclusion hle ⟨coeffMap A.subtype y, hyQ⟩) : ↥(fieldBar q M')) :
          LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (qTwist (uA ^ k) y) := by
        rw [hk (coeffMap A.subtype y) (hmono hyQ) _ rfl, IgNodeAux.coeffMap_qTwist, map_zpow, huA]
      obtain ⟨hO', hresO⟩ := hres' (qTwist (uA ^ k) y) (by rw [← hLy]; exact SetLike.coe_mem _)
      have hψy : ψ ⟨_, hC⟩ = ⟨⟨coeffMap A.subtype (qTwist (uA ^ k) y), _⟩, hO'⟩ := Subtype.ext (Subtype.ext hLy)
      rw [hψy, hresO, IgNodeAux.coeffMap_qTwist, map_zpow, huA1, one_zpow, qTwist_one_apply]

    have hJ1mem : jqModC (AlgebraicClosure ℚ) ∈ modularFunctionFieldBar M' := by
      have h : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) :=
        IgNodeAux.coeffMap_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))
      exact h ▸ coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))
    have hJ2mem : jqNModC (AlgebraicClosure ℚ) M' ∈ modularFunctionFieldBar M' := by
      have h : coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq) = jqNModC (AlgebraicClosure ℚ) M' :=
        IgNodeAux.coeffMap_jqNModC (algebraMap ℚ (AlgebraicClosure ℚ)) M'
      exact h ▸ coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jqN_mem M'))
    have hy1 : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar M' := by
      rw [IgNodeAux.coeffMap_jqModC]; exact hJ1mem
    have hy2 : coeffMap A.subtype (jqNModC ↥A M') ∈ modularFunctionFieldBar M' := by
      rw [IgNodeAux.coeffMap_jqNModC]; exact hJ2mem
    obtain ⟨hI1, hres1, hf1⟩ := hgen (jqModC ↥A) hy1
    obtain ⟨hI2, hres2, hf2⟩ := hgen (jqNModC ↥A M') hy2
    set J1 : ↥(modularFunctionFieldC (ResidueField A) M') := ⟨jqModC (ResidueField A), jqModC_mem _ M'⟩ with hJ1
    set J2 : ↥(modularFunctionFieldC (ResidueField A) M') := ⟨jqNModC (ResidueField A) M', jqNModC_mem _ M'⟩ with hJ2
    have hR1 : R₀.residue ⟨_, hI1⟩ = J1 := Subtype.ext (hres1.trans (IgNodeAux.coeffMap_jqModC _))
    have hR2 : R₀.residue ⟨_, hI2⟩ = J2 := Subtype.ext (hres2.trans (IgNodeAux.coeffMap_jqNModC _ _))

    intro g
    have hcl : g ∈ Subfield.closure (Set.range (algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')) ∪ {J1, J2}) := by
      have hg : (g : LaurentSeries (ResidueField A)) ∈ Subfield.closure
          (Set.range (algebraMap (ResidueField A) (LaurentSeries (ResidueField A))) ∪
            {jqModC (ResidueField A), jqNModC (ResidueField A) M'}) := g.2
      have hmap : (Subfield.closure (Set.range (algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')) ∪ {J1, J2})).map f₀ =
          Subfield.closure (Set.range (algebraMap (ResidueField A) (LaurentSeries (ResidueField A))) ∪
            {jqModC (ResidueField A), jqNModC (ResidueField A) M'}) := by
        rw [RingHom.map_field_closure, Set.image_union, Set.image_insert_eq, Set.image_singleton, ← Set.range_comp]
        rfl
      rw [← hmap, Subfield.mem_map] at hg
      obtain ⟨g', hg', hgg'⟩ := hg
      have : g' = g := Subtype.ext hgg'
      exact this ▸ hg'
    refine RingHom.eqOn_field_closure ?_ hcl
    rintro x (⟨c, rfl⟩ | hx)
    ·
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
      have h0 := R₀.residue_algebraMap a
      obtain ⟨hC, hjC⟩ := hj _ ((R₀.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2)
      show f₁ _ = f₂ _
      rw [hf₁, hf₂, ← h0, ← hjC]
      have h1 : (⟨IntermediateField.inclusion hle (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (a : AlgebraicClosure ℚ)), hC⟩ : ↥Rg.integers) =
          ⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : AlgebraicClosure ℚ), (Rg.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2⟩ :=
        Subtype.ext (Subtype.ext rfl)
      rw [h1, Rg.residue_algebraMap, AlgEquiv.commutes, h0]
      rfl
    · rcases hx with rfl | hx
      · show f₁ J1 = f₂ J1
        rw [hf₂, ← hR1, hf1]; exact hres1.symm
      · rw [Set.mem_singleton_iff] at hx; subst hx
        show f₁ J2 = f₂ J2
        rw [hf₂, ← hR2, hf2]; exact hres2.symm

  have hover : ∀ b : Place (ResidueField A) FI,
      (∀ g : ↥(modularFunctionFieldC (ResidueField A) M'),
        g ∈ (s : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
          j g ∈ b.toValuationSubring) →
      (bE b).restrictAlong (IntermediateField.inclusion hleE) hint = (s : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')) := by
    intro b hb
    ext g
    rw [show ((bE b).restrictAlong (IntermediateField.inclusion hleE) hint).toValuationSubring =
        (bE b).toValuationSubring.comap (IntermediateField.inclusion hleE).toRingHom from rfl,
      ValuationSubring.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hbE, hb, ← hcomp g,
      AlgEquiv.symm_apply_apply]
  obtain ⟨w, -, huniq⟩ := existsUnique_place_restrictAlong_eq_of_mem_ssPlaces q hq M' hqM' A hA hleE hint
    (s : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')) ((hW _).1 s.2)
  exact hbEinj _ _ ((huniq _ (hover b₁ hb₁)).trans (huniq _ (hover b₂ hb₂)).symm)

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem IgNode.eq_of_dvd
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
    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)

    (ℓ : CuspidalType.ProjLine q)
    {FI : Type} [Field FI] [Algebra (ResidueField A) FI]
    (Rg : RegularProlongation A (fieldBar q M') FI) (hRg : Rg.integers = OIg ℓ)
    (j : modularFunctionFieldC (ResidueField A) M' →+* FI)
    (hj : ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ Rg.integers,
        Rg.residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩))
    (s : ↥W) (b₁ b₂ : Place (ResidueField A) FI)
    (hb₁ : ∀ g : modularFunctionFieldC (ResidueField A) M',
      g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔ j g ∈ b₁.toValuationSubring)
    (hb₂ : ∀ g : modularFunctionFieldC (ResidueField A) M',
      g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔ j g ∈ b₂.toValuationSubring)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M')
    (hγO : OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (ha : (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0) : b₁ = b₂ := by

  obtain ⟨hKum, hE, -⟩ :=
    isKummerGenerator_eisensteinRatio_and_igusaFunctionField_eq_xHFunctionFieldC_levelH q hq M' hqM' A hA
  have hleE : modularFunctionFieldC (ResidueField A) M' ≤ xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M') := by
    rw [← hE]; exact ModularCurve.IgusaCover.le_igusaFunctionField _ _
  have hint : (IntermediateField.inclusion hleE).toRingHom.IsIntegral :=
    IgNodeAux.isIntegral_inclusion_of_isKummerGenerator _ hKum hE hleE

  obtain ⟨OIg', R, hRint, hpres', hres', -, -, -⟩ := exists_igusaValuationSubrings q hq M' hqM' A hA ζ
  have hO : OIg (lineInfty q) = OIg' (lineInfty q) := by
    ext f; rw [hIg_inf, hpres']
  set L := levelAutBar q M' ζ γ with hL
  have hmemℓ : ∀ f : ↥(fieldBar q M'), f ∈ Rg.integers ↔ L f ∈ R.integers := by
    intro f; rw [hRg, hγO, ValuationSubring.mem_comap, hRint, ← hO]; rfl

  let ψ : ↥Rg.integers ≃+* ↥R.integers :=
    { toFun := fun x => ⟨L x, (hmemℓ x).1 x.2⟩
      invFun := fun y => ⟨L.symm y, (hmemℓ _).2 (by rw [AlgEquiv.apply_symm_apply]; exact y.2)⟩
      left_inv := fun x => Subtype.ext (L.symm_apply_apply (x : ↥(fieldBar q M')))
      right_inv := fun y => Subtype.ext (L.apply_symm_apply (y : ↥(fieldBar q M')))
      map_mul' := fun x y => Subtype.ext (map_mul L _ _)
      map_add' := fun x y => Subtype.ext (map_add L _ _) }
  have hψ : ∀ x : ↥Rg.integers, ((ψ x : ↥R.integers) : ↥(fieldBar q M')) = L x := fun _ => rfl
  let φ : ↥Rg.integers →+* ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) := R.residue.comp ψ.toRingHom
  have hφ : ∀ x, φ x = R.residue (ψ x) := fun _ => rfl
  have hφsurj : Function.Surjective φ := R.residue_surjective.comp ψ.surjective
  have hker : RingHom.ker Rg.residue = RingHom.ker φ := by
    rw [Rg.ker_residue]; ext x
    rw [RingHom.mem_ker, hφ, ← RingHom.mem_ker, R.ker_residue, IsLocalRing.mem_maximalIdeal,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
    exact (MulEquiv.isUnit_map ψ.toMulEquiv (x := x)).not.symm

  let Θr : FI ≃+* ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) :=
    (RingHom.quotientKerEquivOfSurjective Rg.residue_surjective).symm.trans
      ((Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hφsurj))
  have hΘr : ∀ x : ↥Rg.integers, Θr (Rg.residue x) = φ x := by
    intro x
    simp only [Θr, RingEquiv.trans_apply, RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
  have hΘalg : ∀ c : ResidueField A, Θr (algebraMap (ResidueField A) FI c) = algebraMap (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) c := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    rw [← Rg.residue_algebraMap a, hΘr, hφ, ← R.residue_algebraMap a]
    congr 1
    exact Subtype.ext (by rw [hψ]; exact L.commutes (a : AlgebraicClosure ℚ))
  let Θ : FI ≃ₐ[ResidueField A] ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) := AlgEquiv.ofRingEquiv (f := Θr) hΘalg
  have hΘ : ∀ x : ↥Rg.integers, Θ (Rg.residue x) = R.residue (ψ x) := fun x => hΘr x

  have hΘint : (Θ.symm.toAlgHom : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) →ₐ[ResidueField A] FI).toRingHom.IsIntegral := by
    intro x
    have hx : x = (Θ.symm.toAlgHom : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) →ₐ[ResidueField A] FI).toRingHom (Θ x) := (Θ.symm_apply_apply x).symm
    rw [hx]; exact RingHom.isIntegralElem_map _
  let bE : Place (ResidueField A) FI → Place (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) := fun b =>
    b.restrictAlong (Θ.symm.toAlgHom) hΘint
  have hbE : ∀ (b : Place (ResidueField A) FI) (x : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))),
      x ∈ (bE b).toValuationSubring ↔ Θ.symm x ∈ b.toValuationSubring := fun b x => Iff.rfl
  have hbEinj : ∀ b c, bE b = bE c → b = c := by
    intro b c h
    ext x
    rw [← Θ.symm_apply_apply x, ← hbE, ← hbE, h]

  have hcomp : ∀ g : ↥(modularFunctionFieldC (ResidueField A) M'),
      ((Θ (j g) : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) =
        qExpand (ResidueField A) (q ^ 2) (g : LaurentSeries (ResidueField A)) := by
    have hq' : q.Prime := Fact.out
    have hmono : ∀ {x : LaurentSeries (AlgebraicClosure ℚ)}, x ∈ modularFunctionFieldBar M' →
        x ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) := by
      intro x hx
      refine IntermediateField.adjoin.mono _ _ _ (Set.image_mono ?_) hx
      intro z hz
      exact modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ M' (by rw [modularFunctionFieldFullC_rat]; exact hz)

    let f₁ : ↥(modularFunctionFieldC (ResidueField A) M') →+* LaurentSeries (ResidueField A) :=
      (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')).val.toRingHom.comp
        ((Θ.toAlgHom.toRingHom).comp j)
    let f₂ : ↥(modularFunctionFieldC (ResidueField A) M') →+* LaurentSeries (ResidueField A) :=
      (qExpand (ResidueField A) (q ^ 2)).comp (modularFunctionFieldC (ResidueField A) M').val.toRingHom
    have hf₁ : ∀ g, f₁ g = ((Θ (j g) : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) := fun _ => rfl
    have hf₂ : ∀ g, f₂ g = qExpand (ResidueField A) (q ^ 2) (g : LaurentSeries (ResidueField A)) := fun _ => rfl
    let f₀ : ↥(modularFunctionFieldC (ResidueField A) M') →+* LaurentSeries (ResidueField A) :=
      (modularFunctionFieldC (ResidueField A) M').val.toRingHom
    suffices H : ∀ g, f₁ g = f₂ g by
      intro g; have := H g; rw [hf₁, hf₂] at this; exact this

    have hgen : ∀ (y : LaurentSeries ↥A) (hyQ : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
        ∃ hI : (⟨coeffMap A.subtype y, hyQ⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
          ((R₀.residue ⟨_, hI⟩ : ↥(modularFunctionFieldC (ResidueField A) M')) : LaurentSeries (ResidueField A)) =
              coeffMap (IsLocalRing.residue ↥A) y ∧
          f₁ (R₀.residue ⟨_, hI⟩) = qExpand (ResidueField A) (q ^ 2) (coeffMap (IsLocalRing.residue ↥A) y) := by
      intro y hyQ
      obtain ⟨hI, hresI⟩ := hR₀ y hyQ
      refine ⟨hI, hresI, ?_⟩
      obtain ⟨hC, hjC⟩ := hj ⟨coeffMap A.subtype y, hyQ⟩ hI
      rw [hf₁, ← hjC, hΘ]
      have hLy : ((L (IntermediateField.inclusion hle ⟨coeffMap A.subtype y, hyQ⟩) : ↥(fieldBar q M')) :
          LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (qExpand ↥A (q ^ 2) y) := by
        rw [coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0 q M' hqM' ζ γ hγ ha
          (coeffMap A.subtype y) (hmono hyQ) _ rfl, IgNodeAux.coeffMap_qExpand]
      obtain ⟨hO', hresO⟩ := hres' (qExpand ↥A (q ^ 2) y) (by rw [← hLy]; exact SetLike.coe_mem _)
      have hψy : ψ ⟨_, hC⟩ = ⟨⟨coeffMap A.subtype (qExpand ↥A (q ^ 2) y), _⟩, hO'⟩ := Subtype.ext (Subtype.ext hLy)
      rw [hψy, hresO, IgNodeAux.coeffMap_qExpand]

    have hJ1mem : jqModC (AlgebraicClosure ℚ) ∈ modularFunctionFieldBar M' := by
      have h : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) :=
        IgNodeAux.coeffMap_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))
      exact h ▸ coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))
    have hJ2mem : jqNModC (AlgebraicClosure ℚ) M' ∈ modularFunctionFieldBar M' := by
      have h : coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq) = jqNModC (AlgebraicClosure ℚ) M' :=
        IgNodeAux.coeffMap_jqNModC (algebraMap ℚ (AlgebraicClosure ℚ)) M'
      exact h ▸ coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jqN_mem M'))
    have hy1 : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar M' := by
      rw [IgNodeAux.coeffMap_jqModC]; exact hJ1mem
    have hy2 : coeffMap A.subtype (jqNModC ↥A M') ∈ modularFunctionFieldBar M' := by
      rw [IgNodeAux.coeffMap_jqNModC]; exact hJ2mem
    obtain ⟨hI1, hres1, hf1⟩ := hgen (jqModC ↥A) hy1
    obtain ⟨hI2, hres2, hf2⟩ := hgen (jqNModC ↥A M') hy2
    set J1 : ↥(modularFunctionFieldC (ResidueField A) M') := ⟨jqModC (ResidueField A), jqModC_mem _ M'⟩ with hJ1
    set J2 : ↥(modularFunctionFieldC (ResidueField A) M') := ⟨jqNModC (ResidueField A) M', jqNModC_mem _ M'⟩ with hJ2
    have hR1 : R₀.residue ⟨_, hI1⟩ = J1 := Subtype.ext (hres1.trans (IgNodeAux.coeffMap_jqModC _))
    have hR2 : R₀.residue ⟨_, hI2⟩ = J2 := Subtype.ext (hres2.trans (IgNodeAux.coeffMap_jqNModC _ _))

    intro g
    have hcl : g ∈ Subfield.closure (Set.range (algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')) ∪ {J1, J2}) := by
      have hg : (g : LaurentSeries (ResidueField A)) ∈ Subfield.closure
          (Set.range (algebraMap (ResidueField A) (LaurentSeries (ResidueField A))) ∪
            {jqModC (ResidueField A), jqNModC (ResidueField A) M'}) := g.2
      have hmap : (Subfield.closure (Set.range (algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')) ∪ {J1, J2})).map f₀ =
          Subfield.closure (Set.range (algebraMap (ResidueField A) (LaurentSeries (ResidueField A))) ∪
            {jqModC (ResidueField A), jqNModC (ResidueField A) M'}) := by
        rw [RingHom.map_field_closure, Set.image_union, Set.image_insert_eq, Set.image_singleton, ← Set.range_comp]
        rfl
      rw [← hmap, Subfield.mem_map] at hg
      obtain ⟨g', hg', hgg'⟩ := hg
      have : g' = g := Subtype.ext hgg'
      exact this ▸ hg'
    refine RingHom.eqOn_field_closure ?_ hcl
    rintro x (⟨c, rfl⟩ | hx)
    ·
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
      have h0 := R₀.residue_algebraMap a
      obtain ⟨hC, hjC⟩ := hj _ ((R₀.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2)
      show f₁ _ = f₂ _
      rw [hf₁, hf₂, ← h0, ← hjC]
      have h1 : (⟨IntermediateField.inclusion hle (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (a : AlgebraicClosure ℚ)), hC⟩ : ↥Rg.integers) =
          ⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : AlgebraicClosure ℚ), (Rg.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2⟩ :=
        Subtype.ext (Subtype.ext rfl)
      rw [h1, Rg.residue_algebraMap, AlgEquiv.commutes, h0]
      show algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) _ =
        qExpand (ResidueField A) (q ^ 2) (algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) _)
      rw [IgNodeAux.qExpand_algebraMap]
    · rcases hx with rfl | hx
      · show f₁ J1 = f₂ J1
        rw [hf₂, ← hR1, hf1]; exact congrArg _ hres1.symm
      · rw [Set.mem_singleton_iff] at hx; subst hx
        show f₁ J2 = f₂ J2
        rw [hf₂, ← hR2, hf2]; exact congrArg _ hres2.symm

  have hover : ∀ b : Place (ResidueField A) FI,
      (∀ g : ↥(modularFunctionFieldC (ResidueField A) M'),
        g ∈ (s : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
          j g ∈ b.toValuationSubring) →
      ∀ (g : ↥(modularFunctionFieldC (ResidueField A) M')) (g' : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))),
        (g' : LaurentSeries (ResidueField A)) = qExpand (ResidueField A) (q ^ 2) (g : LaurentSeries (ResidueField A)) →
        (g ∈ (s : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
          g' ∈ (bE b).toValuationSubring) := by
    intro b hb g g' hg'
    have hgj : g' = Θ (j g) := Subtype.ext (hg'.trans (hcomp g).symm)
    rw [hgj, hbE, AlgEquiv.symm_apply_apply]
    exact hb g
  obtain ⟨w, -, huniq⟩ := existsUnique_place_forall_mem_iff_mem_of_coe_eq_qExpand_sq_of_mem_ssPlaces q hq M' hqM' A hA
    hleE hint (s : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')) ((hW _).1 s.2)
  exact hbEinj _ _ ((huniq _ (hover b₁ hb₁)).trans (huniq _ (hover b₂ hb₂)).symm)

set_option maxHeartbeats 1600000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (ModularCurve.modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (ModularCurve.modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : ModularCurve.modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)

    (ℓ : CuspidalType.ProjLine q)
    {FI : Type} [Field FI] [Algebra (ResidueField A) FI]
    (Rg : RegularProlongation A (fieldBar q M') FI) (hRg : Rg.integers = OIg ℓ)
    (j : ModularCurve.modularFunctionFieldC (ResidueField A) M' →+* FI)
    (hj : ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ Rg.integers,
        Rg.residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩))
    (s : ↥W) (b₁ b₂ : Place (ResidueField A) FI)
    (hb₁ : ∀ g : ModularCurve.modularFunctionFieldC (ResidueField A) M',
      g ∈ (s : Place (ResidueField A) (ModularCurve.modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔ j g ∈ b₁.toValuationSubring)
    (hb₂ : ∀ g : ModularCurve.modularFunctionFieldC (ResidueField A) M',
      g ∈ (s : Place (ResidueField A) (ModularCurve.modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔ j g ∈ b₂.toValuationSubring) :
    b₁ = b₂ := by
  obtain ⟨γ, hγ, -, hγO⟩ := hIg ℓ
  by_cases ha : (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  · exact IgNode.eq_of_dvd q hq M' hqM' A hA W hW hle R₀ hR₀ ζ OIg hIg_inf hIg ℓ Rg hRg j hj s b₁ b₂ hb₁ hb₂ γ hγ hγO ha
  · exact IgNode.eq_of_not_dvd q hq M' hqM' A hA W hW hle R₀ hR₀ ζ OIg hIg_inf hIg ℓ Rg hRg j hj s b₁ b₂ hb₁ hb₂ γ hγ hγO ha

end S_ModularCurve_FullLevel_eq_of_forall_mem_iff_map_mem_of_integers_eq_igusaRing
end P2MW
export P2MW.S_ModularCurve_FullLevel_eq_of_forall_mem_iff_map_mem_of_integers_eq_igusaRing (solution)
