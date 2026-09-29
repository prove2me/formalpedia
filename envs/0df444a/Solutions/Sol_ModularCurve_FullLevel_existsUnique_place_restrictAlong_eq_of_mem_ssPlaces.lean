-- Prove2me | solution 1 for ModularCurve.FullLevel.existsUnique_place_restrictAlong_eq_of_mem_ssPlaces
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/88c6291c-568d-5542-8a4a-43ab83358fd5

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Correspondence

import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_IgusaFunctionField
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_ModularCurve_FullLevel_isKummerGenerator_eisensteinRatio_and_igusaFunctionField_eq_xHFunctionFieldC_levelH
import Theorems.Thm_ModularCurve_FullLevel_ramificationIndex_xHFunctionFieldC_levelH_modularFunctionFieldC_eq_of_liesOverPrime
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_eq_finrank
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_existsUnique_place_restrictAlong_eq_of_mem_ssPlaces
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms"
p2m_attr_erase "instance" "CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex"
p2m_attr_erase "simp" "ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆"
p2m_attr_erase "simp" "TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate"
p2m_attr_erase "simp" "ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace I2RamAux

open IntermediateField Polynomial

theorem isSplittingField_igusaFunctionField
    {κ : Type} [Field κ] {Ω : Type} [Field Ω] [Algebra κ Ω]
    (K₀ : IntermediateField κ Ω) (a : Ω) (n : ℕ) (hn : n ≠ 0) {ζ : κ} (hζ : IsPrimitiveRoot ζ n)
    (c : ↥K₀) (hc : (c : Ω) = a ^ n) :
    letI : Algebra ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) :=
      (IntermediateField.inclusion (IgusaCover.le_igusaFunctionField K₀ a)).toRingHom.toAlgebra
    IsSplittingField ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) (X ^ n - C c) := by
  letI algI : Algebra ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) :=
    (IntermediateField.inclusion (IgusaCover.le_igusaFunctionField K₀ a)).toRingHom.toAlgebra
  have hroot : aeval a (X ^ n - C c) = 0 := by simp [hc]
  have hint : IsIntegral ↥K₀ a := ⟨_, monic_X_pow_sub_C c hn, by rw [← aeval_def]; exact hroot⟩
  have hE : K₀⟮a⟯ = extendScalars (IgusaCover.le_igusaFunctionField K₀ a) := by
    apply le_antisymm
    · rw [adjoin_le_iff, Set.singleton_subset_iff]
      rw [SetLike.mem_coe, mem_extendScalars]
      exact IgusaCover.mem_igusaFunctionField K₀ a
    · intro x hx
      rw [mem_extendScalars] at hx
      change x ∈ (K₀⟮a⟯).restrictScalars κ
      revert x hx
      change IgusaCover.igusaFunctionField K₀ a ≤ (K₀⟮a⟯).restrictScalars κ
      unfold IgusaCover.igusaFunctionField
      rw [adjoin_le_iff]
      rintro y (hy | rfl)
      · exact (K₀⟮a⟯).algebraMap_mem ⟨y, hy⟩
      · exact mem_adjoin_simple_self ↥K₀ y
  haveI : IsScalarTower ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) Ω :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let α : ↥(IgusaCover.igusaFunctionField K₀ a) := ⟨a, IgusaCover.mem_igusaFunctionField K₀ a⟩
  have hα : α ^ n = algebraMap ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) c := by
    apply Subtype.ext
    show ((α ^ n : ↥(IgusaCover.igusaFunctionField K₀ a)) : Ω) =
      ((IntermediateField.inclusion (IgusaCover.le_igusaFunctionField K₀ a) c :
        ↥(IgusaCover.igusaFunctionField K₀ a)) : Ω)
    rw [IntermediateField.coe_inclusion, hc]
    simp [α]
  constructor
  · have hζI : IsPrimitiveRoot (algebraMap ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) (algebraMap κ ↥K₀ ζ)) n :=
      (hζ.map_of_injective (algebraMap κ ↥K₀).injective).map_of_injective
        (algebraMap ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a)).injective
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    exact X_pow_sub_C_splits_of_isPrimitiveRoot hζI hα
  · have hS : Algebra.adjoin ↥K₀ {α} = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx1 : (x : Ω) ∈ K₀⟮a⟯ := by
        rw [hE, mem_extendScalars]
        exact x.2
      have hx2 : (x : Ω) ∈ (Algebra.adjoin ↥K₀ {α}).map
          (IsScalarTower.toAlgHom ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) Ω) := by
        rw [AlgHom.map_adjoin, Set.image_singleton]
        change (x : Ω) ∈ Algebra.adjoin ↥K₀ {a}
        rw [← adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
        exact hx1
      obtain ⟨y, hy, hyx⟩ := Subalgebra.mem_map.mp hx2
      have : y = x := Subtype.ext hyx
      rwa [← this]
    rw [eq_top_iff, ← hS]
    apply Algebra.adjoin_mono
    rw [Set.singleton_subset_iff, mem_rootSet_of_ne (X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) c)]
    rw [map_sub, map_pow, aeval_X, aeval_C, hα, sub_self]

theorem finiteIndex_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)

end I2RamAux

namespace I2RamAux
open IntermediateField Polynomial

theorem package
    {κ : Type} [Field κ] [IsAlgClosed κ] {Ω : Type} [Field Ω] [Algebra κ Ω]
    (K₀ E : IntermediateField κ Ω) (a : Ω) (n : ℕ) (hn : (n : κ) ≠ 0)
    (hK : IgusaCover.IsKummerGenerator n K₀ a) (hE : IgusaCover.igusaFunctionField K₀ a = E)
    (hrel : K₀.relfinrank E = n) (hle : K₀ ≤ E) :
    letI : Algebra ↥K₀ ↥E := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    IsScalarTower κ ↥K₀ ↥E ∧ FiniteDimensional ↥K₀ ↥E ∧ Algebra.IsSeparable ↥K₀ ↥E ∧ Module.finrank ↥K₀ ↥E = n := by
  subst hE
  letI alg : Algebra ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) :=
    (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI hst : IsScalarTower κ ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (by simp)
  haveI : NeZero ((n : ℕ) : κ) := ⟨hn⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot κ n
  set b : ↥K₀ := ⟨a ^ n, hK.pow_mem⟩ with hbdef
  haveI hsplit : IsSplittingField ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) (X ^ n - C b) :=
    isSplittingField_igusaFunctionField K₀ a n hn0 hζ b rfl
  have hdeg : Module.finrank ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) = n := by
    show Module.finrank ↥K₀ ↥(extendScalars (IgusaCover.le_igusaFunctionField K₀ a)) = n
    rw [← relfinrank_eq_finrank_of_le]
    exact hrel
  haveI hfd : FiniteDimensional ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) :=
    Module.finite_of_finrank_pos (by rw [hdeg]; exact Nat.pos_of_ne_zero hn0)
  have hb : b ≠ 0 := by
    intro h
    have h' : (a ^ n : Ω) = 0 := by
      have := congrArg Subtype.val h
      simpa [hbdef] using this
    exact hK.ne_zero ((pow_eq_zero_iff hn0).mp h')
  have hnK : ((n : ℕ) : ↥K₀) ≠ 0 := by
    intro h
    apply hn
    have h' : algebraMap κ ↥K₀ (n : κ) = 0 := by rwa [map_natCast]
    exact (map_eq_zero_iff _ (algebraMap κ ↥K₀).injective).mp h'
  haveI : IsGalois ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) :=
    IsGalois.of_separable_splitting_field (p := X ^ n - C b) (Polynomial.separable_X_pow_sub_C b hnK hb)
  exact ⟨hst, hfd, inferInstance, hdeg⟩

end I2RamAux

set_option maxHeartbeats 3200000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (hle : modularFunctionFieldC (ResidueField A) M' ≤ xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))
    (hint : RingHom.IsIntegral (IntermediateField.inclusion hle).toRingHom)
    (s : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M'))
    (hs : s ∈ ssPlaces q M' (ResidueField A)) :
    ∃! w : Place (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')),
      w.restrictAlong (IntermediateField.inclusion hle) hint = s := by
  classical

  haveI hAC : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  haveI hch : CharP (ResidueField A) q :=
    ValuationSubring.residueField_charP_of_liesOverPrime A (Fact.out : q.Prime) hA
  have hq5 : 5 ≤ q := hq
  have hnpos : 0 < (q - 1) / 2 := by omega
  have hnlt : (q - 1) / 2 < q := by omega
  have hn : (((q - 1) / 2 : ℕ) : ResidueField A) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff (ResidueField A) q] at h
    exact absurd (Nat.eq_zero_of_dvd_of_lt h hnlt) (by omega)

  obtain ⟨hK, hIg, hrel⟩ :=
    ModularCurve.FullLevel.isKummerGenerator_eisensteinRatio_and_igusaFunctionField_eq_xHFunctionFieldC_levelH
      q hq M' hqM' A hA
  letI alg : Algebra ↥(modularFunctionFieldC (ResidueField A) M') ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  obtain ⟨hst, hfd, hsep, hdeg⟩ := I2RamAux.package (κ := ResidueField A)
    (modularFunctionFieldC (ResidueField A) M')
    (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) _ ((q - 1) / 2) hn hK hIg hrel hle
  haveI := hst
  haveI := hfd
  haveI := hsep

  haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
  haveI : (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')).FiniteIndex :=
    I2RamAux.finiteIndex_gammaH (q ^ 2 * M') (levelH q M')
  haveI hcurve : IsCurveOver (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) :=
    ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed (ResidueField A)
      (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) (ModularCurve.translation_mem_GammaH _ _)

  have hrats : s.IsRational :=
    (Place.isRational_iff_deg_eq_one s).mpr (ModularCurve.place_deg_eq_one_of_isAlgClosed (ResidueField A) M' s)
  have hratw : ∀ w : Place (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), w.IsRational := fun w =>
    (Place.isRational_iff_deg_eq_one w).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed w)

  have hsum := Place.sum_ramificationIndex_eq_finrank (F' := ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) s hrats (fun w _ => hratw w)
  rw [hdeg] at hsum

  have hram : ∀ w ∈ s.fiber ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), (w.ramificationIndex ↥(modularFunctionFieldC (ResidueField A) M') : ℤ) = (((q - 1) / 2 : ℕ) : ℤ) := by
    intro w hw
    have hwv : w.restrict ↥(modularFunctionFieldC (ResidueField A) M') = s := Place.mem_fiber.mp hw
    have hwv' : Place.restrictAlong (IntermediateField.inclusion hle) hint w = s := hwv
    have hsw : Place.restrictAlong (IntermediateField.inclusion hle) hint w ∈ ssPlaces q M' (ResidueField A) := by
      rw [hwv']; exact hs
    have hC2 := (ModularCurve.FullLevel.ramificationIndex_xHFunctionFieldC_levelH_modularFunctionFieldC_eq_of_liesOverPrime
      q hq M' hqM' A hA hle hint w).1 hsw
    exact_mod_cast hC2

  have hne : (s.fiber ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hsum
    have : (0 : ℤ) < (((q - 1) / 2 : ℕ) : ℤ) := by exact_mod_cast hnpos
    omega
  obtain ⟨w₀, hw₀⟩ := hne
  have hw₀' : w₀.restrict ↥(modularFunctionFieldC (ResidueField A) M') = s := Place.mem_fiber.mp hw₀
  refine ⟨w₀, hw₀', ?_⟩

  intro w hw
  have hw' : w.restrict ↥(modularFunctionFieldC (ResidueField A) M') = s := hw
  have hwf : w ∈ s.fiber ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) := Place.mem_fiber.mpr hw'
  by_contra hne'
  have hsub : ({w, w₀} : Finset (Place (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))) ⊆ s.fiber ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hwf
    · rw [Finset.mem_singleton] at hx; subst hx; exact hw₀
  have hle2 := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun x : Place (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) => (x.ramificationIndex ↥(modularFunctionFieldC (ResidueField A) M') : ℤ))
    (fun x _ _ => Int.natCast_nonneg _)
  rw [Finset.sum_pair hne', hram w hwf, hram w₀ hw₀, hsum] at hle2
  have : (0 : ℤ) < (((q - 1) / 2 : ℕ) : ℤ) := by exact_mod_cast hnpos
  omega

#print axioms solution

end S_ModularCurve_FullLevel_existsUnique_place_restrictAlong_eq_of_mem_ssPlaces
end P2MW
export P2MW.S_ModularCurve_FullLevel_existsUnique_place_restrictAlong_eq_of_mem_ssPlaces (solution)
