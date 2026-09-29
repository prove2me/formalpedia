-- Prove2me | solution 1 for ModularCurve.FullLevel.genusFF_xHFunctionFieldC_levelH_eq_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/dbb3762a-221a-536b-9f21-01f48ea8a91b

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_EichlerMass
import Definitions.Def_ModularCurve_IgusaFunctionField
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_FullLevel_isKummerGenerator_eisensteinRatio_and_igusaFunctionField_eq_xHFunctionFieldC_levelH
import Theorems.Thm_ModularCurve_FullLevel_ramificationIndex_xHFunctionFieldC_levelH_modularFunctionFieldC_eq_of_liesOverPrime
import Theorems.Thm_AlgebraicCurve_two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_eq_finrank
import Theorems.Thm_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFormula
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_sum_inv_placeWidth_eq_eichlerMass_of_ssPlaces
import Theorems.Thm_ModularCurve_card_eq_nuTwo_and_card_eq_nuThree_of_forall_mem_iff_placeWidth_eq
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_good
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_gamma0_eq_modularFunctionFieldC_of_not_dvd
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_genusFF_xHFunctionFieldC_levelH_eq_of_liesOverPrime
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms"
p2m_attr_erase "instance" "CuspForm.GammaH_finiteIndex ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "simp" "ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U"
p2m_attr_erase "simp" "CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve~genus ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

noncomputable section

local instance instAlgebraResidueFieldXHFunctionFieldC
    (A : ValuationSubring (AlgebraicClosure ℚ)) (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    Algebra (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) M H) :=
  inferInstance

namespace I2BodyPkg

open IntermediateField Polynomial

section KummerPackage

variable {κ : Type} [Field κ] {Ω : Type} [Field Ω] [Algebra κ Ω]

theorem finrank_inclusion_eq (K₀ : IntermediateField κ Ω) (a : Ω) (n : ℕ) (hn0 : n ≠ 0)
    (hrel : K₀.relfinrank (IgusaCover.igusaFunctionField K₀ a) = n)
    (hle : K₀ ≤ IgusaCover.igusaFunctionField K₀ a) :
    letI : Algebra ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    Module.finrank ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) = n ∧
      FiniteDimensional ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) := by
  letI alg : Algebra ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) :=
    (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have hdeg : Module.finrank ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) = n := by
    show Module.finrank ↥K₀ ↥(extendScalars hle) = n
    rw [← relfinrank_eq_finrank_of_le]
    exact hrel
  exact ⟨hdeg, Module.finite_of_finrank_pos (by rw [hdeg]; exact Nat.pos_of_ne_zero hn0)⟩

theorem adjoin_simple_eq_top (K₀ : IntermediateField κ Ω) (a : Ω) (haint0 : ∃ n : ℕ, n ≠ 0 ∧ a ^ n ∈ K₀)
    (hle : K₀ ≤ IgusaCover.igusaFunctionField K₀ a) :
    letI : Algebra ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    IntermediateField.adjoin ↥K₀ ({⟨a, IgusaCover.mem_igusaFunctionField K₀ a⟩} :
      Set ↥(IgusaCover.igusaFunctionField K₀ a)) = ⊤ := by
  letI alg : Algebra ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) :=
    (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI hst : IsScalarTower ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) Ω :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨n, hn0, hmem⟩ := haint0
  set b : ↥K₀ := ⟨a ^ n, hmem⟩ with hbdef
  set α : ↥(IgusaCover.igusaFunctionField K₀ a) := ⟨a, IgusaCover.mem_igusaFunctionField K₀ a⟩ with hαdef
  have hrootΩ : aeval a (X ^ n - C b) = 0 := by
    rw [aeval_sub, aeval_X_pow, aeval_C, sub_eq_zero]
    rfl
  have haint : IsIntegral ↥K₀ a := ⟨_, monic_X_pow_sub_C b hn0, by rw [← aeval_def]; exact hrootΩ⟩
  have hα : α ^ n = algebraMap ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) b := Subtype.ext rfl
  have hroot : aeval α (X ^ n - C b) = 0 := by
    rw [aeval_sub, aeval_X_pow, aeval_C, hα, sub_self]
  have hαint : IsIntegral ↥K₀ α := ⟨_, monic_X_pow_sub_C b hn0, by rw [← aeval_def]; exact hroot⟩
  have hEΩ : K₀⟮a⟯ = extendScalars hle := by
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
  have hS : Algebra.adjoin ↥K₀ {α} = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx1 : (x : Ω) ∈ K₀⟮a⟯ := by
      rw [hEΩ, mem_extendScalars]
      exact x.2
    have hx2 : (x : Ω) ∈ (Algebra.adjoin ↥K₀ {α}).map
        (IsScalarTower.toAlgHom ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) Ω) := by
      rw [AlgHom.map_adjoin, Set.image_singleton]
      change (x : Ω) ∈ Algebra.adjoin ↥K₀ {a}
      rw [← adjoin_simple_toSubalgebra_of_isAlgebraic haint.isAlgebraic]
      exact hx1
    obtain ⟨y, hy, hyx⟩ := Subalgebra.mem_map.mp hx2
    have : y = x := Subtype.ext hyx
    rwa [← this]
  apply IntermediateField.toSubalgebra_injective
  rw [adjoin_simple_toSubalgebra_of_isAlgebraic hαint.isAlgebraic, hS, IntermediateField.top_toSubalgebra]

theorem kummer_package
    (K₀ E : IntermediateField κ Ω) (a : Ω) (n : ℕ) (hn : (n : κ) ≠ 0)
    (hK : IgusaCover.IsKummerGenerator n K₀ a) (hE : IgusaCover.igusaFunctionField K₀ a = E)
    (hrel : K₀.relfinrank E = n) (hle : K₀ ≤ E) :
    letI : Algebra ↥K₀ ↥E := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    (IntermediateField.inclusion hle).toRingHom.IsIntegral ∧ FiniteDimensional ↥K₀ ↥E ∧
      Algebra.IsSeparable ↥K₀ ↥E ∧ Module.finrank ↥K₀ ↥E = n := by
  subst hE
  letI alg : Algebra ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) :=
    (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (by simp)
  obtain ⟨hdeg, hfd⟩ := finrank_inclusion_eq K₀ a n hn0 hrel hle
  haveI := hfd

  have hint : (IntermediateField.inclusion hle).toRingHom.IsIntegral := fun x =>
    Algebra.IsIntegral.isIntegral (R := ↥K₀) x

  set b : ↥K₀ := ⟨a ^ n, hK.pow_mem⟩ with hbdef
  have hb : b ≠ 0 := by
    intro h
    have h' : (a ^ n : Ω) = 0 := congrArg Subtype.val h
    exact hK.ne_zero ((pow_eq_zero_iff hn0).mp h')
  set α : ↥(IgusaCover.igusaFunctionField K₀ a) := ⟨a, IgusaCover.mem_igusaFunctionField K₀ a⟩ with hαdef
  have hα : α ^ n = algebraMap ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) b := Subtype.ext rfl
  have hnK : ((n : ℕ) : ↥K₀) ≠ 0 := by
    intro h
    apply hn
    have h' : algebraMap κ ↥K₀ (n : κ) = 0 := by rwa [map_natCast]
    exact (map_eq_zero_iff _ (algebraMap κ ↥K₀).injective).mp h'
  have hroot : aeval α (X ^ n - C b) = 0 := by
    rw [aeval_sub, aeval_X_pow, aeval_C, hα, sub_self]
  have hsepα : IsSeparable ↥K₀ α :=
    (Polynomial.separable_X_pow_sub_C b hnK hb).of_dvd (minpoly.dvd ↥K₀ α hroot)
  have htop := adjoin_simple_eq_top K₀ a ⟨n, hn0, hK.pow_mem⟩ hle

  haveI hsep1 : Algebra.IsSeparable ↥K₀ ↥K₀⟮α⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable ↥K₀ _).mpr hsepα
  have hsep : Algebra.IsSeparable ↥K₀ ↥(IgusaCover.igusaFunctionField K₀ a) :=
    AlgEquiv.Algebra.isSeparable ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)
  exact ⟨hint, hfd, hsep, hdeg⟩

end KummerPackage

theorem fg_modularFunctionFieldC (q : ℕ) [Fact q.Prime] (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] :
    ∃ x : ↥(modularFunctionFieldC k N), Transcendental k x ∧
      FiniteDimensional ↥(IntermediateField.adjoin k ({x} : Set ↥(modularFunctionFieldC k N)))
        ↥(modularFunctionFieldC k N) := by
  rw [← ModularCurve.qExpFunctionFieldC_gamma0_eq_modularFunctionFieldC_of_not_dvd k N q hqN]
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.T]
  obtain ⟨x, -, hx, hfin⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed k
      (CongruenceSubgroup.Gamma0 N) hT
  exact ⟨x, hx, hfin⟩

theorem placeWidth_le_three {k : Type*} [Field k] [DecidableEq k] (N : ℕ) [NeZero N]
    (v : Place k (modularFunctionFieldC k N)) : placeWidth N v ≤ 3 := by
  unfold placeWidth
  refine le_trans (Nat.div_le_self _ _) ?_
  rcases jWidth_eq_one_or (v.evalAt (jGeomGen k N)) with h | h | h <;> omega

theorem ord_pos_of_placeWidth_eq_two {k : Type*} [Field k] [DecidableEq k] (N : ℕ) [NeZero N]
    (v : Place k (modularFunctionFieldC k N)) (h : placeWidth N v = 2) :
    0 < v.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) 1728) := by
  unfold placeWidth at h
  have hW : jWidth (v.evalAt (jGeomGen k N)) ≤ 3 := by
    rcases jWidth_eq_one_or (v.evalAt (jGeomGen k N)) with h' | h' | h' <;> omega
  have hrpos : 0 < placeRamificationJ N v := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0, Nat.div_zero] at h
    omega
  have hr1 : placeRamificationJ N v = 1 := by
    by_contra hne
    have hlt : jWidth (v.evalAt (jGeomGen k N)) / placeRamificationJ N v < 2 :=
      (Nat.div_lt_iff_lt_mul hrpos).mpr (by omega)
    omega
  rw [hr1, Nat.div_one] at h
  have hev : v.evalAt (jGeomGen k N) = 1728 := by
    unfold jWidth at h
    split_ifs at h with h0 h1 <;> first | assumption | omega
  have hr1' := hr1
  unfold placeRamificationJ at hr1'
  rw [hev] at hr1'
  have hpos : 0 < (v.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) 1728)).toNat := by
    rw [hr1']; exact one_pos
  exact Int.lt_toNat.mp hpos

theorem ord_pos_of_placeWidth_eq_three {k : Type*} [Field k] [DecidableEq k] (N : ℕ) [NeZero N]
    (v : Place k (modularFunctionFieldC k N)) (h : placeWidth N v = 3) :
    0 < v.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) 0) := by
  unfold placeWidth at h
  have hW : jWidth (v.evalAt (jGeomGen k N)) ≤ 3 := by
    rcases jWidth_eq_one_or (v.evalAt (jGeomGen k N)) with h' | h' | h' <;> omega
  have hrpos : 0 < placeRamificationJ N v := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0, Nat.div_zero] at h
    omega
  have hr1 : placeRamificationJ N v = 1 := by
    by_contra hne
    have hlt : jWidth (v.evalAt (jGeomGen k N)) / placeRamificationJ N v < 2 :=
      (Nat.div_lt_iff_lt_mul hrpos).mpr (by omega)
    omega
  rw [hr1, Nat.div_one] at h
  have hev : v.evalAt (jGeomGen k N) = 0 := by
    unfold jWidth at h
    split_ifs at h with h0 h1 <;> first | assumption | omega
  have hr1' := hr1
  unfold placeRamificationJ at hr1'
  rw [hev] at hr1'
  have hpos : 0 < (v.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) 0)).toNat := by
    rw [hr1']; exact one_pos
  exact Int.lt_toNat.mp hpos

theorem one_le_placeWidth_of_mem_ssPlaces {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (hq5 : 5 ≤ q) (hqN : ¬ q ∣ N)
    {v : Place k (modularFunctionFieldC k N)} (hv : v ∈ ssPlaces q N k) : 1 ≤ placeWidth N v := by
  have hdvd := placeRamificationJ_dvd_jWidth_of_mem_ssPlaces hq5 hqN hv
  have hcentre := (IsSupersingularPlace.isCentreOf_evalAt hv).1
  have hrpos : 0 < placeRamificationJ N v := by
    unfold placeRamificationJ
    exact Int.lt_toNat.mpr hcentre
  unfold placeWidth
  exact Nat.div_pos (Nat.le_of_dvd (jWidth_pos _) hdvd) hrpos

end I2BodyPkg

namespace I2BodyPkg2

private theorem eq_one_and_eq_of_jWidth_div_eq {k : Type*} [Field k] [DecidableEq k]
    (c : k) (e m : ℕ) (hm : 2 ≤ m) (h : jWidth c / e = m) : e = 1 ∧ jWidth c = m := by
  have hle3 : jWidth c ≤ 3 := by rcases jWidth_eq_one_or c with h' | h' | h' <;> omega
  have he1 : e = 1 := by
    by_contra hne
    rcases Nat.eq_zero_or_pos e with h0 | hpos
    · rw [h0, Nat.div_zero] at h; omega
    · have h2 : 2 ≤ e := by omega
      have : jWidth c / e ≤ 1 :=
        calc jWidth c / e ≤ 3 / e := Nat.div_le_div_right hle3
          _ ≤ 3 / 2 := Nat.div_le_div_left h2 (by norm_num)
          _ = 1 := by norm_num
      omega
  subst he1
  rw [Nat.div_one] at h
  exact ⟨rfl, h⟩

theorem placeWidth_le_three' {k : Type*} [Field k] [DecidableEq k] (N : ℕ) [NeZero N]
    (v : Place k (modularFunctionFieldC k N)) : placeWidth N v ≤ 3 := by
  unfold placeWidth
  calc jWidth (v.evalAt (jGeomGen k N)) / placeRamificationJ N v ≤ jWidth (v.evalAt (jGeomGen k N)) :=
        Nat.div_le_self _ _
    _ ≤ 3 := by rcases jWidth_eq_one_or (v.evalAt (jGeomGen k N)) with h' | h' | h' <;> omega

theorem ord_eq_one_of_placeWidth_eq_two {k : Type*} [Field k] [DecidableEq k] (N : ℕ) [NeZero N]
    (v : Place k (modularFunctionFieldC k N)) (h : placeWidth N v = 2) :
    v.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) 1728) = 1 := by
  obtain ⟨he, hj⟩ := eq_one_and_eq_of_jWidth_div_eq (v.evalAt (jGeomGen k N)) (placeRamificationJ N v) 2 le_rfl h
  have hc : v.evalAt (jGeomGen k N) = 1728 := by
    by_contra hne
    by_cases h0 : v.evalAt (jGeomGen k N) = 0
    · rw [jWidth_of_eq_zero h0] at hj; omega
    · rw [jWidth_of_ne h0 hne] at hj; omega
  unfold placeRamificationJ at he
  rw [hc] at he
  omega

theorem ord_eq_one_of_placeWidth_eq_three {k : Type*} [Field k] [DecidableEq k] (N : ℕ) [NeZero N]
    (v : Place k (modularFunctionFieldC k N)) (h : placeWidth N v = 3) :
    v.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) 0) = 1 := by
  obtain ⟨he, hj⟩ := eq_one_and_eq_of_jWidth_div_eq (v.evalAt (jGeomGen k N)) (placeRamificationJ N v) 3 (by norm_num) h
  have hc : v.evalAt (jGeomGen k N) = 0 := by
    by_contra h0
    by_cases h17 : v.evalAt (jGeomGen k N) = 1728
    · rw [jWidth_of_eq_1728 h17 h0] at hj; omega
    · rw [jWidth_of_ne h0 h17] at hj; omega
  unfold placeRamificationJ at he
  rw [hc] at he
  omega

theorem exists_finset_placeWidth_eq (q : ℕ) [Fact q.Prime] (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N)
    (k : Type*) [Field k] [CharP k q] [DecidableEq k] (c : ℕ) (hc : 2 ≤ c) :
    ∃ S : Finset (Place k (modularFunctionFieldC k N)), ∀ v, v ∈ S ↔ placeWidth N v = c := by
  have hsep := ModularCurve.isSeparable_jqNModC_of_good k N q hqN
  by_cases h2 : c = 2
  · subst h2
    have hfin : {v : Place k (modularFunctionFieldC k N) | placeWidth N v = 2}.Finite :=
      (ModularCurve.finite_setOf_ord_jGeomGen_sub_pos k N hsep 1728).subset (fun v hv => by
        simp only [Set.mem_setOf_eq] at hv ⊢
        rw [ord_eq_one_of_placeWidth_eq_two N v hv]; exact one_pos)
    exact ⟨hfin.toFinset, fun v => by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]⟩
  by_cases h3 : c = 3
  · subst h3
    have hfin : {v : Place k (modularFunctionFieldC k N) | placeWidth N v = 3}.Finite :=
      (ModularCurve.finite_setOf_ord_jGeomGen_sub_pos k N hsep 0).subset (fun v hv => by
        simp only [Set.mem_setOf_eq] at hv ⊢
        rw [ord_eq_one_of_placeWidth_eq_three N v hv]; exact one_pos)
    exact ⟨hfin.toFinset, fun v => by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]⟩
  · refine ⟨∅, fun v => ?_⟩
    simp only [Finset.notMem_empty, false_iff]
    have := placeWidth_le_three' N v
    omega

theorem cast_ne_zero_of_profile (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (k : Type*) [Field k] [CharP k q]
    (x : ℕ) (hx : x = (q - 1) / 2 ∨ (1 ≤ x ∧ x ≤ 3)) : ((x : ℕ) : k) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff k q] at h
  have hx0 : 0 < x := by omega
  have hxq : x < q := by omega
  exact absurd (Nat.le_of_dvd hx0 h) (by omega)

theorem final_arith (q n : ℕ) (hqn : q = 2 * n + 1) (g g₀ ψ c ν₂ ν₃ w mass s : ℚ)
    (hg₀ : g₀ = 1 + ψ / 12 - ν₂ / 4 - ν₃ / 3 - c / 2) (hmass : mass = ((q : ℚ) - 1) * ψ / 12)
    (hs : s = -w + (n : ℚ) * mass + (n : ℚ) * ν₂ / 2 + 2 * (n : ℚ) * ν₃ / 3)
    (hRH : 2 * g - 2 = (n : ℚ) * (2 * g₀ - 2) + s) :
    g = 1 + ((q : ℚ) ^ 2 - 1) * ψ / 48 - ((q : ℚ) - 1) * c / 4 - w / 2 := by
  subst hqn hg₀ hmass hs
  push_cast at hRH ⊢
  linear_combination (1 / 2 : ℚ) * hRH

end I2BodyPkg2

namespace I2BodyAux

open IntermediateField

theorem card_fiber_mul_eq
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
    [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F']
    (v : Place K F) (hv : v.IsRational) (hrat : ∀ w ∈ v.fiber F', Place.IsRational w)
    (m : ℕ) (hm : ∀ w ∈ v.fiber F', w.ramificationIndex F = m) :
    (v.fiber F').card * m = Module.finrank F F' := by
  have h := Place.sum_ramificationIndex_eq_finrank (F' := F') v hv hrat
  rw [Finset.sum_congr rfl (fun w hw => by rw [hm w hw])] at h
  rw [Finset.sum_const, nsmul_eq_mul] at h
  exact_mod_cast h

theorem rh_grouped
    {K F F' : Type*} [Field K] [IsAlgClosed K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    [HasPrincipalDivisors K F']
    (hF : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hratF : ∀ v : Place K F, v.IsRational) (hratF' : ∀ w : Place K F', w.IsRational)
    (m : Place K F → ℕ) (hm : ∀ w : Place K F', w.ramificationIndex F = m (w.restrict F))
    (htame : ∀ v : Place K F, ((m v : ℕ) : K) ≠ 0)
    (T : Finset (Place K F)) (hT : ∀ v : Place K F, v ∉ T → m v = 1) :
    2 * (genusFF K F' : ℚ) - 2 =
      (Module.finrank F F' : ℚ) * (2 * (genusFF K F : ℚ) - 2) +
        ∑ v ∈ T, ((Module.finrank F F' : ℚ) - (Module.finrank F F' : ℚ) / (m v : ℚ)) := by
  classical
  have htame' : ∀ w : Place K F', ((w.ramificationIndex F : ℕ) : K) ≠ 0 := fun w => by
    rw [hm w]; exact htame _
  have hRH := AlgebraicCurve.two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame
    (K := K) (F := F) (F' := F') hF htame'

  set f : Place K F' → ℤ := fun w => (w.ramificationIndex F : ℤ) - 1 with hf
  have hsupp : Function.support f ⊆ ↑(T.biUnion fun v => v.fiber F') := by
    intro w hw
    rw [Function.mem_support] at hw
    simp only [Finset.coe_biUnion, Finset.mem_coe, Set.mem_iUnion, exists_prop]
    refine ⟨w.restrict F, ?_, Place.restrict_mem_fiber w⟩
    by_contra hv
    apply hw
    simp only [hf, hm w, hT _ hv, Nat.cast_one, sub_self]
  have hfin : ∑ᶠ w, f w = ∑ w ∈ T.biUnion (fun v => v.fiber F'), f w :=
    finsum_eq_sum_of_support_subset f hsupp
  have hdisj : (↑T : Set (Place K F)).PairwiseDisjoint (fun v => v.fiber F') := by
    intro v _ v' _ hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro w hw hw'
    rw [Place.mem_fiber] at hw hw'
    exact hne (hw.symm.trans hw')
  rw [Finset.sum_biUnion hdisj] at hfin

  have hcard : ∀ v : Place K F, (v.fiber F').card * m v = Module.finrank F F' := fun v =>
    card_fiber_mul_eq v (hratF v) (fun w _ => hratF' w) (m v)
      (fun w hw => by rw [hm w, Place.mem_fiber.mp hw])
  have hinner : ∀ v ∈ T, ∑ w ∈ v.fiber F', f w =
      (Module.finrank F F' : ℤ) - ((v.fiber F').card : ℤ) := by
    intro v _
    calc ∑ w ∈ v.fiber F', f w = ∑ w ∈ v.fiber F', ((m v : ℤ) - 1) :=
          Finset.sum_congr rfl (fun w hw => by simp only [hf, hm w, Place.mem_fiber.mp hw])
      _ = ((v.fiber F').card : ℤ) * ((m v : ℤ) - 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (Module.finrank F F' : ℤ) - ((v.fiber F').card : ℤ) := by
          rw [← hcard v]; push_cast; ring
  rw [Finset.sum_congr rfl hinner] at hfin

  have hm0 : ∀ v : Place K F, (m v : ℚ) ≠ 0 := fun v h => by
    have : m v = 0 := by exact_mod_cast h
    exact htame v (by rw [this, Nat.cast_zero])
  have hcardQ : ∀ v : Place K F, ((v.fiber F').card : ℚ) = (Module.finrank F F' : ℚ) / (m v : ℚ) := by
    intro v
    rw [eq_div_iff (hm0 v)]
    exact_mod_cast hcard v
  have hRHQ : (2 * (genusFF K F' : ℤ) - 2 : ℚ) =
      (((Module.finrank F F' : ℤ) * (2 * (genusFF K F : ℤ) - 2) +
        ∑ v ∈ T, ((Module.finrank F F' : ℤ) - ((v.fiber F').card : ℤ)) : ℤ) : ℚ) := by
    rw [← hfin]; exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hRH
  push_cast at hRHQ
  rw [hRHQ]
  congr 1
  exact Finset.sum_congr rfl (fun v _ => by rw [hcardQ v])

theorem sum_profile {α : Type*} [DecidableEq α] (W S₂ S₃ T : Finset α) (pw : α → ℕ) (n : ℕ) (hn : n ≠ 0)
    (hWT : W ⊆ T) (h2T : S₂ ⊆ T) (h3T : S₃ ⊆ T)
    (hS₂ : ∀ v, v ∈ S₂ ↔ pw v = 2) (hS₃ : ∀ v, v ∈ S₃ ↔ pw v = 3)
    (hle3 : ∀ v, pw v ≤ 3) (hW1 : ∀ v ∈ W, 1 ≤ pw v)
    (m : α → ℕ) (hmW : ∀ v ∈ W, m v = n) (hmW' : ∀ v, v ∉ W → m v = max 1 (pw v)) :
    ∑ v ∈ T, ((n : ℚ) - (n : ℚ) / (m v : ℚ)) =
      -(W.card : ℚ) + (n : ℚ) * ∑ w ∈ W, ((pw w : ℚ))⁻¹ +
        (n : ℚ) * (S₂.card : ℚ) / 2 + 2 * (n : ℚ) * (S₃.card : ℚ) / 3 := by
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn

  have key : ∀ v ∈ T, ((n : ℚ) - (n : ℚ) / (m v : ℚ)) =
      (-(if v ∈ W then (1 : ℚ) else 0) + (n : ℚ) * (if v ∈ W then ((pw v : ℚ))⁻¹ else 0)) +
        ((n : ℚ) / 2 * (if v ∈ S₂ then (1 : ℚ) else 0) +
          2 * (n : ℚ) / 3 * (if v ∈ S₃ then (1 : ℚ) else 0)) := by
    intro v _
    by_cases hvW : v ∈ W
    · rw [hmW v hvW, if_pos hvW, if_pos hvW, div_self hnQ]
      have h1 := hW1 v hvW
      have h3 := hle3 v
      interval_cases h : pw v
      · have h2' : v ∉ S₂ := fun h' => by rw [hS₂] at h'; omega
        have h3' : v ∉ S₃ := fun h' => by rw [hS₃] at h'; omega
        rw [if_neg h2', if_neg h3']; push_cast; ring
      · have h2' : v ∈ S₂ := (hS₂ v).mpr h
        have h3' : v ∉ S₃ := fun h' => by rw [hS₃] at h'; omega
        rw [if_pos h2', if_neg h3']; push_cast; ring
      · have h2' : v ∉ S₂ := fun h' => by rw [hS₂] at h'; omega
        have h3' : v ∈ S₃ := (hS₃ v).mpr h
        rw [if_neg h2', if_pos h3']; push_cast; ring
    · rw [hmW' v hvW, if_neg hvW, if_neg hvW]
      have h3 := hle3 v
      interval_cases h : pw v
      · have h2' : v ∉ S₂ := fun h' => by rw [hS₂] at h'; omega
        have h3' : v ∉ S₃ := fun h' => by rw [hS₃] at h'; omega
        rw [if_neg h2', if_neg h3']; simp
      · have h2' : v ∉ S₂ := fun h' => by rw [hS₂] at h'; omega
        have h3' : v ∉ S₃ := fun h' => by rw [hS₃] at h'; omega
        rw [if_neg h2', if_neg h3']; simp
      · have h2' : v ∈ S₂ := (hS₂ v).mpr h
        have h3' : v ∉ S₃ := fun h' => by rw [hS₃] at h'; omega
        rw [if_pos h2', if_neg h3', show max 1 2 = 2 from rfl]; push_cast; field_simp; ring
      · have h2' : v ∉ S₂ := fun h' => by rw [hS₂] at h'; omega
        have h3' : v ∈ S₃ := (hS₃ v).mpr h
        rw [if_neg h2', if_pos h3', show max 1 3 = 3 from rfl]; push_cast; field_simp; ring
  rw [Finset.sum_congr rfl key]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr hWT, Finset.inter_eq_right.mpr h2T, Finset.inter_eq_right.mpr h3T,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  ring

end I2BodyAux

namespace I2BodyMain

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (A : ValuationSubring (AlgebraicClosure ℚ))

open Classical in

def mult (v : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')) : ℕ :=
  if v ∈ ssPlaces q M' (ResidueField A) then (q - 1) / 2 else max 1 (placeWidth M' v)

variable {q M' A}

omit [Fact q.Prime] in
theorem mult_of_mem {v : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')}
    (hv : v ∈ ssPlaces q M' (ResidueField A)) : mult q M' A v = (q - 1) / 2 := by
  unfold mult; rw [if_pos hv]

omit [Fact q.Prime] in
theorem mult_of_not_mem {v : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')}
    (hv : v ∉ ssPlaces q M' (ResidueField A)) : mult q M' A v = max 1 (placeWidth M' v) := by
  unfold mult; rw [if_neg hv]

theorem ramificationIndex_eq_mult (hq : 5 ≤ q) (hqM' : ¬ q ∣ M') (hA : A.LiesOverPrime q)
    (hle : modularFunctionFieldC (ResidueField A) M' ≤ xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))
    (hint : RingHom.IsIntegral (IntermediateField.inclusion hle).toRingHom)
    (w : Place (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) :
    letI : Algebra ↥(modularFunctionFieldC (ResidueField A) M')
        ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) :=
      (IntermediateField.inclusion hle).toRingHom.toAlgebra
    w.ramificationIndex ↥(modularFunctionFieldC (ResidueField A) M') =
      mult q M' A (w.restrictAlong (IntermediateField.inclusion hle) hint) := by
  have key := ModularCurve.FullLevel.ramificationIndex_xHFunctionFieldC_levelH_modularFunctionFieldC_eq_of_liesOverPrime
    q hq M' hqM' A hA hle hint w
  dsimp only at key
  unfold mult
  split_ifs with hv
  · exact key.1 hv
  · exact key.2 hv

theorem cast_mult_ne_zero (hq : 5 ≤ q) [CharP (ResidueField A) q]
    (v : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')) :
    ((mult q M' A v : ℕ) : ResidueField A) ≠ 0 := by
  refine I2BodyPkg2.cast_ne_zero_of_profile q hq (ResidueField A) (mult q M' A v) ?_
  by_cases hv : v ∈ ssPlaces q M' (ResidueField A)
  · exact Or.inl (mult_of_mem hv)
  · rw [mult_of_not_mem hv]
    exact Or.inr ⟨le_max_left _ _, max_le (by norm_num) (I2BodyPkg.placeWidth_le_three M' v)⟩

omit [Fact q.Prime] in

theorem mult_eq_one [DecidableEq (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M'))]
    (W : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (S₂ : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')))
    (hS₂ : ∀ v, v ∈ S₂ ↔ placeWidth M' v = 2)
    (S₃ : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')))
    (hS₃ : ∀ v, v ∈ S₃ ↔ placeWidth M' v = 3)
    (v : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')) (hv : v ∉ W ∪ S₂ ∪ S₃) :
    mult q M' A v = 1 := by
  simp only [Finset.mem_union, not_or] at hv
  obtain ⟨⟨hvW, hv2⟩, hv3⟩ := hv
  have hss : v ∉ ssPlaces q M' (ResidueField A) := fun h => hvW ((hW v).mpr h)
  rw [mult_of_not_mem hss]
  have h2 : placeWidth M' v ≠ 2 := fun h => hv2 ((hS₂ v).mpr h)
  have h3 : placeWidth M' v ≠ 3 := fun h => hv3 ((hS₃ v).mpr h)
  have hle3 := I2BodyPkg.placeWidth_le_three M' v
  have : placeWidth M' v ≤ 1 := by omega
  exact max_eq_left this

theorem genusFF_base_eq (hq : 5 ≤ q) (hqM' : ¬ q ∣ M') [CharP (ResidueField A) q] [IsAlgClosed (ResidueField A)] :
    (AlgebraicCurve.genusFF (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M') : ℚ) = genusFormula M' := by
  have h7 := ModularCurve.genusFF_modularFunctionFieldFullC_eq_genusFormula q hq M' hqM' (ResidueField A)
  have h55 := ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC (ResidueField A) q M' hqM'
  exact (congrArg (fun S : IntermediateField (ResidueField A) (LaurentSeries (ResidueField A)) =>
    (AlgebraicCurve.genusFF (ResidueField A) ↥S : ℚ) = genusFormula M') h55).mpr h7

end I2BodyMain

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A)) :
    (AlgebraicCurve.genusFF (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) : ℚ) =
      1 + ((q : ℚ) ^ 2 - 1) * dedekindPsi M' / 48
        - ((q : ℚ) - 1) * cuspCount M' / 4
        - (W.card : ℚ) / 2 := by
  classical

  haveI hAC : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  haveI hch : CharP (ResidueField A) q :=
    ValuationSubring.residueField_charP_of_liesOverPrime A (Fact.out : q.Prime) hA
  have hqn : q = 2 * ((q - 1) / 2) + 1 := by
    obtain ⟨k, hk⟩ := (Fact.out : q.Prime).odd_of_ne_two (by omega); omega
  have hn0 : (q - 1) / 2 ≠ 0 := by omega
  have hn : (((q - 1) / 2 : ℕ) : ResidueField A) ≠ 0 :=
    I2BodyPkg2.cast_ne_zero_of_profile q hq (ResidueField A) _ (Or.inl rfl)

  obtain ⟨hK, hIg, hrel⟩ :=
    ModularCurve.FullLevel.isKummerGenerator_eisensteinRatio_and_igusaFunctionField_eq_xHFunctionFieldC_levelH
      q hq M' hqM' A hA
  have hle : modularFunctionFieldC (ResidueField A) M' ≤
      xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M') :=
    hIg ▸ IgusaCover.le_igusaFunctionField _ _
  letI alg : Algebra ↥(modularFunctionFieldC (ResidueField A) M')
      ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) :=
    (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI hst : IsScalarTower (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')
      ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) :=
    AlgebraicCurve.isScalarTower_along (IntermediateField.inclusion hle)
  obtain ⟨hint, hfd, hsep, hdeg⟩ := I2BodyPkg.kummer_package
    (modularFunctionFieldC (ResidueField A) M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))
    _ ((q - 1) / 2) hn hK hIg hrel hle
  haveI := hfd
  haveI := hsep

  haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
  haveI : (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH (q ^ 2 * M') (levelH q M'))
  haveI hcurve : IsCurveOver (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) :=
    ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed (ResidueField A)
      (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) (ModularCurve.translation_mem_GammaH _ _)

  have hratF : ∀ v : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M'), v.IsRational :=
    fun v => (Place.isRational_iff_deg_eq_one v).mpr (ModularCurve.place_deg_eq_one_of_isAlgClosed _ M' v)
  have hratF' : ∀ w : Place (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')),
      w.IsRational :=
    fun w => (Place.isRational_iff_deg_eq_one w).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed w)

  have hm : ∀ w : Place (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')),
      w.ramificationIndex ↥(modularFunctionFieldC (ResidueField A) M') =
        I2BodyMain.mult q M' A (w.restrict ↥(modularFunctionFieldC (ResidueField A) M')) :=
    fun w => I2BodyMain.ramificationIndex_eq_mult hq hqM' hA hle hint w

  obtain ⟨S₂, hS₂⟩ := I2BodyPkg2.exists_finset_placeWidth_eq q M' hqM' (ResidueField A) 2 le_rfl
  obtain ⟨S₃, hS₃⟩ := I2BodyPkg2.exists_finset_placeWidth_eq q M' hqM' (ResidueField A) 3 (by norm_num)

  have hRH := I2BodyAux.rh_grouped (K := ResidueField A)
    (F := ↥(modularFunctionFieldC (ResidueField A) M'))
    (F' := ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))
    (I2BodyPkg.fg_modularFunctionFieldC q M' hqM' (ResidueField A)) hratF hratF' (I2BodyMain.mult q M' A) hm
    (I2BodyMain.cast_mult_ne_zero hq) (W ∪ S₂ ∪ S₃) (I2BodyMain.mult_eq_one W hW S₂ hS₂ S₃ hS₃)
  rw [hdeg] at hRH

  have hsum := I2BodyAux.sum_profile W S₂ S₃ (W ∪ S₂ ∪ S₃) (placeWidth M') ((q - 1) / 2) hn0
    (Finset.subset_union_left.trans Finset.subset_union_left)
    (Finset.subset_union_right.trans Finset.subset_union_left) Finset.subset_union_right
    hS₂ hS₃ (I2BodyPkg.placeWidth_le_three M')
    (fun v hv => I2BodyPkg.one_le_placeWidth_of_mem_ssPlaces hq hqM' ((hW v).mp hv)) (I2BodyMain.mult q M' A)
    (fun v hv => I2BodyMain.mult_of_mem ((hW v).mp hv))
    (fun v hv => I2BodyMain.mult_of_not_mem (fun h => hv ((hW v).mpr h)))
  have hmass := ModularCurve.sum_inv_placeWidth_eq_eichlerMass_of_ssPlaces q M' hq hqM' (ResidueField A) W hW
  obtain ⟨hν₂, hν₃⟩ := ModularCurve.card_eq_nuTwo_and_card_eq_nuThree_of_forall_mem_iff_placeWidth_eq
    q M' hq hqM' (ResidueField A) S₂ hS₂ S₃ hS₃
  rw [hmass, hν₂, hν₃] at hsum

  have hg₀ := I2BodyMain.genusFF_base_eq (A := A) hq hqM'
  rw [hg₀] at hRH
  exact I2BodyPkg2.final_arith q ((q - 1) / 2) hqn _ _ (dedekindPsi M') (cuspCount M') (nuTwo M') (nuThree M')
    (W.card : ℚ) (eichlerMass M' q) _ rfl rfl hsum hRH

end

end S_ModularCurve_FullLevel_genusFF_xHFunctionFieldC_levelH_eq_of_liesOverPrime
end P2MW
export P2MW.S_ModularCurve_FullLevel_genusFF_xHFunctionFieldC_levelH_eq_of_liesOverPrime (solution)
