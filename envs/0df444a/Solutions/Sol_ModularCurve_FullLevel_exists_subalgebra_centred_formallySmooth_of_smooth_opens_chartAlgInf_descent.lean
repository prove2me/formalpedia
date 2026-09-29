-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_of_smooth_opens_chartAlgInf_descent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/e55365db-b776-5c9a-ae32-3f03f2afa5f7

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_FullLevel_exists_admissible_smallConstants_botLayer_levelField_ringEquiv_of_descentBase
import Theorems.Thm_ModularCurve_FullLevel_exists_regularProlongation_integers_eq_igusaGaussRing
import Theorems.Thm_ModularCurve_FullLevel_mem_constantReduction_integers_iff_inclusion_mem_igusaGaussRing
import Theorems.Thm_ModularCurve_FullLevel_transcendental_and_finiteDimensional_adjoin_levelField
import Theorems.Thm_ModularCurve_FullLevel_mem_igusaRing_coe_levelField_and_injective_twoChartIntegralModel
import Theorems.Thm_ModularCurve_FullLevel_exists_forall_coe_mem_igusa_iff_of_valuationSubring_levelField
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin

import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_Algebra_Smooth_fg_and_isIntegral_mem_and_minimalPrimes_and_formallySmooth_localizationAtPrime
import Theorems.Thm_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
import Theorems.Thm_Algebra_Smooth_isReduced_of_isReduced_of_isNoetherianRing
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_minimalPrimes_or_isMaximal_of_mem_chartAlgFin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_of_smooth_opens_chartAlgInf_descent
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms"
p2m_attr_erase "instance" "CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex ValuationSubring.instIsAlgClosedResidueField GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.qExpandAlgHomC_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add"
p2m_attr_erase "simp" "KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero"
p2m_attr_erase "simp" "WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply ModularCurve.LevelN.coe_jGen ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL"
p2m_attr_erase "simp" "ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace E150I

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

theorem isUnit_iff_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) (a : A) :
    IsUnit (e a) ↔ IsUnit a := MulEquiv.isUnit_map e.toMulEquiv

theorem mem_maximalIdeal_iff_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (a : A) : e a ∈ maximalIdeal B ↔ a ∈ maximalIdeal A := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_of_ringEquiv]

theorem eval_map_symm {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) (f : B[X]) (b : A) :
    e ((f.map e.symm.toRingHom).eval b) = f.eval (e b) := by
  rw [Polynomial.eval_map]
  change e.toRingHom (eval₂ e.symm.toRingHom b f) = _
  rw [Polynomial.hom_eval₂, RingEquiv.toRingHom_comp_symm_toRingHom, eval₂_eq_eval_map, Polynomial.map_id]
  rfl

theorem henselianLocalRing_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [HenselianLocalRing A] (e : A ≃+* B) : HenselianLocalRing B where
  is_henselian := by
    intro f hf a₀ h₁ h₂
    set g : A[X] := f.map e.symm.toRingHom with hg_def
    have hg : g.Monic := hf.map _
    have hb₀ : e (e.symm a₀) = a₀ := e.apply_symm_apply a₀
    have h₁' : g.eval (e.symm a₀) ∈ maximalIdeal A := by
      rw [← mem_maximalIdeal_iff_of_ringEquiv e, eval_map_symm, hb₀]; exact h₁
    have h₂' : IsUnit (g.derivative.eval (e.symm a₀)) := by
      rw [← isUnit_iff_of_ringEquiv e, hg_def, derivative_map, eval_map_symm, hb₀]; exact h₂
    obtain ⟨b, hb, hb'⟩ := HenselianLocalRing.is_henselian g hg (e.symm a₀) h₁' h₂'
    refine ⟨e b, ?_, ?_⟩
    · have := congrArg e hb.eq_zero
      rw [eval_map_symm, map_zero] at this
      exact this
    · have := (mem_maximalIdeal_iff_of_ringEquiv e _).mpr hb'
      rwa [map_sub, hb₀] at this

theorem isDiscreteValuationRing_of_ringEquiv {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing A] (e : A ≃+* B) : IsDiscreteValuationRing B := by
  haveI : IsPrincipalIdealRing B := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  haveI : IsLocalRing B := IsLocalRing.of_surjective' e.toRingHom e.surjective
  refine { not_a_field' := ?_ }
  intro h
  apply IsDiscreteValuationRing.not_a_field A
  rw [eq_bot_iff] at h ⊢
  intro a ha
  have := h ((mem_maximalIdeal_iff_of_ringEquiv e a).mpr ha)
  rw [Ideal.mem_bot] at this ⊢
  exact e.injective (this.trans (map_zero e).symm)

theorem maximalIdeal_eq_span_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (ϖ : A) (h : maximalIdeal A = Ideal.span {ϖ}) : maximalIdeal B = Ideal.span {e ϖ} := by
  apply le_antisymm
  · intro b hb
    have : e.symm b ∈ maximalIdeal A := by
      rw [← mem_maximalIdeal_iff_of_ringEquiv e, e.apply_symm_apply]; exact hb
    rw [h, Ideal.mem_span_singleton] at this
    obtain ⟨c, hc⟩ := this
    rw [Ideal.mem_span_singleton]
    refine ⟨e c, ?_⟩
    rw [← map_mul, ← hc, e.apply_symm_apply]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact (mem_maximalIdeal_iff_of_ringEquiv e ϖ).mpr (h ▸ Ideal.mem_span_singleton_self ϖ)

theorem exists_isPrimitiveRoot_of_isUnit_of_residueField
    {A : Type*} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    (n : ℕ) (hn : 0 < n) (hnA : IsUnit (n : A))
    (hk : ∃ ζ₀ : ResidueField A, IsPrimitiveRoot ζ₀ n) :
    ∃ ζ : A, IsPrimitiveRoot ζ n ∧ ∃ ζ₀ : ResidueField A, IsPrimitiveRoot ζ₀ n ∧ residue A ζ = ζ₀ := by
  obtain ⟨ζ₀, hζ₀⟩ := hk
  obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective ζ₀
  have ha₀' : residue A a₀ = ζ₀ := ha₀

  have hmonic : (X ^ n - 1 : A[X]).Monic := monic_X_pow_sub_C (1 : A) hn.ne'
  have heval : (X ^ n - 1 : A[X]).eval a₀ ∈ maximalIdeal A := by
    rw [← residue_eq_zero_iff]
    simp only [eval_sub, eval_pow, eval_X, eval_one, map_sub, map_pow, map_one, ha₀', hζ₀.pow_eq_one, sub_self]
  have hderiv : IsUnit ((X ^ n - 1 : A[X]).derivative.eval a₀) := by
    have : (X ^ n - 1 : A[X]).derivative.eval a₀ = (n : A) * a₀ ^ (n - 1) := by
      simp [derivative_X_pow]
    rw [this]
    refine hnA.mul (IsUnit.pow _ ?_)
    rw [← residue_ne_zero_iff_isUnit, ha₀']
    exact hζ₀.ne_zero hn.ne'
  obtain ⟨ζ, hroot, hζa⟩ := HenselianLocalRing.is_henselian (X ^ n - 1) hmonic a₀ heval hderiv
  have hres : residue A ζ = ζ₀ := by
    rw [← ha₀', ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hζa
  have hpow : ζ ^ n = 1 := by
    have := hroot
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_one, sub_eq_zero] at this
    exact this
  refine ⟨ζ, IsPrimitiveRoot.mk_of_lt ζ hn hpow ?_, ζ₀, hζ₀, hres⟩
  intro l hl0 hln hl
  apply hζ₀.pow_ne_one_of_pos_of_lt hl0.ne' hln
  rw [← hres, ← map_pow, hl, map_one]

end E150I

namespace E148LC
theorem adjoin_inv_eq {K F : Type*} [Field K] [Field F] [Algebra K F] (j : F) :
    IntermediateField.adjoin K ({j⁻¹} : Set F) = IntermediateField.adjoin K ({j} : Set F) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self _ _)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have := inv_mem (IntermediateField.mem_adjoin_simple_self K j⁻¹)
    rwa [inv_inv] at this

theorem mem_nonunits_comap_iff {K L : Type*} [Field K] [Field L] (O : ValuationSubring L) (f : K →+* L) (x : K) :
    x ∈ (O.comap f).nonunits ↔ f x ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap,
    map_inv₀, map_eq_zero_iff f f.injective]
end E148LC

namespace E147GP

universe u

open AlgebraicCurve.TwoChartIntegralModel in

theorem chartAlg_mem_of_subset {R F : Type u} {E : Type*} [CommRing R] [Field F] [Field E] [Algebra R F]
    (ι : F →+* E) (O : ValuationSubring E) (S : Set F)
    (hR : ∀ a : R, ι (algebraMap R F a) ∈ O) (hS : ∀ s ∈ S, ι s ∈ O) :
    ∀ b : F, b ∈ chartAlg R F S → ι b ∈ O := by
  intro b hb
  rw [mem_chartAlg_iff] at hb
  let P : Subalgebra R F :=
    { carrier := {f | ι f ∈ O}
      mul_mem' := fun {a b} ha hb => by
        show ι (a * b) ∈ O
        rw [map_mul]; exact O.mul_mem _ _ ha hb
      one_mem' := by show ι 1 ∈ O; rw [map_one]; exact O.one_mem
      add_mem' := fun {a b} ha hb => by
        show ι (a + b) ∈ O
        rw [map_add]; exact O.add_mem _ _ ha hb
      zero_mem' := by show ι 0 ∈ O; rw [map_zero]; exact O.zero_mem
      algebraMap_mem' := hR }
  have hadj : Algebra.adjoin R S ≤ P := Algebra.adjoin_le (fun s hs => hS s hs)
  let φ : ↥(Algebra.adjoin R S) →+* O :=
    (ι.comp (algebraMap ↥(Algebra.adjoin R S) F)).codRestrict O.toSubring (fun s => hadj s.2)
  have hint : IsIntegral O (ι b) :=
    hb.map_of_comp_eq φ ι (by ext s; rfl)
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := O) (K := E)).mp hint
  rw [← hy]
  exact y.2

theorem mem_nonunits_of_mem_nonunits_of_le {K E : Type*} [Field K] [Field E] (V : ValuationSubring K) (W : ValuationSubring E)
    (ι : K →+* E) (hVW : ∀ f : K, f ∈ V → ι f ∈ W) (x : K) (hx : ι x ∈ W.nonunits) : x ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or] at hx ⊢
  rcases hx with h0 | hinv
  · exact Or.inl ((map_eq_zero_iff ι ι.injective).mp h0)
  · exact Or.inr (fun h => hinv (by rw [← map_inv₀]; exact hVW _ h))

end E147GP

namespace E147CP

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u v

theorem exists_basicOpen_le {C : Type u} [CommRing C] {X : Scheme.{u}} (ι : Spec (CommRingCat.of C) ⟶ X)
    (U : X.Opens) (y : PrimeSpectrum C) (hy : ι.base y ∈ U) :
    ∃ f : C, f ∉ y.asIdeal ∧ ∀ z : PrimeSpectrum C, f ∉ z.asIdeal → ι.base z ∈ U := by
  have hyV : y ∈ (ι ⁻¹ᵁ U : (Spec (CommRingCat.of C)).Opens) := hy
  obtain ⟨t, ⟨f, rfl⟩, hyt, htV⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hyV (ι ⁻¹ᵁ U).isOpen
  exact ⟨f, (PrimeSpectrum.mem_basicOpen f y).mp hyt, fun z hz => htV ((PrimeSpectrum.mem_basicOpen f z).mpr hz)⟩

theorem smooth_away_of_basicOpen_le {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
    {X : Scheme.{u}} (ι : Spec (CommRingCat.of C) ⟶ X) [IsOpenImmersion ι] (π : X ⟶ Spec (CommRingCat.of R))
    (hι : ι ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R C)))
    (U : X.Opens) (hU : Smooth (U.ι ≫ π)) (f : C)
    (hf : ∀ z : PrimeSpectrum C, f ∉ z.asIdeal → ι.base z ∈ U) :
    Algebra.Smooth R (Localization.Away f) := by
  let g : Spec (CommRingCat.of (Localization.Away f)) ⟶ Spec (CommRingCat.of C) :=
    Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away f)))
  have hrange : Set.range (g ≫ ι).base ⊆ Set.range U.ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hz : g.base z ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum C)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
      exact ⟨z, rfl⟩
    exact hf _ ((PrimeSpectrum.mem_basicOpen f _).mp hz)
  let h : Spec (CommRingCat.of (Localization.Away f)) ⟶ U := IsOpenImmersion.lift U.ι (g ≫ ι) hrange
  have hfac : h ≫ U.ι = g ≫ ι := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion (h ≫ U.ι) := by rw [hfac]; infer_instance
  haveI : IsOpenImmersion h := IsOpenImmersion.of_comp _ U.ι
  have hsm : Smooth (h ≫ (U.ι ≫ π)) := inferInstance
  have heq : h ≫ (U.ι ≫ π) = Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))) := by
    rw [← Category.assoc, hfac, Category.assoc, hι, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [heq, HasRingHomProperty.Spec_iff (P := @Smooth)] at hsm
  exact (RingHom.smooth_algebraMap).mp hsm

theorem eq_of_minimal_of_le_of_isDomain_localization {T : Type v} [CommRing T] (q : Ideal T) [q.IsPrime]
    [IsDomain (Localization.AtPrime q)]
    {P₁ P₂ : Ideal T} [P₁.IsPrime] [P₂.IsPrime] (h₁ : P₁ ≤ q) (h₂ : P₂ ≤ q)
    (hm₁ : ∀ P : Ideal T, P.IsPrime → P ≤ P₁ → P = P₁) (hm₂ : ∀ P : Ideal T, P.IsPrime → P ≤ P₂ → P = P₂) :
    P₁ = P₂ := by
  have hker : ∀ P : Ideal T, P.IsPrime → P ≤ q → RingHom.ker (algebraMap T (Localization.AtPrime q)) ≤ P := by
    intro P hP hPq x hx
    rw [RingHom.mem_ker, IsLocalization.map_eq_zero_iff q.primeCompl] at hx
    obtain ⟨⟨m, hm⟩, hmx⟩ := hx
    have : m * x ∈ P := by rw [hmx]; exact P.zero_mem
    exact ((hP.mem_or_mem this).resolve_left (fun h => hm (hPq h)))
  haveI : (RingHom.ker (algebraMap T (Localization.AtPrime q))).IsPrime := RingHom.ker_isPrime _
  rw [← hm₁ _ this (hker P₁ inferInstance h₁), ← hm₂ _ this (hker P₂ inferInstance h₂)]

theorem eq_of_mem_minimalPrimes_of_le_of_smooth_away {R C : Type v} [CommRing R] [IsLocalRing R] [CommRing C] [Algebra R C]
    (f : C) (𝔫 : Ideal C) [h𝔫 : 𝔫.IsPrime] (hf : f ∉ 𝔫)
    (hle : (maximalIdeal R).map (algebraMap R C) ≤ 𝔫)
    [Algebra.Smooth R (Localization.Away f)]
    {P P' : Ideal C} (hP : P ∈ ((maximalIdeal R).map (algebraMap R C)).minimalPrimes)
    (hP' : P' ∈ ((maximalIdeal R).map (algebraMap R C)).minimalPrimes) (hPn : P ≤ 𝔫) (hP'n : P' ≤ 𝔫) : P = P' := by
  classical
  set S := Localization.Away f with hS
  set p : Ideal R := maximalIdeal R with hp

  have hdisj : ∀ Q : Ideal C, Q ≤ 𝔫 → Disjoint (Submonoid.powers f : Set C) Q := by
    intro Q hQ
    rw [Set.disjoint_left]
    rintro x ⟨n, rfl⟩ hx
    exact hf (h𝔫.mem_of_pow_mem n (hQ hx))
  have hmapPrime : ∀ Q : Ideal C, Q.IsPrime → Q ≤ 𝔫 → (Q.map (algebraMap C S)).IsPrime := fun Q hQ hQn =>
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) S Q hQ (hdisj Q hQn)
  have hcomap : ∀ Q : Ideal C, Q.IsPrime → Q ≤ 𝔫 → (Q.map (algebraMap C S)).comap (algebraMap C S) = Q := fun Q hQ hQn =>
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) S hQ (hdisj Q hQn)
  have hpS : p.map (algebraMap R S) = (p.map (algebraMap R C)).map (algebraMap C S) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

  have hmin : ∀ Q : Ideal C, Q ∈ (p.map (algebraMap R C)).minimalPrimes → Q ≤ 𝔫 →
      (Q.map (algebraMap C S)).IsPrime ∧ p.map (algebraMap R S) ≤ Q.map (algebraMap C S) ∧
      ∀ Q' : Ideal S, Q'.IsPrime → p.map (algebraMap R S) ≤ Q' → Q' ≤ Q.map (algebraMap C S) → Q' = Q.map (algebraMap C S) := by
    intro Q hQ hQn
    have hQp : Q.IsPrime := hQ.1.1
    refine ⟨hmapPrime Q hQp hQn, by rw [hpS]; exact Ideal.map_mono hQ.1.2, ?_⟩
    intro Q' hQ' hpQ' hQ'Q
    have h1 : p.map (algebraMap R C) ≤ Q'.comap (algebraMap C S) := by
      rw [← Ideal.map_le_iff_le_comap, ← hpS]; exact hpQ'
    have h2 : Q'.comap (algebraMap C S) ≤ Q := by
      have := Ideal.comap_mono (f := algebraMap C S) hQ'Q
      rwa [hcomap Q hQp hQn] at this
    haveI := hQ'
    have h3 : Q'.comap (algebraMap C S) = Q := le_antisymm h2 (hQ.2 ⟨Ideal.comap_isPrime _ Q', h1⟩ h2)
    rw [← h3]
    exact (IsLocalization.map_under (Submonoid.powers f) S Q').symm

  have hover : ∀ Q : Ideal S, Q.IsPrime → p.map (algebraMap R S) ≤ Q → Q.LiesOver p := by
    intro Q hQ hpQ
    haveI := hQ
    have hne : Q.under R ≠ ⊤ := Ideal.IsPrime.ne_top (Ideal.comap_isPrime _ Q)
    exact ⟨(IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hne (Ideal.map_le_iff_le_comap.mp hpQ)⟩
  have hover' : ∀ Q : Ideal S, Q.IsPrime → Q.LiesOver p → p.map (algebraMap R S) ≤ Q := by
    intro Q hQ hQp
    rw [Ideal.map_le_iff_le_comap, hQp.over]

  let φ := PrimeSpectrum.primesOverOrderIsoFiber R S p

  obtain ⟨hNpr, hpN, -⟩ : (𝔫.map (algebraMap C S)).IsPrime ∧ p.map (algebraMap R S) ≤ 𝔫.map (algebraMap C S) ∧ True :=
    ⟨hmapPrime 𝔫 h𝔫 le_rfl, by rw [hpS]; exact Ideal.map_mono hle, trivial⟩
  obtain ⟨hQ₁pr, hpQ₁, hQ₁min⟩ := hmin P hP hPn
  obtain ⟨hQ₂pr, hpQ₂, hQ₂min⟩ := hmin P' hP' hP'n
  let N : p.primesOver S := ⟨𝔫.map (algebraMap C S), ⟨hNpr, hover _ hNpr hpN⟩⟩
  let Q₁ : p.primesOver S := ⟨P.map (algebraMap C S), ⟨hQ₁pr, hover _ hQ₁pr hpQ₁⟩⟩
  let Q₂ : p.primesOver S := ⟨P'.map (algebraMap C S), ⟨hQ₂pr, hover _ hQ₂pr hpQ₂⟩⟩
  have hQ₁N : Q₁ ≤ N := Ideal.map_mono hPn
  have hQ₂N : Q₂ ≤ N := Ideal.map_mono hP'n

  haveI : IsDomain (Localization.AtPrime (φ N).asIdeal) :=
    (Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime p.ResidueField (p.Fiber S)
      (φ N).asIdeal (Localization.AtPrime (φ N).asIdeal)).1

  have hminT : ∀ Q : p.primesOver S,
      (∀ Q' : Ideal S, Q'.IsPrime → p.map (algebraMap R S) ≤ Q' → Q' ≤ Q.1 → Q' = Q.1) →
      ∀ P0 : Ideal (p.Fiber S), P0.IsPrime → P0 ≤ (φ Q).asIdeal → P0 = (φ Q).asIdeal := by
    intro Q hQmin P0 hP0 hle0
    let Q0 : p.primesOver S := φ.symm ⟨P0, hP0⟩
    have hφQ0 : φ Q0 = ⟨P0, hP0⟩ := φ.apply_symm_apply _
    have hQ0Q : Q0 ≤ Q := by
      rw [← φ.le_iff_le, hφQ0]
      exact hle0
    have hEq : Q0.1 = Q.1 := hQmin Q0.1 Q0.2.1 (hover' _ Q0.2.1 Q0.2.2) hQ0Q
    have hQ0eq : Q0 = Q := Subtype.ext hEq
    rw [← hQ0eq, hφQ0]
  haveI : (φ Q₁).asIdeal.IsPrime := (φ Q₁).2
  haveI : (φ Q₂).asIdeal.IsPrime := (φ Q₂).2
  have hT : (φ Q₁).asIdeal = (φ Q₂).asIdeal :=
    eq_of_minimal_of_le_of_isDomain_localization (φ N).asIdeal
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr (φ.monotone hQ₁N))
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr (φ.monotone hQ₂N))
      (hminT Q₁ hQ₁min) (hminT Q₂ hQ₂min)
  have hQQ : Q₁ = Q₂ := φ.injective (PrimeSpectrum.ext hT)
  have hQQ' : P.map (algebraMap C S) = P'.map (algebraMap C S) := congrArg (fun Q : p.primesOver S => Q.1) hQQ
  rw [← hcomap P hP.1.1 hPn, ← hcomap P' hP'.1.1 hP'n, hQQ']

end E147CP

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in
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
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)
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

    (K₀ : Subfield (AlgebraicClosure ℚ)) [Algebra.IsAlgebraic ↥K₀ (AlgebraicClosure ℚ)] (hπK₀ : π ∈ K₀)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [HenselianLocalRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (hιK₀ : Set.range (fun a : A₀ => ((ι a : ↥A) : AlgebraicClosure ℚ)) =
      (A : Set (AlgebraicClosure ℚ)) ∩ (K₀ : Set (AlgebraicClosure ℚ)))
    (hres : Function.Surjective ((IsLocalRing.residue ↥A).comp ι))
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})

    (hϖ₀π : ((ι ϖ₀ : ↥A) : AlgebraicClosure ℚ) = π)

    (F₀ : Subfield ↥(fieldBar q M'))
    (hF₀ : ∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔ ∀ n : ℤ, ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ K₀)

    (hjF₀ : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀)

    [Algebra A₀ ↥F₀]
    (hj₀ : ∀ a : A₀, ((algebraMap A₀ ↥F₀ a : ↥F₀) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ))
    [Fact ((⟨_, hjF₀⟩ : ↥F₀) ≠ 0)]
    (V : ValuationSubring ↥F₀)
    (hV : ∀ f : ↥F₀, f ∈ V → (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q))
    (hVlt : ∃ f : ↥F₀, (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q) ∧ f ∉ V)
    (hCV : ∀ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), (g : ↥F₀) ∈ V)
    (𝔫 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (h𝔫max : 𝔫.IsMaximal)
    (h𝔫 : ∀ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), g ∈ 𝔫 ↔ (g : ↥F₀) ∈ V.nonunits)

    (hnotSS : ∀ s : ↥W, (∃ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
        (∃ h : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s, (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s)) ∧ g ∉ 𝔫) ∨
      (∃ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), ((g : ↥F₀) : ↥(fieldBar q M')) ∉ OSS s))

    (𝔮 : CuspidalType.ProjLine q → Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)))
    (hLOC : ∀ ℓ (x : ↥F₀), (x : ↥(fieldBar q M')) ∈ OIg ℓ ↔
      ∃ b c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), c ∉ 𝔮 ℓ ∧ x * (c : ↥F₀) = (b : ↥F₀))
    (hMIN : ∀ ℓ, 𝔮 ℓ ∈ (Ideal.map (algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (maximalIdeal A₀)).minimalPrimes)
    (hINJ : Function.Injective 𝔮)
    (hSURJ : ∀ 𝔮' : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
      𝔮' ∈ (Ideal.map (algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (maximalIdeal A₀)).minimalPrimes → ∃ ℓ, 𝔮' = 𝔮 ℓ)

    (hGENFIB : ∀ 𝔭 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), 𝔭.IsPrime → 𝔭 ≠ ⊥ → algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ϖ₀ ∉ 𝔭 →
      ∃ V₁ : ValuationSubring ↥F₀, ∀ f : ↥F₀, f ∈ V₁ ↔ ∃ b c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), c ∉ 𝔭 ∧ f * (c : ↥F₀) = (b : ↥F₀))

    (U : (AlgebraicCurve.TwoChartIntegralModel A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).Opens)
    (hxU : (AlgebraicCurve.TwoChartIntegralModel.ιInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ⟨𝔫, h𝔫max.isPrime⟩ ∈ U)
    (hU : Smooth (U.ι ≫ AlgebraicCurve.TwoChartIntegralModel.toBase A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) :
    (∃ (B : Subalgebra A₀ ↥F₀) (𝔪 : Ideal ↥B) (_ : 𝔪.IsMaximal),

      B.FG ∧
      (∀ x : ↥F₀, _root_.IsIntegral ↥B x → x ∈ B) ∧
      (∀ x : ↥F₀, ∃ b c : ↥F₀, b ∈ B ∧ c ∈ B ∧ c ≠ 0 ∧ x * c = b) ∧
      (∀ 𝔮 : Ideal ↥B, 𝔮.IsPrime → Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔮 → ¬ 𝔮.IsMaximal →
        𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes) ∧
      (∀ 𝔭 : Ideal ↥B, 𝔭.IsPrime → 𝔭 ≠ ⊥ → ¬ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔭) →
        ∃ V₁ : ValuationSubring ↥F₀, ∀ f : ↥F₀, f ∈ V₁ ↔ ∃ b c : ↥B, c ∉ 𝔭 ∧ f * (c : ↥F₀) = (b : ↥F₀)) ∧

      (∀ ℓ' : CuspidalType.ProjLine q, (∀ b : ↥B, ((b : ↥F₀) : ↥(fieldBar q M')) ∈ OIg ℓ') → ℓ' = lineInfty q) ∧
      (∀ s : ↥W, ¬ ∀ b : ↥B, ((b : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s) ∧
      (∃ 𝔮 : Ideal ↥B, 𝔮.IsPrime ∧ ∀ x : ↥F₀, (x : ↥(fieldBar q M')) ∈ OIg (lineInfty q) ↔
        ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : ↥F₀) = (b : ↥F₀)) ∧
      (∀ 𝔮 : Ideal ↥B, 𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes →
        ∀ x : ↥F₀, (x : ↥(fieldBar q M')) ∈ OIg (lineInfty q) ↔ ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : ↥F₀) = (b : ↥F₀)) ∧

      (∀ b : ↥B, (b : ↥F₀) ∈ V) ∧ (∀ b : ↥B, b ∈ 𝔪 ↔ (b : ↥F₀) ∈ V.nonunits) ∧

      ((⟨_, hjF₀⟩ : ↥F₀) ∈ B ∨ (⟨_, hjF₀⟩ : ↥F₀)⁻¹ ∈ B) ∧

      (algebraMap A₀ (Localization.AtPrime 𝔪)).FormallySmooth) := by
  classical
  have hqprime : q.Prime := Fact.out

  obtain ⟨k₀, π₀, hπ₀, hk₀, hππ, hdvrK, hunifK, hhensK, hresK, hκ, ⟨ℓa, hℓa, hℓa3, hℓaq, hℓaM', ζ₀, hζ₀⟩, htame, ⟨eK, heK⟩,
      hA₁, hfd, hdvr1, hhens1, ⟨e₀, he₀⟩, hform⟩ :=
    ModularCurve.FullLevel.exists_admissible_smallConstants_botLayer_levelField_ringEquiv_of_descentBase q hq M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀
  letI algk0 : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  obtain ⟨F₀', hCHAR, hK1, hSTAB, hLD, hRAT, hcar, Φ, hΦ⟩ := hform
  haveI := hdvr1
  haveI := hhens1
  have hΦ' : ∀ t : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀'), ((Φ.symm t : ↥F₀) : ↥(fieldBar q M')) = (t : ↥(fieldBar q M')) := fun t => by
    rw [← hΦ (Φ.symm t), Φ.apply_symm_apply]

  obtain ⟨R, hR⟩ := ModularCurve.FullLevel.exists_regularProlongation_integers_eq_igusaGaussRing q hq M' hqM' A hA W hW hle R₀ hR₀ ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr
  have hR₀O := ModularCurve.FullLevel.mem_constantReduction_integers_iff_inclusion_mem_igusaGaussRing q hq M' hqM' A hA W hW hle R₀ hR₀ ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr

  let iBT : ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) →+* ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') :=
    RingHom.codRestrict ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')
      (fun c => (le_sup_left : IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ≤ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀'))
        (IntermediateField.subset_adjoin _ _ ⟨(c : AlgebraicClosure ℚ), c.2, rfl⟩))
  letI algBT : Algebra ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') := iBT.toAlgebra
  have hBT : ∀ c : ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), ((algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') c : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c : AlgebraicClosure ℚ) := fun _ => rfl
  letI algA1T : Algebra ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') :=
    (Φ.toRingHom.comp ((algebraMap A₀ ↥F₀).comp e₀.symm.toRingHom)).toAlgebra
  have halgT : ∀ a : ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))), ((algebraMap ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))) : AlgebraicClosure ℚ) := by
    intro a
    change ((Φ (algebraMap A₀ ↥F₀ (e₀.symm a)) : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')) : ↥(fieldBar q M')) = _
    rw [hΦ, hj₀, ← he₀ (e₀.symm a), e₀.apply_symm_apply]
  letI algBF : Algebra ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥F₀ := (Φ.symm.toRingHom.comp (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀'))).toAlgebra
  let ψ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') ≃ₐ[↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))] ↥F₀ := AlgEquiv.ofRingEquiv (f := Φ.symm) (fun _ => rfl)
  letI algA0B : Algebra A₀ ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) := ((algebraMap ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))).comp e₀.symm.symm.toRingHom).toAlgebra
  haveI : IsFractionRing A₀ ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) :=
    (IsFractionRing.isFractionRing_iff_of_base_ringEquiv (R := ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ)))) (S := ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))) e₀.symm).mp inferInstance
  haveI istA0BF : IsScalarTower A₀ ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥F₀ := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    apply Subtype.ext
    change ((algebraMap A₀ ↥F₀ a : ↥F₀) : ↥(fieldBar q M')) =
      ((Φ.symm (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') ((e₀.symm.symm a : ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ)))) : ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)))) : ↥F₀) : ↥(fieldBar q M'))
    rw [hΦ', hBT, hj₀]
    exact congrArg _ (he₀ a).symm

  let j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') := Φ (⟨_, hjF₀⟩ : ↥F₀)
  have hj₁ : (j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
      ↥(modularFunctionFieldBar M')) := hΦ _
  have hj₁' : ((j₁ : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) jq := by
    rw [hj₁]; rfl
  haveI hj₁0 : Fact (j₁ ≠ 0) := ⟨fun h => (Fact.out : (⟨_, hjF₀⟩ : ↥F₀) ≠ 0) (Φ.injective (h.trans (map_zero Φ).symm))⟩
  have hψj : ψ j₁ = (⟨_, hjF₀⟩ : ↥F₀) := Φ.symm_apply_apply _

  obtain ⟨htj1, hFD1⟩ := @ModularCurve.FullLevel.transcendental_and_finiteDimensional_adjoin_levelField
    q _ M' _ k₀ (⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) hfd F₀' hK1 (hLD (⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) hfd) hRAT algBT hBT j₁ hj₁'
  have hIR := ModularCurve.FullLevel.mem_igusaRing_coe_levelField_and_injective_twoChartIntegralModel
    q hq M' hqM' A hA W hW hle R₀ hR₀ ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr R hR hR₀O π hπ hπP k₀ π₀ hπ₀ hdvrK hunifK hhensK hresK hκ ℓa hℓa hℓa3 hℓaq hℓaM' ζ₀ hζ₀ π₀ hπ₀ htame (⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) hfd (A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) hA₁ F₀' hK1 hSTAB hLD hRAT halgT j₁ hj₁
  dsimp only at hIR
  obtain ⟨hR1, hR2, hR3, hR4⟩ := hIR
  have hBI := ModularCurve.FullLevel.exists_forall_coe_mem_igusa_iff_of_valuationSubring_levelField
    q hq M' hqM' A hA W hW hle R₀ hR₀ ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr R hR hR₀O π hπ hπP k₀ π₀ hπ₀ hdvrK hunifK hhensK hresK hκ ℓa hℓa hℓa3 hℓaq hℓaM' ζ₀ hζ₀ π₀ hπ₀ htame (⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) hfd (A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) hA₁ F₀' hK1 hSTAB hLD hRAT halgT j₁ hj₁

  have htjF : Transcendental ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (⟨_, hjF₀⟩ : ↥F₀) := by
    intro h
    apply htj1
    rw [← hψj] at h
    exact (isAlgebraic_algHom_iff ψ.toAlgHom ψ.injective).mp h
  have htj0 : Transcendental A₀ (⟨_, hjF₀⟩ : ↥F₀) := fun h =>
    htjF (h.extendScalars (IsFractionRing.injective A₀ ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))))
  haveI := hFD1
  have hmap : (IntermediateField.adjoin ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ({j₁} : Set ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀'))).map ψ.toAlgHom =
      IntermediateField.adjoin ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀) := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    congr 2
  let e₁ := ((IntermediateField.adjoin ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ({j₁} : Set ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀'))).equivMap ψ.toAlgHom).trans
    (IntermediateField.equivOfEq hmap)
  have hFDF : FiniteDimensional ↥(IntermediateField.adjoin ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀)) ↥F₀ := by
    refine Module.Finite.of_equiv_equiv e₁.toRingEquiv ψ.toRingEquiv ?_
    ext x
    rfl
  haveI := hFDF
  have hsepF : Algebra.IsSeparable ↥(IntermediateField.adjoin ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀)) ↥F₀ := inferInstance

  let VIg : CuspidalType.ProjLine q → ValuationSubring ↥F₀ := fun l => (OIg l).comap F₀.subtype
  have hVIg : ∀ l (x : ↥F₀), x ∈ VIg l ↔ (x : ↥(fieldBar q M')) ∈ OIg l := fun _ _ => ValuationSubring.mem_comap
  have hVIgnu : ∀ l (x : ↥F₀), x ∈ (VIg l).nonunits ↔ (x : ↥(fieldBar q M')) ∈ (OIg l).nonunits := fun l x =>
    E148LC.mem_nonunits_comap_iff (OIg l) F₀.subtype x

  have heA : ∀ a : A₀, ((algebraMap A₀ ↥F₀ a : ↥F₀) : ↥(fieldBar q M')) =
      ((algebraMap ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') (e₀ a) : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')) : ↥(fieldBar q M')) := fun a => by
    rw [hj₀, halgT, he₀]
  have hVA : ∀ l (a : A₀), algebraMap A₀ ↥F₀ a ∈ VIg l := fun l a => by
    rw [hVIg, heA]; exact hR1 l (e₀ a)
  have hVm : ∀ l, ∀ a ∈ IsLocalRing.maximalIdeal A₀, algebraMap A₀ ↥F₀ a ∈ (VIg l).nonunits := fun l a ha => by
    rw [hVIgnu, heA]; exact hR2 l (e₀ a) ((E150I.mem_maximalIdeal_iff_of_ringEquiv e₀ a).mpr ha)

  haveI h𝔫p : 𝔫.IsPrime := h𝔫max.isPrime
  have hadjinv : IntermediateField.adjoin ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ({((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹} : Set ↥F₀) =
      IntermediateField.adjoin ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀) := E148LC.adjoin_inv_eq _
  haveI hFDF' : FiniteDimensional ↥(IntermediateField.adjoin ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ({((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹} : Set ↥F₀)) ↥F₀ := by
    rw [hadjinv]; exact hFDF
  haveI hsepF' : Algebra.IsSeparable ↥(IntermediateField.adjoin ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ({((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹} : Set ↥F₀)) ↥F₀ := by
    rw [hadjinv]; exact hsepF
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ({((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹} : Set ↥F₀)) ↥F₀ :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : Fact (((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹ ≠ 0) := ⟨inv_ne_zero (Fact.out)⟩
  have htj0' : Transcendental A₀ ((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹ := fun h => htj0 (by simpa using h.inv)
  haveI hFrac : IsFractionRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥F₀ := AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg A₀ ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥F₀ _
  have hVWnu : ∀ x : ↥F₀, (x : ↥(fieldBar q M')) ∈ (OIg (lineInfty q)).nonunits → x ∈ V.nonunits := fun x hx =>
    E147GP.mem_nonunits_of_mem_nonunits_of_le V (OIg (lineInfty q)) F₀.subtype hV x hx
  have hϖ𝔫 : algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ϖ₀ ∈ 𝔫 := by
    rw [h𝔫]
    apply hVWnu
    have h1 := hVm (lineInfty q) ϖ₀ (by rw [hϖ₀]; exact Ideal.mem_span_singleton_self ϖ₀)
    rw [hVIgnu] at h1
    exact h1
  have hmap𝔪 : (maximalIdeal A₀).map (algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) = Ideal.span {algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ϖ₀} := by
    rw [hϖ₀, Ideal.map_span, Set.image_singleton]
  have h𝔪le : (maximalIdeal A₀).map (algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) ≤ 𝔫 := by
    rw [hmap𝔪, Ideal.span_singleton_le_iff_mem]; exact hϖ𝔫

  have hinvIg : ∀ ℓ (c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))), c ∈ 𝔮 ℓ → (c : ↥F₀) ≠ 0 → (((c : ↥F₀)⁻¹ : ↥F₀) : ↥(fieldBar q M')) ∉ OIg ℓ := by
    intro ℓ c hc hc0 h1
    obtain ⟨b, c', hc', hbc⟩ := (hLOC ℓ _).mp h1
    apply hc'
    have : c' = c * b := by
      apply Subtype.ext
      rw [Subalgebra.coe_mul, ← hbc, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    rw [this]; exact Ideal.mul_mem_right _ _ hc

  obtain ⟨f₀, hf₀𝔫, hf₀U⟩ := E147CP.exists_basicOpen_le (AlgebraicCurve.TwoChartIntegralModel.ιInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) U ⟨𝔫, h𝔫max.isPrime⟩ hxU
  haveI hsm₀ : Algebra.Smooth A₀ (Localization.Away f₀) :=
    E147CP.smooth_away_of_basicOpen_le (AlgebraicCurve.TwoChartIntegralModel.ιInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) (AlgebraicCurve.TwoChartIntegralModel.toBase A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))
      (AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) U hU f₀ hf₀U
  have hinf : 𝔮 (lineInfty q) ≤ 𝔫 := by
    intro c hc
    rw [h𝔫]
    by_contra hcn
    rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at hcn
    exact hinvIg _ c hc hcn.1 (hV _ hcn.2)
  have hone : ∀ ℓ, 𝔮 ℓ ≤ 𝔫 → ℓ = lineInfty q := fun ℓ hℓ =>
    hINJ (E147CP.eq_of_mem_minimalPrimes_of_le_of_smooth_away f₀ 𝔫 hf₀𝔫 h𝔪le (hMIN ℓ) (hMIN _) hℓ hinf)

  have hgℓ : ∀ ℓ : {ℓ : CuspidalType.ProjLine q // ℓ ≠ lineInfty q}, ∃ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), g ∈ 𝔮 ℓ.1 ∧ g ∉ 𝔫 := by
    intro ℓ
    by_contra h
    push Not at h
    exact ℓ.2 (hone ℓ.1 h)
  choose gI hgI using hgℓ
  let gS : ↥W → ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) := fun s =>
    if h : (∃ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), (∃ h : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s, (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s)) ∧ g ∉ 𝔫)
    then h.choose else 1
  have hgS𝔫 : ∀ s, gS s ∉ 𝔫 := by
    intro s
    show (if h : _ then _ else _) ∉ 𝔫
    split_ifs with h
    · exact h.choose_spec.2
    · exact fun h1 => h𝔫max.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  haveI : Fintype (CuspidalType.ProjLine q) := Fintype.ofFinite _
  let fr : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) := (∏ ℓ : {ℓ : CuspidalType.ProjLine q // ℓ ≠ lineInfty q}, gI ℓ) * (∏ s : ↥W, gS s)
  let f : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) := f₀ * fr
  have hfr𝔫 : fr ∉ 𝔫 := by
    intro h
    rcases h𝔫max.isPrime.mem_or_mem h with h1 | h2
    · obtain ⟨ℓ, -, hℓ⟩ := Ideal.IsPrime.prod_mem_iff.mp h1
      exact (hgI ℓ).2 hℓ
    · obtain ⟨s, -, hs⟩ := Ideal.IsPrime.prod_mem_iff.mp h2
      exact hgS𝔫 s hs
  have hf𝔫 : f ∉ 𝔫 := fun h => (h𝔫max.isPrime.mem_or_mem h).elim hf₀𝔫 hfr𝔫
  have hfℓ : ∀ ℓ, ℓ ≠ lineInfty q → f ∈ 𝔮 ℓ := by
    intro ℓ hℓ
    have h1 : gI ⟨ℓ, hℓ⟩ ∣ fr := Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ _)) _
    obtain ⟨k, hk⟩ := h1
    show f₀ * fr ∈ 𝔮 ℓ
    rw [hk]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (hgI ⟨ℓ, hℓ⟩).1)

  have hfF0 : ((f : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) : ↥F₀) ≠ 0 := fun h => hf𝔫 (by rw [show f = 0 from Subtype.ext h]; exact 𝔫.zero_mem)
  have hfU : ∀ z : PrimeSpectrum ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), f ∉ z.asIdeal → (AlgebraicCurve.TwoChartIntegralModel.ιInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base z ∈ U := fun z hz =>
    hf₀U z (fun h0 => hz (Ideal.mul_mem_right fr _ h0))
  haveI hsmL : Algebra.Smooth A₀ (Localization.Away f) :=
    E147CP.smooth_away_of_basicOpen_le (AlgebraicCurve.TwoChartIntegralModel.ιInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) (AlgebraicCurve.TwoChartIntegralModel.toBase A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))
      (AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) U hU f hfU
  have hunits : ∀ y : Submonoid.powers f, IsUnit ((AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).val y) := by
    rintro ⟨_, n, rfl⟩
    rw [map_pow]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero n hfF0)
  let φL : Localization.Away f →ₐ[A₀] ↥F₀ := IsLocalization.liftAlgHom (M := Submonoid.powers f) hunits
  have hφalg : ∀ c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), φL (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) (Localization.Away f) c) = (c : ↥F₀) := fun c =>
    IsLocalization.lift_eq hunits c
  have hf0 : f ≠ 0 := by
    intro h; apply hfF0; rw [h]; rfl
  have hinjCL : Function.Injective (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) (Localization.Away f)) :=
    IsLocalization.injective (Localization.Away f) (powers_le_nonZeroDivisors_of_noZeroDivisors hf0)
  have hφinj : Function.Injective φL := by
    show Function.Injective (IsLocalization.lift (M := Submonoid.powers f) hunits)
    rw [IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h; rw [hinjCL h]
    · intro h; exact congrArg _ (Subtype.ext h)
  let B : Subalgebra A₀ ↥F₀ := φL.range
  let e : Localization.Away f ≃ₐ[A₀] ↥B := AlgEquiv.ofInjective φL hφinj
  have he : ∀ z, ((e z : ↥B) : ↥F₀) = φL z := fun _ => rfl
  haveI : Algebra.Smooth A₀ ↥B := Algebra.Smooth.of_equiv e
  letI algCB : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B := (e.toAlgHom.toRingHom.comp (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) (Localization.Away f))).toAlgebra
  have halgCB : ∀ c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), ((algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B c : ↥B) : ↥F₀) = (c : ↥F₀) := fun c => (he _).trans (hφalg c)
  haveI : IsScalarTower A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B := IsScalarTower.of_algebraMap_eq (fun a => Subtype.ext (by
    rw [halgCB]; rfl))
  let e' : Localization.Away f ≃ₐ[↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))] ↥B := AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun _ => rfl)
  haveI hlocB : IsLocalization.Away f ↥B := IsLocalization.isLocalization_of_algEquiv (Submonoid.powers f) e'
  have hCB : ∀ c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), (c : ↥F₀) ∈ B := fun c => ⟨algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) (Localization.Away f) c, hφalg c⟩
  have hCBeq : ∀ c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), (⟨(c : ↥F₀), hCB c⟩ : ↥B) = algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B c := fun c => Subtype.ext (halgCB c).symm
  have hfunitB : IsUnit (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B f) := IsLocalization.map_units ↥B (⟨f, Submonoid.mem_powers f⟩ : Submonoid.powers f)
  have hBform : ∀ b : ↥B, ∃ (c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (n : ℕ), (b : ↥F₀) * ((f : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) : ↥F₀) ^ n = (c : ↥F₀) := by
    intro b
    obtain ⟨⟨c, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers f) b
    refine ⟨c, n, ?_⟩
    have := congrArg (fun w : ↥B => (w : ↥F₀)) h
    simp only [Subalgebra.coe_mul] at this
    rw [map_pow, Subalgebra.coe_pow, halgCB, halgCB] at this
    exact this
  have hfinvV : ((f : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) : ↥F₀)⁻¹ ∈ V := by
    have h1 : ((f : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) : ↥F₀) ∉ V.nonunits := fun h => hf𝔫 ((h𝔫 f).mpr h)
    rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at h1
    exact h1.2
  have hfinvB : (((f : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) : ↥F₀))⁻¹ ∈ B := by
    obtain ⟨u, hu⟩ := hfunitB
    have h1 : ((↑(u⁻¹) : ↥B) : ↥F₀) * ((f : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) : ↥F₀) = 1 := by
      rw [← halgCB f, ← hu, ← Subalgebra.coe_mul, Units.inv_mul, Subalgebra.coe_one]
    rw [← eq_inv_of_mul_eq_one_left h1]
    exact (↑(u⁻¹) : ↥B).2
  have hinvB : ∀ c d : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), f = c * d → ((c : ↥F₀))⁻¹ ∈ B := by
    intro c d hcd
    have hd0 : (d : ↥F₀) ≠ 0 := by
      intro h; apply hfF0; rw [hcd, Subalgebra.coe_mul, h, mul_zero]
    have hval : ((c : ↥F₀))⁻¹ = (d : ↥F₀) * (((f : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) : ↥F₀))⁻¹ := by
      rw [hcd, Subalgebra.coe_mul, mul_inv, mul_comm ((c : ↥F₀))⁻¹, ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
    rw [hval]; exact mul_mem (hCB d) hfinvB

  have hinf𝔮 : f ∉ 𝔮 (lineInfty q) := fun h => hf𝔫 (hinf h)
  have hdisj : ∀ Q : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), Q.IsPrime → f ∉ Q → Disjoint (Submonoid.powers f : Set ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) Q := by
    intro Q hQ hfQ
    rw [Set.disjoint_left]
    rintro x ⟨n, rfl⟩ hx
    exact hfQ (hQ.mem_of_pow_mem n hx)
  have hunder : ∀ Q : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), Q.IsPrime → f ∉ Q → (Q.map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B)).comap (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B) = Q :=
    fun Q hQ hfQ => IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) ↥B hQ (hdisj Q hQ hfQ)
  have hmapP : ∀ Q : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), Q.IsPrime → f ∉ Q → (Q.map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B)).IsPrime :=
    fun Q hQ hfQ => IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) ↥B Q hQ (hdisj Q hQ hfQ)
  have hmu : ∀ P : Ideal ↥B, (P.comap (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B)).map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B) = P :=
    fun P => IsLocalization.map_under (Submonoid.powers f) ↥B P
  have hfP : ∀ P : Ideal ↥B, P ≠ ⊤ → f ∉ P.comap (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B) := fun P hP h =>
    hP (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_comap.mp h) hfunitB)

  have hmaxB : ∀ P : Ideal ↥B, P.IsPrime → (P.comap (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B)).IsMaximal → P.IsMaximal := by
    intro P hP hPm
    obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P hP.ne_top
    have h1 : P.comap (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B) = M.comap (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B) :=
      hPm.eq_of_le (Ideal.IsPrime.ne_top (Ideal.comap_isPrime _ M)) (Ideal.comap_mono hPM)
    have h2 : P = M := by rw [← hmu P, ← hmu M, h1]
    rw [h2]; exact hM

  have hHC : ∀ (P' : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))), P'.IsPrime → f ∉ P' → ∀ (x : ↥F₀) (b c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))), c ∉ P' → x * (c : ↥F₀) = (b : ↥F₀) →
      ∃ b' c' : ↥B, c' ∉ P'.map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B) ∧ x * (c' : ↥F₀) = (b' : ↥F₀) := by
    intro P' hP' hfP' x b c hc hbc
    refine ⟨⟨b, hCB b⟩, ⟨c, hCB c⟩, ?_, hbc⟩
    rw [hCBeq, ← Ideal.mem_comap, hunder P' hP' hfP']
    exact hc
  have hHB : ∀ (P' : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))), P'.IsPrime → f ∉ P' → ∀ (x : ↥F₀) (b c : ↥B), c ∉ P'.map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B) →
      x * (c : ↥F₀) = (b : ↥F₀) → ∃ b' c' : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), c' ∉ P' ∧ x * (c' : ↥F₀) = (b' : ↥F₀) := by
    intro P' hP' hfP' x b c hc hbc
    obtain ⟨c₁, m, hc₁⟩ := hBform c
    obtain ⟨b₁, n, hb₁⟩ := hBform b
    refine ⟨b₁ * f ^ m, c₁ * f ^ n, ?_, ?_⟩
    · intro hmem
      rcases hP'.mem_or_mem hmem with h1 | h2
      · apply hc
        have heq : algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B c₁ = c * algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B (f ^ m) :=
          Subtype.ext (by rw [Subalgebra.coe_mul, halgCB, map_pow, Subalgebra.coe_pow, halgCB]; exact hc₁.symm)
        have hmem' : c * algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B (f ^ m) ∈ P'.map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B) := by
          rw [← heq]; exact Ideal.mem_map_of_mem _ h1
        exact ((hmapP P' hP' hfP').mem_or_mem hmem').resolve_right (fun h =>
          (hmapP P' hP' hfP').ne_top (Ideal.eq_top_of_isUnit_mem _ h (by rw [map_pow]; exact hfunitB.pow m)))
      · exact hfP' (hP'.mem_of_pow_mem n h2)
    · rw [Subalgebra.coe_mul, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_pow, ← hc₁, ← hb₁, ← hbc]
      ring

  have h𝔪B : (maximalIdeal A₀).map (algebraMap A₀ ↥B) =
      ((maximalIdeal A₀).map (algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)))).map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hQle : ∀ P : Ideal ↥B, P.IsPrime → (maximalIdeal A₀).map (algebraMap A₀ ↥B) ≤ P →
      (𝔮 (lineInfty q)).map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B) ≤ P := by
    intro P hP hle
    haveI := hP
    have hle' : (maximalIdeal A₀).map (algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) ≤ P.comap (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B) := by
      rw [← Ideal.map_le_iff_le_comap, ← h𝔪B]; exact hle
    obtain ⟨q', hq'min, hq'le⟩ := Ideal.exists_minimalPrimes_le hle'
    obtain ⟨ℓ, rfl⟩ := hSURJ q' hq'min
    have hℓ : ℓ = lineInfty q := by
      by_contra hℓ
      exact hfP P hP.ne_top (hq'le (hfℓ ℓ hℓ))
    subst hℓ
    calc (𝔮 (lineInfty q)).map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B) ≤ (P.comap (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B)).map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B) :=
          Ideal.map_mono hq'le
      _ = P := hmu P

  have hred : IsReduced (↥B ⧸ (maximalIdeal A₀).map (algebraMap A₀ ↥B)) := by
    haveI : IsReduced (TensorProduct A₀ (A₀ ⧸ maximalIdeal A₀) ↥B) :=
      Algebra.Smooth.isReduced_of_isReduced_of_isNoetherianRing (A₀ ⧸ maximalIdeal A₀) _
    let e1 := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A := A₀) (B := ↥B) (maximalIdeal A₀)).toRingEquiv.trans
      (Algebra.TensorProduct.comm A₀ ↥B (A₀ ⧸ maximalIdeal A₀)).toRingEquiv
    exact isReduced_of_injective e1.toRingHom e1.injective
  have h𝔪Q : (maximalIdeal A₀).map (algebraMap A₀ ↥B) = (𝔮 (lineInfty q)).map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B) := by
    apply le_antisymm
    · rw [h𝔪B]; exact Ideal.map_mono (hMIN (lineInfty q)).1.2
    · have hrad : ((maximalIdeal A₀).map (algebraMap A₀ ↥B)).radical = (maximalIdeal A₀).map (algebraMap A₀ ↥B) :=
        ((Ideal.isRadical_iff_quotient_reduced _).mpr hred).radical
      rw [← hrad, Ideal.radical_eq_sInf]
      exact le_sInf (fun J hJ => hQle J hJ.2 hJ.1)
  haveI hprime : ((maximalIdeal A₀).map (algebraMap A₀ ↥B)).IsPrime := by
    rw [h𝔪Q]; exact hmapP _ (hMIN _).1.1 hinf𝔮

  have hdim1 : Ring.KrullDimLE 1 (↥B ⧸ (maximalIdeal A₀).map (algebraMap A₀ ↥B)) := by
    rw [Ring.krullDimLE_one_iff_of_isPrime_bot]
    intro I hI0 hI
    let P : Ideal ↥B := I.comap (Ideal.Quotient.mk _)
    haveI hPp : P.IsPrime := Ideal.comap_isPrime _ I
    have hPI : P.map (Ideal.Quotient.mk _) = I := Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective I
    have h𝔪P : (maximalIdeal A₀).map (algebraMap A₀ ↥B) ≤ P := by
      intro x hx
      show Ideal.Quotient.mk _ x ∈ I
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact I.zero_mem
    have hPne : P ≠ (maximalIdeal A₀).map (algebraMap A₀ ↥B) := by
      intro h
      apply hI0
      rw [← hPI, h, Ideal.map_quotient_self]
    let P' : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) := P.comap (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B)
    haveI hP'p : P'.IsPrime := Ideal.comap_isPrime _ P
    have hϖP' : algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ϖ₀ ∈ P' := by
      show algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B (algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ϖ₀) ∈ P
      rw [← IsScalarTower.algebraMap_apply]
      exact h𝔪P (Ideal.mem_map_of_mem _ (by rw [hϖ₀]; exact Ideal.mem_span_singleton_self ϖ₀))
    rcases AlgebraicCurve.TwoChartIntegralModel.mem_minimalPrimes_or_isMaximal_of_mem_chartAlgFin A₀ ϖ₀ hϖ₀
        ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥F₀ ((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹ htj0' hFDF' hsepF' P' hϖP' with hmin' | hmax'
    · exfalso
      rw [← hmap𝔪] at hmin'
      obtain ⟨ℓ, hℓ⟩ := hSURJ P' hmin'
      have hℓ' : ℓ = lineInfty q := by
        by_contra h
        have hmem := hfℓ ℓ h
        rw [← hℓ] at hmem
        exact hfP P hPp.ne_top hmem
      apply hPne
      rw [← hmu P, show P.comap (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B) = 𝔮 (lineInfty q) from hℓ.trans (by rw [hℓ']), ← h𝔪Q]
    · have hPmax : P.IsMaximal := hmaxB P hPp hmax'
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk ((maximalIdeal A₀).map (algebraMap A₀ ↥B)))
        Ideal.Quotient.mk_surjective hPmax with htop | hmax''
      · exact absurd (hPI ▸ htop) hI.ne_top
      · rwa [hPI] at hmax''

  have hBfrac : ∀ x : ↥F₀, ∃ b c : ↥F₀, b ∈ B ∧ c ∈ B ∧ c ≠ 0 ∧ x * c = b := by
    intro x
    obtain ⟨a, b', hb', rfl⟩ := IsFractionRing.div_surjective (A := ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) x
    have hb0 : ((b' : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) : ↥F₀) ≠ 0 := by
      have := mem_nonZeroDivisors_iff_ne_zero.mp hb'
      exact fun h => this (Subtype.ext h)
    exact ⟨_, _, hCB a, hCB b', hb0, div_mul_cancel₀ _ hb0⟩
  obtain ⟨hBfg, hBn, hdimB, hSM⟩ :=
    Algebra.Smooth.fg_and_isIntegral_mem_and_minimalPrimes_and_formallySmooth_localizationAtPrime B hBfrac hprime hdim1

  have hBV : ∀ b : ↥B, (b : ↥F₀) ∈ V := by
    intro b
    obtain ⟨c, n, hc⟩ := hBform b
    have : (b : ↥F₀) = (c : ↥F₀) * ((((f : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) : ↥F₀))⁻¹) ^ n := by
      rw [← hc, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero n hfF0), mul_one]
    rw [this]; exact mul_mem (hCV c) (pow_mem hfinvV n)
  let ψB : ↥B →+* ↥V := (B.val.toRingHom).codRestrict V (fun b => hBV b)
  let 𝔪V : Ideal ↥B := (maximalIdeal ↥V).comap ψB
  have h𝔪Vmem : ∀ b : ↥B, b ∈ 𝔪V ↔ (b : ↥F₀) ∈ V.nonunits := by
    intro b
    rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
    rfl
  haveI h𝔪Vp : 𝔪V.IsPrime := Ideal.comap_isPrime ψB _
  have h𝔪VC : 𝔪V.comap (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B) = 𝔫 := by
    ext c
    rw [Ideal.mem_comap, h𝔪Vmem, halgCB, h𝔫]
  have h𝔪Vmax : 𝔪V.IsMaximal := hmaxB 𝔪V h𝔪Vp (h𝔪VC ▸ h𝔫max)

  refine ⟨B, 𝔪V, h𝔪Vmax, hBfg, hBn, hBfrac, hdimB, ?_, ?_, ?_, ?_, ?_, hBV, h𝔪Vmem, Or.inr (hCB (AlgebraicCurve.TwoChartIntegralModel.jInvChartInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))), hSM 𝔪V⟩
  ·
    intro 𝔭 h𝔭 h𝔭0 h𝔭𝔪
    haveI := h𝔭
    let P' : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) := 𝔭.comap (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B)
    haveI hP'p : P'.IsPrime := Ideal.comap_isPrime _ 𝔭
    have hfP' : f ∉ P' := hfP 𝔭 h𝔭.ne_top
    have hP'0 : P' ≠ ⊥ := by
      intro h0
      apply h𝔭0
      rw [← hmu 𝔭, show 𝔭.comap (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B) = ⊥ from h0, Ideal.map_bot]
    have hϖP' : algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ϖ₀ ∉ P' := by
      intro h
      apply h𝔭𝔪
      rw [h𝔪B, hmap𝔪, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
      exact h
    obtain ⟨V₁, hV₁⟩ := hGENFIB P' hP'p hP'0 hϖP'
    refine ⟨V₁, fun x => (hV₁ x).trans ⟨?_, ?_⟩⟩
    · rintro ⟨b, c, hc, hbc⟩
      have := hHC P' hP'p hfP' x b c hc hbc
      rwa [hmu 𝔭] at this
    · rintro ⟨b, c, hc, hbc⟩
      exact hHB P' hP'p hfP' x b c (by rw [hmu 𝔭]; exact hc) hbc
  ·
    intro ℓ' hall
    by_contra hℓ'
    have hdvd : gI ⟨ℓ', hℓ'⟩ ∣ f :=
      (Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ _)) _).mul_left f₀
    obtain ⟨d, hd⟩ := hdvd
    have hc0 : ((gI ⟨ℓ', hℓ'⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) : ↥F₀) ≠ 0 := fun h =>
      (hgI ⟨ℓ', hℓ'⟩).2 (by rw [show gI ⟨ℓ', hℓ'⟩ = 0 from Subtype.ext h]; exact 𝔫.zero_mem)
    exact hinvIg ℓ' _ (hgI ⟨ℓ', hℓ'⟩).1 hc0 (hall ⟨_, hinvB _ d hd⟩)
  ·
    intro s hall
    rcases hnotSS s with hcase | ⟨g, hg⟩
    swap
    · exact hg (hall ⟨_, hCB g⟩)
    have hgSeq : gS s = hcase.choose := dif_pos hcase
    obtain ⟨⟨hs, hsm⟩, hs𝔫⟩ := hcase.choose_spec
    have hdvd : hcase.choose ∣ f := by
      rw [← hgSeq]
      exact (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ _)) _).mul_left f₀
    obtain ⟨d, hd⟩ := hdvd
    have hc0 : ((hcase.choose : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) : ↥F₀) ≠ 0 := fun h =>
      hs𝔫 (by rw [show hcase.choose = 0 from Subtype.ext h]; exact 𝔫.zero_mem)
    have hc0' : F₀.subtype ((hcase.choose : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) : ↥F₀) ≠ 0 := (map_ne_zero_iff _ F₀.subtype.injective).mpr hc0
    have hinv : (F₀.subtype ((hcase.choose : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) : ↥F₀))⁻¹ ∈ OSS s := by
      rw [← map_inv₀]
      exact hall ⟨_, hinvB _ d hd⟩
    apply (IsLocalRing.mem_maximalIdeal _).mp hsm
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hc0')⟩
  ·
    refine ⟨(𝔮 (lineInfty q)).map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ↥B), hmapP _ (hMIN _).1.1 hinf𝔮, fun x => (hLOC (lineInfty q) x).trans ⟨?_, ?_⟩⟩
    · rintro ⟨b, c, hc, hbc⟩; exact hHC _ (hMIN _).1.1 hinf𝔮 x b c hc hbc
    · rintro ⟨b, c, hc, hbc⟩; exact hHB _ (hMIN _).1.1 hinf𝔮 x b c hc hbc
  ·
    intro 𝔮' h𝔮'
    rw [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff, h𝔪Q] at h𝔮'
    subst h𝔮'
    intro x
    refine (hLOC (lineInfty q) x).trans ⟨?_, ?_⟩
    · rintro ⟨b, c, hc, hbc⟩; exact hHC _ (hMIN _).1.1 hinf𝔮 x b c hc hbc
    · rintro ⟨b, c, hc, hbc⟩; exact hHB _ (hMIN _).1.1 hinf𝔮 x b c hc hbc

end S_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_of_smooth_opens_chartAlgInf_descent
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_of_smooth_opens_chartAlgInf_descent (solution)
