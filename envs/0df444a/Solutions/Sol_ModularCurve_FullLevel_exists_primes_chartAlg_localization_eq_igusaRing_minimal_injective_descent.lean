-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_primes_chartAlg_localization_eq_igusaRing_minimal_injective_descent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/a55ecd45-37ed-5c05-be06-440d9ce858c0

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_primes_chartAlg_localization_eq_igusaRing_minimal_injective_descent
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

open _root_.Polynomial _root_.AlgebraicGeometry.Polynomial in

theorem map_reverse_ne_zero {A k : Type*} [CommRing A] [CommRing k] (r : A →+* k) (P : Polynomial A)
    (hP : P.map r ≠ 0) : P.reverse.map r ≠ 0 := by
  intro h
  apply hP
  ext n
  rw [Polynomial.coeff_map, Polynomial.coeff_zero]
  by_cases hn : n ≤ P.natDegree
  · have := congrArg (fun Q => Q.coeff (Polynomial.revAt P.natDegree n)) h
    simp only [Polynomial.coeff_map, Polynomial.coeff_reverse, Polynomial.revAt_invol, Polynomial.coeff_zero] at this
    exact this
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hn), map_zero]

theorem gauss_inv {A F : Type*} [CommRing A] [IsLocalRing A] [Field F] [Algebra A F]
    (V : ValuationSubring F) (j : F) (hj0 : j ≠ 0)
    (h : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) :
    ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j⁻¹ P ∈ V ∧ (Polynomial.aeval j⁻¹ P)⁻¹ ∈ V := by
  have hjV : j ∈ V ∧ j⁻¹ ∈ V := by
    have := h Polynomial.X (by rw [Polynomial.map_X]; exact Polynomial.X_ne_zero)
    rwa [Polynomial.aeval_X] at this
  intro P hP
  letI : Invertible (j⁻¹) := invertibleOfNonzero (inv_ne_zero hj0)
  have hinv : (⅟(j⁻¹) : F) = j := by rw [invOf_eq_inv, inv_inv]
  have key : Polynomial.aeval j⁻¹ P = Polynomial.aeval j P.reverse * (j⁻¹) ^ P.natDegree := by
    rw [Polynomial.aeval_def, Polynomial.aeval_def, ← Polynomial.eval₂_reverse_mul_pow (algebraMap A F) j⁻¹ P, hinv]
  obtain ⟨h1, h2⟩ := h P.reverse (map_reverse_ne_zero _ P hP)
  refine ⟨?_, ?_⟩
  · rw [key]; exact mul_mem h1 (pow_mem hjV.2 _)
  · rw [key, mul_inv, ← inv_pow, inv_inv]; exact mul_mem h2 (pow_mem hjV.1 _)

theorem not_C_dvd_iff {A : Type*} [CommRing A] [IsLocalRing A] (ϖ : A)
    (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) (P : Polynomial A) :
    ¬ (Polynomial.C ϖ ∣ P) ↔ P.map (IsLocalRing.residue A) ≠ 0 := by
  rw [not_iff_not, Polynomial.C_dvd_iff_dvd_coeff, Polynomial.ext_iff]
  refine forall_congr' fun n => ?_
  rw [Polynomial.coeff_map, Polynomial.coeff_zero, IsLocalRing.residue_eq_zero_iff, hϖ, Ideal.mem_span_singleton]

theorem adjoin_inv_eq {K F : Type*} [Field K] [Field F] [Algebra K F] (j : F) :
    IntermediateField.adjoin K ({j⁻¹} : Set F) = IntermediateField.adjoin K ({j} : Set F) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self _ _)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have := inv_mem (IntermediateField.mem_adjoin_simple_self K j⁻¹)
    rwa [inv_inv] at this

set_option maxHeartbeats 3200000 in

theorem coreFin
    {A₀ : Type} [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ϖ₀ : A₀) (hϖ₀ : IsLocalRing.maximalIdeal A₀ = Ideal.span {ϖ₀})
    {K : Type} [Field K] [Algebra A₀ K] [IsFractionRing A₀ K]
    {F : Type} [Field F] [Algebra A₀ F] [Algebra K F] [IsScalarTower A₀ K F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental A₀ j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K ({j} : Set F)) F)
    {Λ : Type} (V : Λ → ValuationSubring F)
    (hVA : ∀ (l : Λ) (a : A₀), algebraMap A₀ F a ∈ V l)
    (hVm : ∀ (l : Λ), ∀ a ∈ IsLocalRing.maximalIdeal A₀, algebraMap A₀ F a ∈ (V l).nonunits)
    (hVj : ∀ (l : Λ) (P : Polynomial A₀), P.map (IsLocalRing.residue A₀) ≠ 0 →
      Polynomial.aeval j P ∈ V l ∧ (Polynomial.aeval j P)⁻¹ ∈ V l)
    (hVinj : Function.Injective V)
    (hident : ∀ V' : ValuationSubring F, (∀ a : A₀, algebraMap A₀ F a ∈ V') →
      algebraMap A₀ F ϖ₀ ∈ V'.nonunits →
      (∀ P : Polynomial A₀, ¬ (Polynomial.C ϖ₀ ∣ P) → Polynomial.aeval j P ∈ V' ∧ (Polynomial.aeval j P)⁻¹ ∈ V') →
      ∃ l, V' = V l) :
    ∃ 𝔮 : Λ → Ideal ↥(TwoChartIntegralModel.chartAlgFin A₀ F j),
      (∀ (l : Λ) (x : F), x ∈ V l ↔
        ∃ b c : ↥(TwoChartIntegralModel.chartAlgFin A₀ F j), c ∉ 𝔮 l ∧ x * (c : F) = (b : F)) ∧
      (∀ l, 𝔮 l ∈ (Ideal.map (algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ F j))
        (IsLocalRing.maximalIdeal A₀)).minimalPrimes) ∧
      Function.Injective 𝔮 ∧
      (∀ 𝔮' : Ideal ↥(TwoChartIntegralModel.chartAlgFin A₀ F j),
        𝔮' ∈ (Ideal.map (algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ F j))
          (IsLocalRing.maximalIdeal A₀)).minimalPrimes → ∃ l, 𝔮' = 𝔮 l) := by
  classical

  have hbr := fun l => AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
    A₀ K F j htj hFD hsep (V l) (hVA l) (hVm l) (hVj l)
  choose 𝔓 h𝔓 using fun l => (hbr l).2.1

  have hI : Ideal.map (algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ F j)) (IsLocalRing.maximalIdeal A₀) =
      Ideal.span {algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ F j) ϖ₀} := by
    rw [hϖ₀, Ideal.map_span, Set.image_singleton]
  have hinjC : Function.Injective (algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ F j)) := by
    intro a b h
    have : algebraMap A₀ F a = algebraMap A₀ F b := by
      have := congrArg (fun z : ↥(TwoChartIntegralModel.chartAlgFin A₀ F j) => (z : F)) h
      simpa using this
    rw [IsScalarTower.algebraMap_apply A₀ K F, IsScalarTower.algebraMap_apply A₀ K F] at this
    exact IsFractionRing.injective A₀ K ((algebraMap K F).injective this)
  have hϖ₀0 : ϖ₀ ≠ 0 := by
    intro h
    apply IsDiscreteValuationRing.not_a_field A₀
    rw [hϖ₀, h, Ideal.span_singleton_eq_bot]
  have hmin : ∀ l, 𝔓 l ∈ (Ideal.map (algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ F j))
      (IsLocalRing.maximalIdeal A₀)).minimalPrimes := by
    intro l
    obtain ⟨hprime, hht, -, hconst, -⟩ := h𝔓 l
    haveI := hprime
    haveI : (𝔓 l).FiniteHeight := Ideal.finiteHeight_iff_lt.mpr (Or.inr (by rw [hht]; exact ENat.one_lt_top))
    have hle : Ideal.map (algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ F j)) (IsLocalRing.maximalIdeal A₀) ≤ 𝔓 l := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      exact hconst a ha
    refine Ideal.mem_minimalPrimes_of_height_eq hle ?_
    rw [hht, hI]
    apply Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
    exact mem_nonZeroDivisors_of_ne_zero (fun h => hϖ₀0 (hinjC (h.trans (map_zero _).symm)))
  refine ⟨𝔓, fun l => (h𝔓 l).2.2.2.2, hmin, ?_, ?_⟩
  ·
    intro l l' hll
    apply hVinj
    ext x
    rw [(h𝔓 l).2.2.2.2 x, (h𝔓 l').2.2.2.2 x, hll]
  ·
    intro 𝔮' h𝔮'
    rw [hI] at h𝔮'
    have hprimeϖ : Prime ϖ₀ := by
      have hirr : Irreducible ϖ₀ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ₀).mpr hϖ₀
      exact hirr.prime
    obtain ⟨V', -, hCV', h𝔮'V', hϖV', hPV'⟩ :=
      AlgebraicCurve.TwoChartIntegralModel.exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
        A₀ K F j htj hFD hsep ϖ₀ hprimeϖ 𝔮' h𝔮'
    have hAV' : ∀ a : A₀, algebraMap A₀ F a ∈ V' := fun a => by
      have := hCV' (algebraMap A₀ _ a)
      simpa using this
    obtain ⟨l, rfl⟩ := hident V' hAV' hϖV' hPV'
    refine ⟨l, ?_⟩
    ext b
    rw [h𝔮'V' b, (h𝔓 l).2.2.1 b]

set_option maxHeartbeats 3200000 in

theorem core
    {A₀ : Type} [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ϖ₀ : A₀) (hϖ₀ : IsLocalRing.maximalIdeal A₀ = Ideal.span {ϖ₀})
    {K : Type} [Field K] [Algebra A₀ K] [IsFractionRing A₀ K]
    {F : Type} [Field F] [Algebra A₀ F] [Algebra K F] [IsScalarTower A₀ K F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental A₀ j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K ({j} : Set F)) F)
    {Λ : Type} (V : Λ → ValuationSubring F)
    (hVA : ∀ (l : Λ) (a : A₀), algebraMap A₀ F a ∈ V l)
    (hVm : ∀ (l : Λ), ∀ a ∈ IsLocalRing.maximalIdeal A₀, algebraMap A₀ F a ∈ (V l).nonunits)
    (hVj : ∀ (l : Λ) (P : Polynomial A₀), P.map (IsLocalRing.residue A₀) ≠ 0 →
      Polynomial.aeval j P ∈ V l ∧ (Polynomial.aeval j P)⁻¹ ∈ V l)
    (hVinj : Function.Injective V)
    (hident : ∀ V' : ValuationSubring F, (∀ a : A₀, algebraMap A₀ F a ∈ V') →
      algebraMap A₀ F ϖ₀ ∈ V'.nonunits →
      (∀ P : Polynomial A₀, ¬ (Polynomial.C ϖ₀ ∣ P) → Polynomial.aeval j P ∈ V' ∧ (Polynomial.aeval j P)⁻¹ ∈ V') →
      ∃ l, V' = V l)
    (S : Set F) (hS : S = {j} ∨ S = {j⁻¹}) :
    ∃ 𝔮 : Λ → Ideal ↥(TwoChartIntegralModel.chartAlg A₀ F S),
      (∀ (l : Λ) (x : F), x ∈ V l ↔
        ∃ b c : ↥(TwoChartIntegralModel.chartAlg A₀ F S), c ∉ 𝔮 l ∧ x * (c : F) = (b : F)) ∧
      (∀ l, 𝔮 l ∈ (Ideal.map (algebraMap A₀ ↥(TwoChartIntegralModel.chartAlg A₀ F S))
        (IsLocalRing.maximalIdeal A₀)).minimalPrimes) ∧
      Function.Injective 𝔮 ∧
      (∀ 𝔮' : Ideal ↥(TwoChartIntegralModel.chartAlg A₀ F S),
        𝔮' ∈ (Ideal.map (algebraMap A₀ ↥(TwoChartIntegralModel.chartAlg A₀ F S))
          (IsLocalRing.maximalIdeal A₀)).minimalPrimes → ∃ l, 𝔮' = 𝔮 l) := by
  rcases hS with rfl | rfl
  · exact coreFin ϖ₀ hϖ₀ j htj hFD hsep V hVA hVm hVj hVinj hident
  · haveI : Fact (j⁻¹ ≠ 0) := ⟨inv_ne_zero (Fact.out : j ≠ 0)⟩
    have htj' : Transcendental A₀ j⁻¹ := fun h => htj (IsAlgebraic.inv_iff.mp h)
    have hFD' : FiniteDimensional ↥(IntermediateField.adjoin K ({j⁻¹} : Set F)) F := by
      rw [adjoin_inv_eq]; exact hFD
    have hsep' : Algebra.IsSeparable ↥(IntermediateField.adjoin K ({j⁻¹} : Set F)) F := by
      rw [adjoin_inv_eq]; exact hsep
    have hVj' := fun l => gauss_inv (V l) j (Fact.out : j ≠ 0) (hVj l)
    have hident' : ∀ V' : ValuationSubring F, (∀ a : A₀, algebraMap A₀ F a ∈ V') →
        algebraMap A₀ F ϖ₀ ∈ V'.nonunits →
        (∀ P : Polynomial A₀, ¬ (Polynomial.C ϖ₀ ∣ P) → Polynomial.aeval j⁻¹ P ∈ V' ∧ (Polynomial.aeval j⁻¹ P)⁻¹ ∈ V') →
        ∃ l, V' = V l := by
      intro V' h1 h2 h3
      refine hident V' h1 h2 ?_
      intro P hP
      have h3' : ∀ P : Polynomial A₀, P.map (IsLocalRing.residue A₀) ≠ 0 →
          Polynomial.aeval j⁻¹ P ∈ V' ∧ (Polynomial.aeval j⁻¹ P)⁻¹ ∈ V' :=
        fun P hP => h3 P ((not_C_dvd_iff ϖ₀ hϖ₀ P).mpr hP)
      have := gauss_inv V' j⁻¹ (inv_ne_zero (Fact.out : j ≠ 0)) h3' P ((not_C_dvd_iff ϖ₀ hϖ₀ P).mp hP)
      rwa [inv_inv] at this
    exact coreFin ϖ₀ hϖ₀ j⁻¹ htj' hFD' hsep' V hVA hVm hVj' hVinj hident'

end E148LC

namespace E148LC
theorem mem_nonunits_comap_iff {K L : Type*} [Field K] [Field L] (O : ValuationSubring L) (f : K →+* L) (x : K) :
    x ∈ (O.comap f).nonunits ↔ f x ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap,
    map_inv₀, map_eq_zero_iff f f.injective]
end E148LC

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 16000000 in
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
    (S : Set ↥F₀) (hS : S = {(⟨_, hjF₀⟩ : ↥F₀)} ∨ S = {(⟨_, hjF₀⟩ : ↥F₀)⁻¹}) :
    ∃ 𝔮 : CuspidalType.ProjLine q → Ideal ↥(TwoChartIntegralModel.chartAlg A₀ ↥F₀ S),

      (∀ ℓ (x : ↥F₀), (x : ↥(fieldBar q M')) ∈ OIg ℓ ↔
        ∃ b c : ↥(TwoChartIntegralModel.chartAlg A₀ ↥F₀ S), c ∉ 𝔮 ℓ ∧ x * (c : ↥F₀) = (b : ↥F₀)) ∧

      (∀ ℓ, 𝔮 ℓ ∈ (Ideal.map (algebraMap A₀ ↥(TwoChartIntegralModel.chartAlg A₀ ↥F₀ S)) (maximalIdeal A₀)).minimalPrimes) ∧

      Function.Injective 𝔮 ∧

      (∀ 𝔮' : Ideal ↥(TwoChartIntegralModel.chartAlg A₀ ↥F₀ S),
        𝔮' ∈ (Ideal.map (algebraMap A₀ ↥(TwoChartIntegralModel.chartAlg A₀ ↥F₀ S)) (maximalIdeal A₀)).minimalPrimes →
          ∃ ℓ, 𝔮' = 𝔮 ℓ) := by
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

  let V : CuspidalType.ProjLine q → ValuationSubring ↥F₀ := fun l => (OIg l).comap F₀.subtype
  have hV : ∀ l (x : ↥F₀), x ∈ V l ↔ (x : ↥(fieldBar q M')) ∈ OIg l := fun _ _ => ValuationSubring.mem_comap
  have hVnu : ∀ l (x : ↥F₀), x ∈ (V l).nonunits ↔ (x : ↥(fieldBar q M')) ∈ (OIg l).nonunits := fun l x =>
    E148LC.mem_nonunits_comap_iff (OIg l) F₀.subtype x

  have heA : ∀ a : A₀, ((algebraMap A₀ ↥F₀ a : ↥F₀) : ↥(fieldBar q M')) =
      ((algebraMap ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') (e₀ a) : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')) : ↥(fieldBar q M')) := fun a => by
    rw [hj₀, halgT, he₀]
  have hVA : ∀ l (a : A₀), algebraMap A₀ ↥F₀ a ∈ V l := fun l a => by
    rw [hV, heA]; exact hR1 l (e₀ a)
  have hVm : ∀ l, ∀ a ∈ IsLocalRing.maximalIdeal A₀, algebraMap A₀ ↥F₀ a ∈ (V l).nonunits := fun l a ha => by
    rw [hVnu, heA]; exact hR2 l (e₀ a) ((E150I.mem_maximalIdeal_iff_of_ringEquiv e₀ a).mpr ha)

  have hcompat : (algebraMap ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')).comp e₀.toRingHom = Φ.toRingHom.comp (algebraMap A₀ ↥F₀) := by
    refine RingHom.ext fun a => ?_
    change Φ (algebraMap A₀ ↥F₀ (e₀.symm (e₀ a))) = Φ (algebraMap A₀ ↥F₀ a)
    rw [e₀.symm_apply_apply]
  have haeval : ∀ P : Polynomial A₀, Φ (Polynomial.aeval (⟨_, hjF₀⟩ : ↥F₀) P) = Polynomial.aeval j₁ (P.map e₀.toRingHom) :=
    fun P => Polynomial.map_aeval_eq_aeval_map hcompat P (⟨_, hjF₀⟩ : ↥F₀)
  haveI : IsLocalHom e₀.toRingHom := ⟨fun a h => (E150I.isUnit_iff_of_ringEquiv e₀ a).mp h⟩
  have hmapres : ∀ P : Polynomial A₀, P.map (IsLocalRing.residue A₀) ≠ 0 →
      (P.map e₀.toRingHom).map (IsLocalRing.residue ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ)))) ≠ 0 := by
    intro P hP h
    apply hP
    rw [Polynomial.map_map, ← IsLocalRing.ResidueField.map_comp_residue, ← Polynomial.map_map] at h
    exact (Polynomial.map_eq_zero_iff (IsLocalRing.ResidueField.map e₀.toRingHom).injective).mp h
  have hVj : ∀ l (P : Polynomial A₀), P.map (IsLocalRing.residue A₀) ≠ 0 →
      Polynomial.aeval (⟨_, hjF₀⟩ : ↥F₀) P ∈ V l ∧ (Polynomial.aeval (⟨_, hjF₀⟩ : ↥F₀) P)⁻¹ ∈ V l := by
    intro l P hP
    obtain ⟨h1, h2⟩ := hR3 l (P.map e₀.toRingHom) (hmapres P hP)
    rw [← haeval, hΦ] at h1
    rw [← haeval, ← map_inv₀, hΦ] at h2
    exact ⟨(hV _ _).mpr h1, (hV _ _).mpr h2⟩

  have hVinj : Function.Injective V := by
    intro l l' h
    apply hR4 l l'
    intro f
    rw [← hΦ' f, ← hV l, ← hV l', h]

  have hident : ∀ V' : ValuationSubring ↥F₀, (∀ a : A₀, algebraMap A₀ ↥F₀ a ∈ V') →
      algebraMap A₀ ↥F₀ ϖ₀ ∈ V'.nonunits →
      (∀ P : Polynomial A₀, ¬ (Polynomial.C ϖ₀ ∣ P) →
        Polynomial.aeval (⟨_, hjF₀⟩ : ↥F₀) P ∈ V' ∧ (Polynomial.aeval (⟨_, hjF₀⟩ : ↥F₀) P)⁻¹ ∈ V') → ∃ l, V' = V l := by
    intro V' h1 h2 h3
    let V'' : ValuationSubring ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') := V'.comap Φ.symm.toRingHom
    have hV'' : ∀ t, t ∈ V'' ↔ Φ.symm t ∈ V' := fun _ => ValuationSubring.mem_comap
    have hϖ₁ : IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) = Ideal.span {e₀ ϖ₀} := E150I.maximalIdeal_eq_span_of_ringEquiv e₀ ϖ₀ hϖ₀
    have halg1 : ∀ a : ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') a = Φ (algebraMap A₀ ↥F₀ (e₀.symm a)) := fun _ => rfl
    have hc1 : ∀ a : ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') a ∈ V'' := fun a => by
      rw [hV'', halg1, Φ.symm_apply_apply]; exact h1 _
    have hc2 : algebraMap ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') (e₀ ϖ₀) ∈ V''.nonunits := by
      refine (E148LC.mem_nonunits_comap_iff V' Φ.symm.toRingHom _).mpr ?_
      change Φ.symm (algebraMap ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') (e₀ ϖ₀)) ∈ V'.nonunits
      rw [halg1, Φ.symm_apply_apply, e₀.symm_apply_apply]
      exact h2
    have hc3 : ∀ P : Polynomial ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))), ¬ (Polynomial.C (e₀ ϖ₀) ∣ P) →
        Polynomial.aeval j₁ P ∈ V'' ∧ (Polynomial.aeval j₁ P)⁻¹ ∈ V'' := by
      intro P hP
      have hPP : (P.map e₀.symm.toRingHom).map e₀.toRingHom = P := by
        rw [Polynomial.map_map, RingEquiv.toRingHom_comp_symm_toRingHom, Polynomial.map_id]
      have hP₀ : ¬ (Polynomial.C ϖ₀ ∣ P.map e₀.symm.toRingHom) := by
        rintro ⟨Q, hQ⟩
        apply hP
        refine ⟨Q.map e₀.toRingHom, ?_⟩
        rw [← hPP, hQ, Polynomial.map_mul, Polynomial.map_C]
        rfl
      obtain ⟨k1, k2⟩ := h3 _ hP₀
      have hev : Polynomial.aeval j₁ P = Φ (Polynomial.aeval (⟨_, hjF₀⟩ : ↥F₀) (P.map e₀.symm.toRingHom)) := by
        rw [haeval, hPP]
      refine ⟨(hV'' _).mpr ?_, (hV'' _).mpr ?_⟩
      · rw [hev, Φ.symm_apply_apply]; exact k1
      · rw [hev, ← map_inv₀, Φ.symm_apply_apply]; exact k2
    obtain ⟨l, hl⟩ := hBI (e₀ ϖ₀) hϖ₁ V'' hc1 hc2 hc3
    refine ⟨l, ?_⟩
    ext x
    rw [hV, ← hΦ x, ← hl (Φ x), hV'', Φ.symm_apply_apply]

  obtain ⟨𝔮, hloc, hmin, hinj, hsurj⟩ :=
    E148LC.core ϖ₀ hϖ₀ (⟨_, hjF₀⟩ : ↥F₀) htj0 hFDF hsepF V hVA hVm hVj hVinj hident S hS
  exact ⟨𝔮, fun l x => (hV l x).symm.trans (hloc l x), hmin, hinj, hsurj⟩

end S_ModularCurve_FullLevel_exists_primes_chartAlg_localization_eq_igusaRing_minimal_injective_descent
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_primes_chartAlg_localization_eq_igusaRing_minimal_injective_descent (solution)
