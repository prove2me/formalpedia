-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.pernodeConclusion_traces_of_rigidChart_linkedScalars_of_eq_three_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/92cc56b6-0486-5143-abf5-a0c4f1799e22

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

import Theorems.Thm_Algebra_IsInvariant_moduleFinite_and_finiteType_of_finiteType
import Theorems.Thm_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_isAdicComplete_maximalIdeal
import Theorems.Thm_ModularCurve_UVCrossingModel_isLocalRing_of_not_isUnit
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import Theorems.Thm_Subring_exists_forall_algEquiv_apply_eq_and_forall_mem_and_not_mem_valuationSubring
import Theorems.Thm_ModularCurve_FullLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_FullLevel_exists_finite_subgroup_forall_mem_iff_exists_isLevelAutAt_of_exists_ringHom_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_FullLevel_exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_FullLevel_map_mem_chartAlgFin_of_isLevelAutAt
import Theorems.Thm_ModularCurve_FullLevel_Diamond_qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_FullLevel_Diamond_pernodeConclusion_of_pernodeHyps_of_rigidChart_linkedScalars_of_eq_three_of_dvd
import Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_invariant_notMem_of_endChartPole_of_rigidChart_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_residuallyTranscendental_trace_of_igusaBranch_of_rigidChart_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_FullLevel_Diamond_levelLaws_trace_of_igusaBranch_of_rigidChart_of_eq_levelH_inf_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_pernodeConclusion_traces_of_rigidChart_linkedScalars_of_eq_three_of_dvd
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.instIsElliptic_tateBase ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk AdicCompletion.map_smul_of AdicCompletion.algebraMap_of AdicCompletion.stabilizer_smul_of AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_one GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂"
p2m_attr_erase "simp" "PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.LevelN.coe_jGen ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one"
p2m_attr_erase "simp" "ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun"
p2m_attr_erase "simp" "KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 0
set_option maxHeartbeats 0

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace S3C4Pernode

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section PartB

variable (G : Subgroup (K ≃ₐ[k] K))
  (B : Subring K) (hBG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ B → σ f ∈ B)
  (Õ : Subring K) [IsLocalRing ↥Õ] (hBÕ : B ≤ Õ)
  (hloc : ∀ f : K, f ∈ Õ ↔ ∃ g h : K, g ∈ B ∧ h ∈ B ∧ (∀ hh : h ∈ Õ, IsUnit (⟨h, hh⟩ : ↥Õ)) ∧ f * h = g)

include hBG hBÕ hloc

end PartB

end S3C4Pernode

namespace S3C4Glue

open IsLocalRing Polynomial

theorem isUnit_mk_iff {K : Type} [Field K] (O : Subring K) (x : K) (hx : x ∈ O) :
    IsUnit (⟨x, hx⟩ : ↥O) ↔ ∃ y : K, y ∈ O ∧ x * y = 1 := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨((u⁻¹ : (↥O)ˣ) : ↥O), ((u⁻¹ : (↥O)ˣ) : ↥O).2, ?_⟩
    have h := congrArg (fun z : ↥O => (z : K)) u.mul_inv
    rw [hu] at h
    simpa using h
  · rintro ⟨y, hy, hxy⟩
    exact IsUnit.of_mul_eq_one (b := (⟨y, hy⟩ : ↥O)) (Subtype.ext hxy)

theorem mem_maximalIdeal_iff_lt {K : Type} [Field K] (V : ValuationSubring K) (x : K) (hx : x ∈ V) :
    (⟨x, hx⟩ : ↥V) ∈ maximalIdeal ↥V ↔ V.valuation x < 1 :=
  V.valuation_lt_one_iff ⟨x, hx⟩

noncomputable def toVal {K R : Type} [Field K] [CommRing R] [Algebra R K] (C : Subalgebra R K)
    (V : ValuationSubring K) (hCV : ∀ b : ↥C, (b : K) ∈ V) : ↥C →+* ↥V where
  toFun b := ⟨(b : K), hCV b⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

theorem att_of_mem_closure {k K : Type} [Field k] [Field K] [Algebra k K]
    {Γ : Type} [Group Γ] (S₀ S₁ : Subgroup Γ) (Att : Γ → (K ≃ₐ[k] K) → Prop)
    (huniq : ∀ γ : Γ, γ ∈ S₀ → ∀ τ τ' : K ≃ₐ[k] K, Att γ τ → Att γ τ' → τ = τ')
    (hmul : ∀ γ δ : Γ, γ ∈ S₀ → δ ∈ S₀ → ∀ τ σ : K ≃ₐ[k] K, Att γ τ → Att δ σ → Att (δ * γ) (τ * σ))
    (hone : Att 1 1)
    (hex : ∀ γ : Γ, γ ∈ S₀ → ∃ τ : K ≃ₐ[k] K, Att γ⁻¹ τ)
    (G : Subgroup (K ≃ₐ[k] K))
    (hG : G = Subgroup.closure {τ : K ≃ₐ[k] K | ∃ γ : Γ, γ ∈ S₁ ∧ γ ∈ S₀ ∧ Att γ⁻¹ τ}) :
    ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∃ γ : Γ, γ ∈ S₁ ∧ γ ∈ S₀ ∧ Att γ⁻¹ τ := by
  intro τ hτ
  rw [hG] at hτ
  refine Subgroup.closure_induction (p := fun τ _ => ∃ γ : Γ, γ ∈ S₁ ∧ γ ∈ S₀ ∧ Att γ⁻¹ τ) ?_ ?_ ?_ ?_ hτ
  · intro τ h; exact h
  · exact ⟨1, S₁.one_mem, S₀.one_mem, by rw [inv_one]; exact hone⟩
  · rintro τ σ - - ⟨γ, hγ1, hγ0, hτ⟩ ⟨δ, hδ1, hδ0, hσ⟩
    refine ⟨γ * δ, S₁.mul_mem hγ1 hδ1, S₀.mul_mem hγ0 hδ0, ?_⟩
    rw [mul_inv_rev]
    exact hmul γ⁻¹ δ⁻¹ (S₀.inv_mem hγ0) (S₀.inv_mem hδ0) τ σ hτ hσ
  · rintro τ - ⟨γ, hγ1, hγ0, hτ⟩
    obtain ⟨σ, hσ⟩ := hex γ⁻¹ (S₀.inv_mem hγ0)
    rw [inv_inv] at hσ
    have h1 : Att (γ * γ⁻¹) (τ * σ) := hmul γ⁻¹ γ (S₀.inv_mem hγ0) hγ0 τ σ hτ hσ
    rw [mul_inv_cancel] at h1
    have h2 : τ * σ = 1 := huniq 1 S₀.one_mem _ _ h1 hone
    have h3 : τ⁻¹ = σ := inv_eq_of_mul_eq_one_right h2
    refine ⟨γ⁻¹, S₁.inv_mem hγ1, S₀.inv_mem hγ0, ?_⟩
    rw [inv_inv, h3]
    exact hσ

theorem C3aux_exists_emb (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (m : ℕ) [NeZero m]
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ m) :
    ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / m) := by
  haveI hQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h := AlgebraicClosure.isAlgebraic ℚ
    convert h
    all_goals first | rfl | skip
  haveI : Algebra.IsAlgebraic ℚ ↥k₀ :=
    Algebra.IsAlgebraic.of_injective (k₀.val) (k₀.val).toRingHom.injective
  have hmin : minpoly ℚ ξ = Polynomial.cyclotomic m ℚ :=
    (Polynomial.cyclotomic_eq_minpoly_rat hξ (Nat.pos_of_ne_zero (NeZero.ne m))).symm
  have hroot : Complex.exp (2 * Real.pi * Complex.I / m) ∈ (minpoly ℚ ξ).rootSet ℂ := by
    rw [hmin, Polynomial.mem_rootSet]
    refine ⟨Polynomial.cyclotomic_ne_zero m ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact (Polynomial.isRoot_cyclotomic_iff.mpr (Complex.isPrimitiveRoot_exp m (NeZero.ne m))).eq_zero
  rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ ξ] at hroot
  obtain ⟨ψ, hψ⟩ := hroot
  exact ⟨ψ.toRingHom, hψ⟩

open IsLocalRing

theorem apply_eq_self_of_frac {k K : Type} [Field k] [Field K] [Algebra k K] {R : Type} [CommRing R] [Algebra R K]
    (B : Subalgebra R K) (hfrac : ∀ f : K, ∃ g h : ↥B, (h : K) ≠ 0 ∧ f * (h : K) = (g : K))
    (σ : K ≃ₐ[k] K) (hσ : ∀ f : K, f ∈ B → σ f = f) : ∀ f : K, σ f = f := by
  intro f
  obtain ⟨g, h, hh0, hfh⟩ := hfrac f
  have e1 : σ f * σ (h : K) = σ (g : K) := by rw [← map_mul, hfh]
  rw [hσ _ h.2, hσ _ g.2, ← hfh] at e1
  exact mul_right_cancel₀ hh0 e1

theorem exists_eq_pow_of_stabilises {k K : Type} [Field k] [Field K] [Algebra k K]
    {R : Type} [CommRing R] [Algebra R K]
    {Γ : Type} [Group Γ] (S₀ S₁ : Subgroup Γ) (Att : Γ → (K ≃ₐ[k] K) → Prop)
    (G : Subgroup (K ≃ₐ[k] K))
    (hGatt : ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∃ γ : Γ, γ ∈ S₁ ∧ γ ∈ S₀ ∧ Att γ⁻¹ τ)
    (B : Subalgebra R K) (W : ValuationSubring K)
    (hfrac : ∀ f : K, ∃ g h : ↥B, (h : K) ≠ 0 ∧ f * (h : K) = (g : K))
    (τ₀ : K ≃ₐ[k] K) (n : ℕ)
    (h72 : ∀ γ : Γ, γ ∈ S₁ → γ ∈ S₀ → ∀ τ : K ≃ₐ[k] K, Att γ⁻¹ τ → (∀ f : K, f ∈ W ↔ τ f ∈ W) →
      ∃ m : ℕ, m < n ∧ ∀ f : K, f ∈ B → τ f = (τ₀ ^ m) f)
    (O : Subring K) (hOW : ∀ f : K, f ∈ O → f ∈ W)
    (hR7oneO : ∀ γ : Γ, γ ∈ S₁ → γ ∈ S₀ → ∀ τ : K ≃ₐ[k] K, Att γ⁻¹ τ →
      (∀ f : K, f ∈ O → τ f ∈ W) → ∀ f : K, f ∈ W ↔ τ f ∈ W) :
    ∀ σ : K ≃ₐ[k] K, σ ∈ G → (∀ f : K, f ∈ O ↔ σ f ∈ O) → ∃ j : ℕ, ∀ f : K, σ f = (τ₀ ^ j) f := by
  intro σ hσ hstab
  obtain ⟨γ, h1, h0, hatt⟩ := hGatt σ hσ
  have hinto : ∀ f : K, f ∈ O → σ f ∈ W := fun f hf => hOW _ ((hstab f).mp hf)
  have hW : ∀ f : K, f ∈ W ↔ σ f ∈ W := hR7oneO γ h1 h0 σ hatt hinto
  obtain ⟨m, -, hm⟩ := h72 γ h1 h0 σ hatt hW
  refine ⟨m, ?_⟩
  have key := apply_eq_self_of_frac B hfrac ((τ₀ ^ m)⁻¹ * σ) (fun f hf => by
    rw [AlgEquiv.mul_apply, hm f hf, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply])
  intro f
  have h1 := key f
  rw [AlgEquiv.mul_apply] at h1
  have h2 := congrArg (τ₀ ^ m) h1
  rwa [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at h2

def fixedPart {k K : Type} [Field k] [Field K] [Algebra k K] (G : Subgroup (K ≃ₐ[k] K)) (O : Subring K) : Subring K where
  carrier := {f | f ∈ O ∧ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f}
  mul_mem' := fun {a b} ha hb => ⟨O.mul_mem ha.1 hb.1, fun σ hσ => by rw [map_mul, ha.2 σ hσ, hb.2 σ hσ]⟩
  one_mem' := ⟨O.one_mem, fun σ _ => map_one σ⟩
  add_mem' := fun {a b} ha hb => ⟨O.add_mem ha.1 hb.1, fun σ hσ => by rw [map_add, ha.2 σ hσ, hb.2 σ hσ]⟩
  zero_mem' := ⟨O.zero_mem, fun σ _ => map_zero σ⟩
  neg_mem' := fun {a} ha => ⟨O.neg_mem ha.1, fun σ hσ => by rw [map_neg, ha.2 σ hσ]⟩

theorem mem_fixedPart {k K : Type} [Field k] [Field K] [Algebra k K] (G : Subgroup (K ≃ₐ[k] K)) (O : Subring K) (f : K) :
    f ∈ fixedPart G O ↔ f ∈ O ∧ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f := Iff.rfl

theorem fixedPart_le {k K : Type} [Field k] [Field K] [Algebra k K] (G : Subgroup (K ≃ₐ[k] K)) (O : Subring K) :
    fixedPart G O ≤ O := fun _ hf => hf.1

@[reducible] noncomputable def subringAction {k K : Type} [Field k] [Field K] [Algebra k K] (G : Subgroup (K ≃ₐ[k] K)) (B : Subring K)
    (hBG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ B → σ f ∈ B) : MulSemiringAction ↥G ↥B where
  smul σ b := ⟨(σ : K ≃ₐ[k] K) (b : K), hBG σ σ.2 _ b.2⟩
  one_smul b := Subtype.ext (by change ((1 : ↥G) : K ≃ₐ[k] K) (b : K) = b; rw [OneMemClass.coe_one, AlgEquiv.one_apply])
  mul_smul σ τ b := Subtype.ext (by
    change ((σ * τ : ↥G) : K ≃ₐ[k] K) (b : K) = (σ : K ≃ₐ[k] K) ((τ : K ≃ₐ[k] K) (b : K))
    rw [Subgroup.coe_mul, AlgEquiv.mul_apply])
  smul_zero σ := Subtype.ext (by change (σ : K ≃ₐ[k] K) ((0 : ↥B) : K) = 0; simp)
  smul_add σ a b := Subtype.ext (by change (σ : K ≃ₐ[k] K) ((a + b : ↥B) : K) = _; simp; rfl)
  smul_one σ := Subtype.ext (by change (σ : K ≃ₐ[k] K) ((1 : ↥B) : K) = 1; simp)
  smul_mul σ a b := Subtype.ext (by change (σ : K ≃ₐ[k] K) ((a * b : ↥B) : K) = _; simp; rfl)

theorem noetherian_and_finite_fixedPart {k K : Type} [Field k] [Field K] [Algebra k K]
    {R : Type} [CommRing R] [IsNoetherianRing R] [Algebra R K]
    (G : Subgroup (K ≃ₐ[k] K)) (hGfin : Finite ↥G)
    (hRfix : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ r : R, σ (algebraMap R K r) = algebraMap R K r)
    (Bc : Subalgebra R K) (hBcG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ Bc → σ f ∈ Bc)
    (hft : Algebra.FiniteType R ↥Bc) :
    IsNoetherianRing ↥(fixedPart G Bc.toSubring) ∧
    ∀ (hle : fixedPart G Bc.toSubring ≤ Bc.toSubring),
      letI := (Subring.inclusion hle).toAlgebra; Module.Finite ↥(fixedPart G Bc.toSubring) ↥Bc.toSubring := by
  classical
  haveI := hGfin
  set A : Subring K := fixedPart G Bc.toSubring with hA
  set B : Subring K := Bc.toSubring with hB
  have hle0 : A ≤ B := fixedPart_le G Bc.toSubring
  have hBG' : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ B → σ f ∈ B := fun σ hσ f hf => hBcG σ hσ f hf

  let φB : R →+* ↥B :=
    { toFun := fun r => ⟨algebraMap R K r, Bc.algebraMap_mem r⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  let φA : R →+* ↥A :=
    { toFun := fun r => ⟨algebraMap R K r, ⟨Bc.algebraMap_mem r, fun σ hσ => hRfix σ hσ r⟩⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }

  have main : ∀ (hle : A ≤ B), letI := (Subring.inclusion hle).toAlgebra;
      Module.Finite ↥A ↥B ∧ IsNoetherianRing ↥A := by
    intro hle
    letI algAB : Algebra ↥A ↥B := (Subring.inclusion hle).toAlgebra
    letI algRB : Algebra R ↥B := Bc.algebra
    letI algRA : Algebra R ↥A := φA.toAlgebra
    haveI : IsScalarTower R ↥A ↥B := IsScalarTower.of_algebraMap_eq (fun r => Subtype.ext rfl)
    haveI : FaithfulSMul ↥A ↥B := by
      rw [faithfulSMul_iff_algebraMap_injective]
      intro a b hab
      exact Subtype.ext (congrArg (fun z : ↥B => (z : K)) hab)
    letI act : MulSemiringAction ↥G ↥B := subringAction G B hBG'
    haveI : Algebra.IsInvariant ↥A ↥B ↥G := by
      refine ⟨fun b hb => ?_⟩
      refine ⟨⟨(b : K), ⟨b.2, fun σ hσ => ?_⟩⟩, Subtype.ext rfl⟩
      exact congrArg (fun z : ↥B => (z : K)) (hb ⟨σ, hσ⟩)

    haveI : Algebra.FiniteType R ↥B := hft
    obtain ⟨h1, h2⟩ := Algebra.IsInvariant.moduleFinite_and_finiteType_of_finiteType R ↥A ↥B ↥G
    exact ⟨h1, Algebra.FiniteType.isNoetherianRing R ↥A⟩
  exact ⟨(main hle0).2, fun hle => (main hle).1⟩

open IsLocalRing

noncomputable def restrictSubalg {k K : Type} [Field k] [Field K] [Algebra k K] {R : Type} [CommRing R] [Algebra R K]
    (C : Subalgebra R K) (σ : K ≃ₐ[k] K) (hσ : ∀ f : K, f ∈ C → σ f ∈ C) : ↥C →+* ↥C where
  toFun b := ⟨σ (b : K), hσ _ b.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

theorem restrictSubalg_apply_coe {k K : Type} [Field k] [Field K] [Algebra k K] {R : Type} [CommRing R] [Algebra R K]
    (C : Subalgebra R K) (σ : K ≃ₐ[k] K) (hσ : ∀ f : K, f ∈ C → σ f ∈ C) (b : ↥C) :
    ((restrictSubalg C σ hσ b : ↥C) : K) = σ (b : K) := rfl

theorem exists_invariant_split {k K : Type} [Field k] [Field K] [Algebra k K]
    {R : Type} [CommRing R] [Algebra R K]
    (G : Subgroup (K ≃ₐ[k] K)) (hGfin : Finite ↥G)
    (C : Subalgebra R K) (hCG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ C → σ f ∈ C)
    (W X : ValuationSubring K) (hCW : ∀ b : ↥C, (b : K) ∈ W) (hCX : ∀ b : ↥C, (b : K) ∈ X)
    (y : Ideal ↥C) (hy : y.IsMaximal)
    (hyW : ∀ b : ↥C, b ∈ y ↔ ∃ hb : (b : K) ∈ W, (⟨(b : K), hb⟩ : ↥W) ∈ maximalIdeal ↥W)
    (hXy : ∀ b : ↥C, (∀ hb : (b : K) ∈ X, (⟨(b : K), hb⟩ : ↥X) ∈ maximalIdeal ↥X) → b ∈ y)
    (hXne : ∃ b : ↥C, b ∈ y ∧ ∀ hb : (b : K) ∈ X, (⟨(b : K), hb⟩ : ↥X) ∉ maximalIdeal ↥X) :
    ∃ f : K, f ∈ C ∧ (∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f) ∧
      (∀ hfW : f ∈ W, (⟨f, hfW⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
      (∀ hfX : f ∈ X, (⟨f, hfX⟩ : ↥X) ∉ maximalIdeal ↥X) := by
  classical
  haveI := hGfin
  haveI : Fintype ↥G := Fintype.ofFinite ↥G

  let 𝔮 : Ideal ↥C := (maximalIdeal ↥X).comap (toVal C X hCX)
  have hmem𝔮 : ∀ b : ↥C, b ∈ 𝔮 ↔ (⟨(b : K), hCX b⟩ : ↥X) ∈ maximalIdeal ↥X := fun b => Iff.rfl
  let I : ↥G → Ideal ↥C := fun σ => 𝔮.comap (restrictSubalg C (σ : K ≃ₐ[k] K) (hCG σ σ.2))
  have hIprime : ∀ σ : ↥G, (I σ).IsPrime := by
    intro σ
    haveI : 𝔮.IsPrime := Ideal.comap_isPrime _ _
    exact Ideal.comap_isPrime _ _
  have hmemI : ∀ (σ : ↥G) (b : ↥C), b ∈ I σ ↔
      (⟨(σ : K ≃ₐ[k] K) (b : K), hCX ⟨_, hCG σ σ.2 _ b.2⟩⟩ : ↥X) ∈ maximalIdeal ↥X := fun σ b => Iff.rfl

  have h𝔮y : 𝔮 ≤ y := by
    intro b hb
    apply hXy b
    intro hb'
    exact (hmem𝔮 b).mp hb
  have h𝔮ne : 𝔮 ≠ y := by
    obtain ⟨b, hby, hbX⟩ := hXne
    intro h
    have : b ∈ 𝔮 := h ▸ hby
    exact hbX (hCX b) ((hmem𝔮 b).mp this)

  have hnot : ∀ σ : ↥G, ¬ (y ≤ I σ) := by
    intro σ hle

    have hsurj : Function.Surjective (restrictSubalg C ((σ : K ≃ₐ[k] K)⁻¹) (hCG _ (G.inv_mem σ.2))) := by
      intro c
      refine ⟨⟨(σ : K ≃ₐ[k] K) (c : K), hCG σ σ.2 _ c.2⟩, Subtype.ext ?_⟩
      rw [restrictSubalg_apply_coe]
      change (σ : K ≃ₐ[k] K)⁻¹ ((σ : K ≃ₐ[k] K) (c : K)) = c
      rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    haveI hJmax : (y.comap (restrictSubalg C ((σ : K ≃ₐ[k] K)⁻¹) (hCG _ (G.inv_mem σ.2)))).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ hsurj
    have hJ𝔮 : y.comap (restrictSubalg C ((σ : K ≃ₐ[k] K)⁻¹) (hCG _ (G.inv_mem σ.2))) ≤ 𝔮 := by
      intro c hc
      rw [Ideal.mem_comap] at hc
      have h1 := hle hc
      rw [hmemI] at h1
      rw [hmem𝔮]
      have heq : (σ : K ≃ₐ[k] K) (((restrictSubalg C ((σ : K ≃ₐ[k] K)⁻¹) (hCG _ (G.inv_mem σ.2)) c : ↥C) : K)) = (c : K) := by
        rw [restrictSubalg_apply_coe, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
      have : (⟨(σ : K ≃ₐ[k] K) (((restrictSubalg C ((σ : K ≃ₐ[k] K)⁻¹) (hCG _ (G.inv_mem σ.2)) c : ↥C) : K)), hCX ⟨_, hCG σ σ.2 _ (restrictSubalg C _ _ c).2⟩⟩ : ↥X) = ⟨(c : K), hCX c⟩ :=
        Subtype.ext heq
      rw [this] at h1
      exact h1
    have hJeq : y.comap (restrictSubalg C ((σ : K ≃ₐ[k] K)⁻¹) (hCG _ (G.inv_mem σ.2))) = 𝔮 := by
      haveI : 𝔮.IsPrime := Ideal.comap_isPrime _ _
      exact hJmax.eq_of_le (Ideal.IsPrime.ne_top ‹_›) hJ𝔮
    have h𝔮max : 𝔮.IsMaximal := hJeq ▸ hJmax
    exact h𝔮ne (h𝔮max.eq_of_le hy.ne_top h𝔮y)

  have havoid : ¬ ((y : Set ↥C) ⊆ ⋃ σ ∈ (↑(Finset.univ : Finset ↥G) : Set ↥G), (I σ : Set ↥C)) := by
    rw [Ideal.subset_union_prime (1 : ↥G) (1 : ↥G) (fun σ _ _ _ => hIprime σ)]
    rintro ⟨σ, -, hσ⟩
    exact hnot σ hσ
  rw [Set.not_subset] at havoid
  obtain ⟨b, hby, hbI⟩ := havoid
  have hbI' : ∀ σ : ↥G, (b : ↥C) ∉ I σ := by
    intro σ hσ
    apply hbI
    simp only [Finset.coe_univ, Set.mem_iUnion, Set.mem_univ, exists_true_left]
    exact ⟨σ, hσ⟩

  set b₀ : K := ((b : ↥C) : K) with hb₀
  have hσC : ∀ σ : ↥G, (σ : K ≃ₐ[k] K) b₀ ∈ C := fun σ => hCG σ σ.2 _ b.2
  refine ⟨∏ σ : ↥G, (σ : K ≃ₐ[k] K) b₀, ?_, ?_, ?_, ?_⟩
  · exact prod_mem fun σ _ => hσC σ
  · intro ρ hρ
    rw [map_prod]
    refine Fintype.prod_equiv (Equiv.mulLeft (⟨ρ, hρ⟩ : ↥G)) _ _ ?_
    intro σ
    simp [AlgEquiv.mul_apply]
  · intro hfW
    rw [mem_maximalIdeal_iff_lt, map_prod]

    have hb1 : W.valuation b₀ < 1 := by
      obtain ⟨hbW, hbm⟩ := (hyW b).mp hby
      exact (mem_maximalIdeal_iff_lt W _ hbW).mp hbm
    have hle1 : ∀ σ : ↥G, W.valuation ((σ : K ≃ₐ[k] K) b₀) ≤ 1 :=
      fun σ => (W.valuation_le_one_iff _).mpr (hCW ⟨_, hσC σ⟩)
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (1 : ↥G))]
    have hrest : ∏ σ ∈ Finset.univ.erase (1 : ↥G), W.valuation ((σ : K ≃ₐ[k] K) b₀) ≤ 1 :=
      Finset.prod_le_one' fun σ _ => hle1 σ
    have h1 : W.valuation (((1 : ↥G) : K ≃ₐ[k] K) b₀) < 1 := by simpa using hb1
    rw [mul_comm]
    exact mul_lt_one_of_lt_of_le h1 hrest
  · intro hfX hm
    rw [mem_maximalIdeal_iff_lt, map_prod] at hm
    have hall : ∀ σ : ↥G, X.valuation ((σ : K ≃ₐ[k] K) b₀) = 1 := by
      intro σ
      have hnot' := hbI' σ
      rw [hmemI] at hnot'
      have hX := hCX ⟨_, hσC σ⟩
      rcases X.valuation_lt_one_or_eq_one ⟨_, hX⟩ with h | h
      · exact (hnot' ((mem_maximalIdeal_iff_lt X _ hX).mpr h)).elim
      · exact h
    rw [Finset.prod_congr rfl (fun σ _ => hall σ), Finset.prod_const_one] at hm
    exact lt_irrefl _ hm

open IsLocalRing

theorem valuation_eq_one_of_inv_mem {K : Type} [Field K] (W : ValuationSubring K) (O : Subring K)
    (hOW : ∀ f : K, f ∈ O → f ∈ W) (x : K) (hx : x ∈ O) (hu : IsUnit (⟨x, hx⟩ : ↥O)) : W.valuation x = 1 := by
  obtain ⟨y, hy, hxy⟩ := (isUnit_mk_iff O x hx).mp hu
  have h1 : W.valuation x ≤ 1 := (W.valuation_le_one_iff _).mpr (hOW _ hx)
  have h2 : W.valuation y ≤ 1 := (W.valuation_le_one_iff _).mpr (hOW _ hy)
  have h3 : W.valuation x * W.valuation y = 1 := by rw [← map_mul, hxy, map_one]
  exact le_antisymm h1 (by
    by_contra h
    rw [not_le] at h
    have := mul_lt_one_of_lt_of_le h h2
    rw [h3] at this
    exact lt_irrefl _ this)

noncomputable def twistToVal {k K : Type} [Field k] [Field K] [Algebra k K] {R : Type} [CommRing R] [Algebra R K]
    (Bc : Subalgebra R K) (W : ValuationSubring K) (hBW : ∀ f : K, f ∈ Bc → f ∈ W)
    (σ : K ≃ₐ[k] K) (hσ : ∀ f : K, f ∈ Bc → σ f ∈ Bc) : ↥Bc →+* ↥W where
  toFun b := ⟨σ (b : K), hBW _ (hσ _ b.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

noncomputable def toSubring' {K : Type} [Field K] {R : Type} [CommRing R] [Algebra R K]
    (Bc : Subalgebra R K) (O : Subring K) (hBO : ∀ f : K, f ∈ Bc → f ∈ O) : ↥Bc →+* ↥O where
  toFun b := ⟨(b : K), hBO _ b.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

theorem exists_invariant_cosplit {k K : Type} [Field k] [Field K] [Algebra k K]
    {R : Type} [CommRing R] [Algebra R K]
    (G : Subgroup (K ≃ₐ[k] K)) (hGfin : Finite ↥G)
    (Bc : Subalgebra R K) (hBcG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ Bc → σ f ∈ Bc)
    (O : Subring K) [IsLocalRing ↥O] (hBO : ∀ f : K, f ∈ Bc → f ∈ O)
    (hloc : ∀ f : K, f ∈ O ↔ ∃ g h : K, g ∈ Bc ∧ h ∈ Bc ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g)
    (hres : ∀ (f : K) (hf : f ∈ O), ∃ (a : R) (ha : algebraMap R K a ∈ O), ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, ha⟩))
    (W : ValuationSubring K) (hOW : ∀ f : K, f ∈ O → f ∈ W)
    (hstabW : ∀ σ : K ≃ₐ[k] K, σ ∈ G → (∀ f : K, f ∈ O → σ f ∈ W) → ∀ f : K, f ∈ W ↔ σ f ∈ W)
    (c : K) (hcO : c ∈ O) (hcu : ¬ IsUnit (⟨c, hcO⟩ : ↥O))
    (hcW : ∀ hc : c ∈ W, (⟨c, hc⟩ : ↥W) ∉ maximalIdeal ↥W) :
    ∃ (f : K) (hfO : f ∈ O), (∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f) ∧ ¬ IsUnit (⟨f, hfO⟩ : ↥O) ∧
      (∀ hfW : f ∈ W, (⟨f, hfW⟩ : ↥W) ∉ maximalIdeal ↥W) := by
  classical
  haveI := hGfin
  haveI : Fintype ↥G := Fintype.ofFinite ↥G
  have hBW : ∀ f : K, f ∈ Bc → f ∈ W := fun f hf => hOW _ (hBO _ hf)

  let 𝔮 : Ideal ↥Bc := (maximalIdeal ↥O).comap (toSubring' Bc O hBO)
  have hmem𝔮 : ∀ b : ↥Bc, b ∈ 𝔮 ↔ ¬ IsUnit (⟨(b : K), hBO _ b.2⟩ : ↥O) := by
    intro b
    show (toSubring' Bc O hBO b) ∈ maximalIdeal ↥O ↔ _
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact Iff.rfl
  let I : ↥G → Ideal ↥Bc := fun σ => (maximalIdeal ↥W).comap (twistToVal Bc W hBW (σ : K ≃ₐ[k] K) (hBcG σ σ.2))
  have hIprime : ∀ σ : ↥G, (I σ).IsPrime := fun σ => Ideal.comap_isPrime _ _
  have hmemI : ∀ (σ : ↥G) (b : ↥Bc), b ∈ I σ ↔
      (⟨(σ : K ≃ₐ[k] K) (b : K), hBW _ (hBcG σ σ.2 _ b.2)⟩ : ↥W) ∈ maximalIdeal ↥W := fun σ b => Iff.rfl

  have h𝔮max : 𝔮.IsMaximal := by
    haveI : 𝔮.IsPrime := Ideal.comap_isPrime _ _
    rw [Ideal.isMaximal_iff]
    refine ⟨fun h1 => Ideal.IsPrime.ne_top' (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one), ?_⟩
    intro J x hJ hx hxJ
    rw [hmem𝔮, not_not] at hx
    obtain ⟨y, hy, hxy⟩ := (isUnit_mk_iff O _ (hBO _ x.2)).mp hx
    obtain ⟨a, ha, hna⟩ := hres y hy

    have hxa : (1 : ↥Bc) - x * algebraMap R ↥Bc a ∈ 𝔮 := by
      rw [hmem𝔮]
      intro hu
      apply hna
      have heq : ((⟨y, hy⟩ : ↥O) - ⟨_, ha⟩) * ⟨(x : K), hBO _ x.2⟩ = ⟨(((1 : ↥Bc) - x * algebraMap R ↥Bc a : ↥Bc) : K), hBO _ ((1 : ↥Bc) - x * algebraMap R ↥Bc a).2⟩ := by
        apply Subtype.ext
        show (y - algebraMap R K a) * (x : K) = (((1 : ↥Bc) - x * algebraMap R ↥Bc a : ↥Bc) : K)
        rw [Subalgebra.coe_sub, Subalgebra.coe_one, Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
        have : (x : K) * y = 1 := hxy
        linear_combination this
      have h2 : IsUnit (((⟨y, hy⟩ : ↥O) - ⟨_, ha⟩) * ⟨(x : K), hBO _ x.2⟩) := by rw [heq]; exact hu
      exact isUnit_of_mul_isUnit_left h2
    have h3 : x * algebraMap R ↥Bc a ∈ J := J.mul_mem_right _ hxJ
    have h4 : (1 : ↥Bc) - x * algebraMap R ↥Bc a ∈ J := hJ hxa
    have : (1 : ↥Bc) = ((1 : ↥Bc) - x * algebraMap R ↥Bc a) + x * algebraMap R ↥Bc a := by ring
    rw [this]
    exact J.add_mem h4 h3

  obtain ⟨g₀, h₀, hg₀, hh₀, hh₀u, hch⟩ := (hloc c).mp hcO
  have hvh₀ : W.valuation h₀ = 1 := valuation_eq_one_of_inv_mem W O hOW h₀ (hBO _ hh₀) (hh₀u _)
  have hvc : W.valuation c = 1 := by
    have h1 : W.valuation c ≤ 1 := (W.valuation_le_one_iff _).mpr (hOW _ hcO)
    rcases W.valuation_lt_one_or_eq_one ⟨c, hOW _ hcO⟩ with h | h
    · exact (hcW (hOW _ hcO) ((mem_maximalIdeal_iff_lt W c _).mpr h)).elim
    · exact h
  have hvg₀ : W.valuation g₀ = 1 := by rw [← hch, map_mul, hvc, hvh₀, one_mul]
  have hg₀𝔮 : (⟨g₀, hg₀⟩ : ↥Bc) ∈ 𝔮 := by
    rw [hmem𝔮]
    intro hu
    apply hcu
    have heq : (⟨g₀, hBO _ hg₀⟩ : ↥O) = ⟨c, hcO⟩ * ⟨h₀, hBO _ hh₀⟩ := Subtype.ext hch.symm
    rw [heq] at hu
    exact isUnit_of_mul_isUnit_left hu

  have hnot : ∀ σ : ↥G, ¬ (𝔮 ≤ I σ) := by
    intro σ hle
    have heq : 𝔮 = I σ := h𝔮max.eq_of_le (Ideal.IsPrime.ne_top (hIprime σ)) hle

    have hinto : ∀ f : K, f ∈ O → (σ : K ≃ₐ[k] K) f ∈ W := by
      intro f hf
      obtain ⟨g, h, hg, hh, hhu, hfh⟩ := (hloc f).mp hf
      have hhI : (⟨h, hh⟩ : ↥Bc) ∉ I σ := by
        rw [← heq, hmem𝔮, not_not]; exact hhu _
      rw [hmemI] at hhI

      have hσhW : (σ : K ≃ₐ[k] K) h ∈ W := hBW _ (hBcG σ σ.2 _ hh)
      have hσhu : IsUnit (⟨(σ : K ≃ₐ[k] K) h, hσhW⟩ : ↥W) := by
        rcases W.valuation_lt_one_or_eq_one ⟨_, hσhW⟩ with h1 | h1
        · exact (hhI ((mem_maximalIdeal_iff_lt W _ _).mpr h1)).elim
        · exact (W.valuation_eq_one_iff _).mpr h1
      obtain ⟨u, hu⟩ := hσhu
      have hyy : ((((u⁻¹ : (↥W)ˣ) : ↥W)) : K) ∈ W := ((u⁻¹ : (↥W)ˣ) : ↥W).2
      have hyy1 : (σ : K ≃ₐ[k] K) h * ((((u⁻¹ : (↥W)ˣ) : ↥W)) : K) = 1 := by
        have e := congrArg (fun z : ↥W => (z : K)) u.mul_inv
        rw [hu] at e
        simpa using e
      set yy : K := ((((u⁻¹ : (↥W)ˣ) : ↥W)) : K) with hyydef
      have : (σ : K ≃ₐ[k] K) f = (σ : K ≃ₐ[k] K) g * yy := by
        have e : (σ : K ≃ₐ[k] K) f * (σ : K ≃ₐ[k] K) h = (σ : K ≃ₐ[k] K) g := by rw [← map_mul, hfh]
        calc (σ : K ≃ₐ[k] K) f = (σ : K ≃ₐ[k] K) f * ((σ : K ≃ₐ[k] K) h * yy) := by rw [hyy1, mul_one]
          _ = (σ : K ≃ₐ[k] K) g * yy := by rw [← mul_assoc, e]
      rw [this]
      exact W.mul_mem _ _ (hBW _ (hBcG σ σ.2 _ hg)) hyy
    have hW := hstabW σ σ.2 hinto

    have h1 : (⟨g₀, hg₀⟩ : ↥Bc) ∈ I σ := heq ▸ hg₀𝔮
    rw [hmemI] at h1
    have h2 := (mem_maximalIdeal_iff_lt W _ _).mp h1

    have hg₀W : g₀ ∈ W := hBW _ hg₀
    have hg₀ne : g₀ ≠ 0 := by
      intro h0; rw [h0, map_zero] at hvg₀; exact zero_ne_one hvg₀
    have hinvW : g₀⁻¹ ∈ W := by
      rw [← W.valuation_le_one_iff, map_inv₀, hvg₀, inv_one]
    have hσinv : (σ : K ≃ₐ[k] K) g₀⁻¹ ∈ W := (hW _).mp hinvW
    have h3 : W.valuation ((σ : K ≃ₐ[k] K) g₀) * W.valuation ((σ : K ≃ₐ[k] K) g₀⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel₀ hg₀ne, map_one, map_one]
    have h4 : W.valuation ((σ : K ≃ₐ[k] K) g₀⁻¹) ≤ 1 := (W.valuation_le_one_iff _).mpr hσinv
    have := mul_lt_one_of_lt_of_le h2 h4
    rw [h3] at this
    exact lt_irrefl _ this

  have havoid : ¬ ((𝔮 : Set ↥Bc) ⊆ ⋃ σ ∈ (↑(Finset.univ : Finset ↥G) : Set ↥G), (I σ : Set ↥Bc)) := by
    rw [Ideal.subset_union_prime (1 : ↥G) (1 : ↥G) (fun σ _ _ _ => hIprime σ)]
    rintro ⟨σ, -, hσ⟩
    exact hnot σ hσ
  rw [Set.not_subset] at havoid
  obtain ⟨b, hb𝔮, hbI⟩ := havoid
  have hbI' : ∀ σ : ↥G, (b : ↥Bc) ∉ I σ := by
    intro σ hσ
    apply hbI
    simp only [Finset.coe_univ, Set.mem_iUnion, Set.mem_univ, exists_true_left]
    exact ⟨σ, hσ⟩
  set b₀ : K := ((b : ↥Bc) : K) with hb₀
  have hσBc : ∀ σ : ↥G, (σ : K ≃ₐ[k] K) b₀ ∈ Bc := fun σ => hBcG σ σ.2 _ b.2
  have hprodO : (∏ σ : ↥G, (σ : K ≃ₐ[k] K) b₀) ∈ O := prod_mem fun σ _ => hBO _ (hσBc σ)
  refine ⟨∏ σ : ↥G, (σ : K ≃ₐ[k] K) b₀, hprodO, ?_, ?_, ?_⟩
  · intro ρ hρ
    rw [map_prod]
    refine Fintype.prod_equiv (Equiv.mulLeft (⟨ρ, hρ⟩ : ↥G)) _ _ ?_
    intro σ
    simp [AlgEquiv.mul_apply]
  · intro hu
    have hbu : ¬ IsUnit (⟨b₀, hBO _ b.2⟩ : ↥O) := (hmem𝔮 b).mp hb𝔮
    apply hbu
    have hsplit : (⟨∏ σ : ↥G, (σ : K ≃ₐ[k] K) b₀, hprodO⟩ : ↥O) =
        ⟨b₀, hBO _ b.2⟩ * ⟨∏ σ ∈ Finset.univ.erase (1 : ↥G), (σ : K ≃ₐ[k] K) b₀,
          prod_mem fun σ _ => hBO _ (hσBc σ)⟩ := by
      apply Subtype.ext
      show (∏ σ : ↥G, (σ : K ≃ₐ[k] K) b₀) = b₀ * ∏ σ ∈ Finset.univ.erase (1 : ↥G), (σ : K ≃ₐ[k] K) b₀
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (1 : ↥G)), mul_comm]
      simp
    rw [hsplit] at hu
    exact isUnit_of_mul_isUnit_left hu
  · intro hfW hm
    rw [mem_maximalIdeal_iff_lt, map_prod] at hm
    have hall : ∀ σ : ↥G, W.valuation ((σ : K ≃ₐ[k] K) b₀) = 1 := by
      intro σ
      have hnot' := hbI' σ
      rw [hmemI] at hnot'
      have hX := hBW _ (hσBc σ)
      rcases W.valuation_lt_one_or_eq_one ⟨_, hX⟩ with h | h
      · exact (hnot' ((mem_maximalIdeal_iff_lt W _ hX).mpr h)).elim
      · exact h
    rw [Finset.prod_congr rfl (fun σ _ => hall σ), Finset.prod_const_one] at hm
    exact lt_irrefl _ hm

@[reducible] noncomputable def subalgAction' {k K : Type} [Field k] [Field K] [Algebra k K] {R : Type} [CommRing R] [Algebra R K]
    (G : Subgroup (K ≃ₐ[k] K)) (B : Subalgebra R K)
    (hBG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ B → σ f ∈ B) : MulSemiringAction ↥G ↥B where
  smul σ b := ⟨(σ : K ≃ₐ[k] K) (b : K), hBG σ σ.2 _ b.2⟩
  one_smul b := Subtype.ext (by change ((1 : ↥G) : K ≃ₐ[k] K) (b : K) = b; rw [OneMemClass.coe_one, AlgEquiv.one_apply])
  mul_smul σ τ b := Subtype.ext (by
    change ((σ * τ : ↥G) : K ≃ₐ[k] K) (b : K) = (σ : K ≃ₐ[k] K) ((τ : K ≃ₐ[k] K) (b : K))
    rw [Subgroup.coe_mul, AlgEquiv.mul_apply])
  smul_zero σ := Subtype.ext (by change (σ : K ≃ₐ[k] K) ((0 : ↥B) : K) = 0; simp)
  smul_add σ a b := Subtype.ext (by change (σ : K ≃ₐ[k] K) ((a + b : ↥B) : K) = _; simp; rfl)
  smul_one σ := Subtype.ext (by change (σ : K ≃ₐ[k] K) ((1 : ↥B) : K) = 1; simp)
  smul_mul σ a b := Subtype.ext (by change (σ : K ≃ₐ[k] K) ((a * b : ↥B) : K) = _; simp; rfl)

def fixedSubalg {k K : Type} [Field k] [Field K] [Algebra k K] {R : Type} [CommRing R] [Algebra R K]
    (G : Subgroup (K ≃ₐ[k] K)) (hRfix : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ r : R, σ (algebraMap R K r) = algebraMap R K r)
    (B : Subalgebra R K) : Subalgebra R K where
  carrier := {f | f ∈ B ∧ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f}
  mul_mem' := fun {a b} ha hb => ⟨B.mul_mem ha.1 hb.1, fun σ hσ => by rw [map_mul, ha.2 σ hσ, hb.2 σ hσ]⟩
  one_mem' := ⟨B.one_mem, fun σ _ => map_one σ⟩
  add_mem' := fun {a b} ha hb => ⟨B.add_mem ha.1 hb.1, fun σ hσ => by rw [map_add, ha.2 σ hσ, hb.2 σ hσ]⟩
  zero_mem' := ⟨B.zero_mem, fun σ _ => map_zero σ⟩
  algebraMap_mem' := fun r => ⟨B.algebraMap_mem r, fun σ hσ => hRfix σ hσ r⟩

theorem finiteType_fixedSubalg {k K : Type} [Field k] [Field K] [Algebra k K]
    {R : Type} [CommRing R] [IsNoetherianRing R] [Algebra R K]
    (G : Subgroup (K ≃ₐ[k] K)) (hGfin : Finite ↥G)
    (hRfix : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ r : R, σ (algebraMap R K r) = algebraMap R K r)
    (B : Subalgebra R K) (hBG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ B → σ f ∈ B)
    (hft : Algebra.FiniteType R ↥B) :
    Algebra.FiniteType R ↥(fixedSubalg G hRfix B) := by
  classical
  haveI := hGfin
  set A : Subalgebra R K := fixedSubalg G hRfix B with hA
  have hle : A ≤ B := fun _ hf => hf.1
  letI algAB : Algebra ↥A ↥B := (Subalgebra.inclusion hle).toAlgebra
  haveI : IsScalarTower R ↥A ↥B := IsScalarTower.of_algebraMap_eq (fun r => Subtype.ext rfl)
  haveI : FaithfulSMul ↥A ↥B := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    exact Subtype.ext (congrArg (fun z : ↥B => (z : K)) hab)
  letI act : MulSemiringAction ↥G ↥B := subalgAction' G B hBG
  haveI : Algebra.IsInvariant ↥A ↥B ↥G := by
    refine ⟨fun b hb => ?_⟩
    refine ⟨⟨(b : K), ⟨b.2, fun σ hσ => ?_⟩⟩, Subtype.ext rfl⟩
    exact congrArg (fun z : ↥B => (z : K)) (hb ⟨σ, hσ⟩)
  haveI := hft
  exact (Algebra.IsInvariant.moduleFinite_and_finiteType_of_finiteType R ↥A ↥B ↥G).2

theorem exists_finset_trace_eq_closure {k K : Type} [Field k] [Field K] [Algebra k K]
    {R : Type} [CommRing R] [IsNoetherianRing R] [Algebra R K]
    (G : Subgroup (K ≃ₐ[k] K)) (hGfin : Finite ↥G)
    (K₀ : IntermediateField k K) (hK₀ : K₀ = IntermediateField.fixedField G)
    (hRfix : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ r : R, σ (algebraMap R K r) = algebraMap R K r)
    (B : Subalgebra R K) (hBG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ B → σ f ∈ B)
    (hft : Algebra.FiniteType R ↥B) :
    ∃ T : Finset ↥K₀, B.toSubring.comap (algebraMap ↥K₀ K) =
      Subring.closure ({f : ↥K₀ | ∃ r : R, (f : K) = algebraMap R K r} ∪ ↑T) := by
  classical
  haveI := hGfin
  have hfix : ∀ f : K, f ∈ K₀ ↔ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f := by
    intro f; rw [hK₀, IntermediateField.mem_fixedField_iff]
  obtain ⟨s, hs⟩ := (finiteType_fixedSubalg G hGfin hRfix B hBG hft).out

  have hsK₀ : ∀ b : ↥(fixedSubalg G hRfix B), ((b : K)) ∈ K₀ := fun b => (hfix _).mpr b.2.2
  let emb : ↥(fixedSubalg G hRfix B) → ↥K₀ := fun b => ⟨(b : K), hsK₀ b⟩
  refine ⟨s.image emb, ?_⟩
  apply le_antisymm
  ·
    intro f hf
    rw [Subring.mem_comap] at hf
    have hfA : (f : K) ∈ fixedSubalg G hRfix B := ⟨hf, (hfix _).mp f.2⟩
    have htop : (⟨(f : K), hfA⟩ : ↥(fixedSubalg G hRfix B)) ∈ Algebra.adjoin R (s : Set ↥(fixedSubalg G hRfix B)) := by
      rw [hs]; trivial

    let φ : ↥(fixedSubalg G hRfix B) →+* ↥K₀ :=
      { toFun := emb
        map_one' := Subtype.ext (by simp [emb])
        map_mul' := fun a b => Subtype.ext (by simp [emb])
        map_zero' := Subtype.ext (by simp [emb])
        map_add' := fun a b => Subtype.ext (by simp [emb]) }
    have hφ : ∀ b, φ b = emb b := fun _ => rfl
    have hmem : φ ⟨(f : K), hfA⟩ ∈ (Algebra.adjoin R (s : Set ↥(fixedSubalg G hRfix B))).toSubring.map φ :=
      Subring.mem_map.mpr ⟨_, htop, rfl⟩
    have heq : φ ⟨(f : K), hfA⟩ = f := Subtype.ext rfl
    rw [heq, Algebra.adjoin_eq_ring_closure, RingHom.map_closure] at hmem
    refine Subring.closure_mono ?_ hmem
    rintro x ⟨y, hy, rfl⟩
    rcases hy with ⟨r, rfl⟩ | hy
    · left; exact ⟨r, rfl⟩
    · right
      rw [Finset.coe_image]
      exact ⟨y, hy, rfl⟩
  · rw [Subring.closure_le]
    rintro f (⟨r, hr⟩ | hf)
    · show f ∈ B.toSubring.comap (algebraMap ↥K₀ K)
      rw [Subring.mem_comap, Subalgebra.mem_toSubring]
      change (f : K) ∈ B
      rw [hr]; exact B.algebraMap_mem r
    · rw [Finset.mem_coe, Finset.mem_image] at hf
      obtain ⟨b, -, rfl⟩ := hf
      show emb b ∈ B.toSubring.comap (algebraMap ↥K₀ K)
      rw [Subring.mem_comap, Subalgebra.mem_toSubring]
      exact b.2.1

theorem completion_pack
    (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) = Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (n : ℕ) (hnq : n ∣ q + 1) :
    ∃ (_ : IsDomain (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
      (_ : IsDiscreteValuationRing (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
      (_ : IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))),
      maximalIdeal (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) =
        Ideal.span {algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩} ∧
      IsUnit ((n : ℕ) : AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := by
  haveI := hdvr
  have hirr : Irreducible (⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hunif
  obtain ⟨i1, i2, i3, hirr', -, -⟩ :=
    IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⟨π₀, hπ⟩ hirr
  haveI := i1; haveI := i2; haveI := i3
  refine ⟨i1, i2, i3, hirr'.maximalIdeal_eq, ?_⟩

  have hqnu : ¬ IsUnit ((q : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := by
    intro hu
    obtain ⟨u, hu⟩ := hu
    have hq1 : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1 := (A.mem_nonunits_iff).mp hA

    have hinvA : ((((u⁻¹ : (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))ˣ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : ↥k₀) : AlgebraicClosure ℚ) ∈ A := ((u⁻¹ : (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))ˣ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))).2
    have hprod : ((q : ℕ) : AlgebraicClosure ℚ) * ((((u⁻¹ : (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))ˣ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : ↥k₀) : AlgebraicClosure ℚ) = 1 := by
      have e := congrArg (fun z : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) => ((z : ↥k₀) : AlgebraicClosure ℚ)) u.mul_inv
      rw [hu] at e
      simpa using e
    have h2 : A.valuation ((((u⁻¹ : (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))ˣ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : ↥k₀) : AlgebraicClosure ℚ) ≤ 1 := (A.valuation_le_one_iff _).mpr hinvA
    have := mul_lt_one_of_lt_of_le hq1 h2
    rw [← map_mul, hprod, map_one] at this
    exact lt_irrefl _ this
  have hq1u : IsUnit ((q + 1 : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := by
    by_contra hnu
    have h1 : ((q + 1 : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h2 : ((q : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := (IsLocalRing.mem_maximalIdeal _).mpr hqnu
    have h3 : (1 : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := by
      have : (1 : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) = ((q + 1 : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) - ((q : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := by push_cast; ring
      rw [this]
      exact (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))).sub_mem h1 h2
    exact (maximalIdeal.isMaximal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))).ne_top ((Ideal.eq_top_iff_one _).mpr h3)
  have hnu : IsUnit ((n : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hnq) hq1u
  have := hnu.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
  rwa [map_natCast] at this

end S3C4Glue

namespace S3C4Glue

open IsLocalRing

theorem ne_zero_of_isUnit_mk {K : Type} [Field K] (O : Subring K) (h : K) (hh : h ∈ O) (hu : IsUnit (⟨h, hh⟩ : ↥O)) : h ≠ 0 := by
  intro h0
  obtain ⟨u, hu⟩ := hu
  have e := congrArg (fun z : ↥O => (z : K)) u.mul_inv
  rw [hu] at e
  simp [h0] at e

theorem exists_frac_invariants {k K : Type} [Field k] [Field K] [Algebra k K]
    (G : Subgroup (K ≃ₐ[k] K)) (hGfin : Finite ↥G)
    (K₀ : IntermediateField k K) (hK₀ : K₀ = IntermediateField.fixedField G)
    (Bx : Subring K) (hBxG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ Bx → σ f ∈ Bx)
    (Õ : Subring K) (hBxO : Bx ≤ Õ)
    (hloc : ∀ f : K, f ∈ Õ ↔ ∃ g h : K, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ Õ, IsUnit (⟨h, hh⟩ : ↥Õ)) ∧ f * h = g)
    (hfracO : ∀ f : K, ∃ a b : K, a ∈ Õ ∧ b ∈ Õ ∧ b ≠ 0 ∧ f * b = a) :
    ∀ f : ↥K₀, ∃ g h : ↥K₀, (g : K) ∈ Bx ∧ (h : K) ∈ Bx ∧ h ≠ 0 ∧ f * h = g := by
  classical
  haveI := hGfin
  haveI : Fintype ↥G := Fintype.ofFinite ↥G
  have hfix : ∀ x : K, x ∈ K₀ ↔ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ x = x := by
    intro x; rw [hK₀, IntermediateField.mem_fixedField_iff]

  have hfracB : ∀ f : K, ∃ g h : K, g ∈ Bx ∧ h ∈ Bx ∧ h ≠ 0 ∧ f * h = g := by
    intro f
    obtain ⟨a, b, ha, hb, hb0, hfb⟩ := hfracO f
    obtain ⟨g₁, h₁, hg₁, hh₁, hu₁, e₁⟩ := (hloc a).mp ha
    obtain ⟨g₂, h₂, hg₂, hh₂, hu₂, e₂⟩ := (hloc b).mp hb
    have hh₁0 : h₁ ≠ 0 := ne_zero_of_isUnit_mk Õ h₁ (hBxO hh₁) (hu₁ (hBxO hh₁))
    have hh₂0 : h₂ ≠ 0 := ne_zero_of_isUnit_mk Õ h₂ (hBxO hh₂) (hu₂ (hBxO hh₂))
    have hg₂0 : g₂ ≠ 0 := by rw [← e₂]; exact mul_ne_zero hb0 hh₂0
    refine ⟨g₁ * h₂, h₁ * g₂, Bx.mul_mem hg₁ hh₂, Bx.mul_mem hh₁ hg₂, mul_ne_zero hh₁0 hg₂0, ?_⟩

    calc f * (h₁ * g₂) = (f * b) * h₁ * h₂ := by rw [← e₂]; ring
      _ = g₁ * h₂ := by rw [hfb, ← e₁]

  intro f
  obtain ⟨g, h, hg, hh, hh0, e⟩ := hfracB (f : K)

  set D : K := ∏ σ : ↥G, (σ : K ≃ₐ[k] K) h with hD
  have hDB : D ∈ Bx := Subring.prod_mem _ (fun σ _ => hBxG σ σ.2 h hh)
  have hD0 : D ≠ 0 := by
    rw [hD, Finset.prod_ne_zero_iff]
    intro σ _
    exact (map_ne_zero_iff (σ : K ≃ₐ[k] K).toRingHom (σ : K ≃ₐ[k] K).injective).mpr hh0
  have hDfix : ∀ ρ : K ≃ₐ[k] K, ρ ∈ G → ρ D = D := by
    intro ρ hρ
    rw [hD, map_prod]
    exact Fintype.prod_equiv (Equiv.mulLeft (⟨ρ, hρ⟩ : ↥G)) _ _ (fun σ => by simp [AlgEquiv.mul_apply])

  have hsplit : D = h * ∏ σ ∈ (Finset.univ.erase (1 : ↥G)), (σ : K ≃ₐ[k] K) h := by
    rw [hD, ← Finset.mul_prod_erase Finset.univ (fun σ : ↥G => (σ : K ≃ₐ[k] K) h) (Finset.mem_univ (1 : ↥G))]
    rfl
  have hND : (f : K) * D ∈ Bx := by
    rw [hsplit, ← mul_assoc, e]
    exact Bx.mul_mem hg (Subring.prod_mem _ (fun σ _ => hBxG σ σ.2 h hh))
  have hNfix : ∀ ρ : K ≃ₐ[k] K, ρ ∈ G → ρ ((f : K) * D) = (f : K) * D := by
    intro ρ hρ; rw [map_mul, hDfix ρ hρ, (hfix _).mp f.2 ρ hρ]
  refine ⟨⟨(f : K) * D, (hfix _).mpr hNfix⟩, ⟨D, (hfix _).mpr hDfix⟩, hND, hDB, ?_, Subtype.ext rfl⟩
  exact fun h0 => hD0 (congrArg (fun z : ↥K₀ => (z : K)) h0)

end S3C4Glue

open S3C4Glue in

theorem jOf_fixed_harness
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ q)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hKℓ : Kℓ = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (hjK : ModularCurve.jqNModC ↥k₀ q ∈ Kℓ)
    (γ : SL(2, ℤ)) (hγq : γ ∈ CongruenceSubgroup.Gamma q) (hγ0 : γ ∈ CongruenceSubgroup.Gamma0 M')
    (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ) :
    τ ⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ = ⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨ι, hι'⟩ := S3C4Glue.C3aux_exists_emb k₀ q ξ hξ
  have hι : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / q) := ⟨ι, hι'⟩

  have hx0 : coeffEmb ↥k₀ jq ∈ ModularCurve.laurentBaseChange ↥k₀ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) := by
    rw [ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]
    exact coeffEmb_mem_laurentBaseChange ↥k₀ (modularFunctionField_le_full M' (jq_mem M'))
  have hjq : coeffEmb ↥k₀ jq = ModularCurve.jqModC ↥k₀ := ModularCurve.map_jqModC (algebraMap ℚ ↥k₀)
  have heq : ((⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) : LaurentSeries ↥k₀) = ModularCurve.qExpand ↥k₀ q (coeffEmb ↥k₀ jq) := by
    rw [hjq]; rfl
  exact ((ModularCurve.FullLevel.Diamond.qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker q M' hqM'
    ℓg hℓg hℓg12 hℓgM' ↥k₀ ξ hξ hι H₁ hH₁ Kℓ hKℓ) _ hx0).2 ⟨_, hjK⟩ heq γ hγ0 τ hτ

set_option autoImplicit false
set_option maxHeartbeats 0

open IsLocalRing

namespace S3C4Pernode

theorem mem_map_algEquiv_iff {k K : Type} [Field k] [Field K] [Algebra k K] (σ : K ≃ₐ[k] K) (O : Subring K) (x : K) :
    x ∈ O.map (σ : K →+* K) ↔ σ.symm x ∈ O := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    change σ.symm (σ y) ∈ O
    rw [AlgEquiv.symm_apply_apply]; exact hy
  · intro h
    exact ⟨σ.symm x, h, by change σ (σ.symm x) = x; rw [AlgEquiv.apply_symm_apply]⟩

theorem hIGSEP_discharge {k K : Type} [Field k] [Field K] [Algebra k K]
    {Γ : Type} [Group Γ] (S₀ S₁ : Subgroup Γ) (Att : Γ → (K ≃ₐ[k] K) → Prop)
    (G : Subgroup (K ≃ₐ[k] K)) (hGfin : Finite ↥G)
    (hGatt : ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∃ γ : Γ, γ ∈ S₁ ∧ γ ∈ S₀ ∧ Att γ⁻¹ τ)
    (K₀ : IntermediateField k K) (hK₀ : K₀ = IntermediateField.fixedField G)
    {R : Type} [CommRing R] [Algebra R K] (Bc : Subalgebra R K)
    (hBcG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ Bc → σ f ∈ Bc)
    (ends : Finset (Subring K)) (hOlocal : ∀ O ∈ ends, IsLocalRing ↥O)
    (hBcO : ∀ O ∈ ends, (∀ f : K, f ∈ Bc → f ∈ O) ∧
      (∀ f : K, f ∈ O ↔ ∃ g h : K, g ∈ Bc ∧ h ∈ Bc ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g))
    (Õ : Subring K) (hÕ : Õ ∈ ends)
    (nodes : Finset (Subring ↥K₀)) (hnodes : ∀ O' ∈ nodes, ∃ Õ' ∈ ends, ∀ f : ↥K₀, f ∈ O' ↔ ((f : K)) ∈ Õ')
    (O : Subring ↥K₀) (hO : ∀ f : ↥K₀, f ∈ O ↔ ((f : K)) ∈ Õ)
    (Wx : ValuationSubring K) (hÕWx : ∀ f : K, f ∈ Õ → f ∈ Wx)
    (hsepP : ∀ O' ∈ ends, ∀ γ : Γ, γ ∈ S₁ → γ ∈ S₀ → ∀ τ : K ≃ₐ[k] K, Att γ⁻¹ τ →
      (∀ f : K, f ∈ O' → τ f ∈ Wx) → O' = Õ) :
    ∀ O' ∈ nodes, O' ≠ O → ∃ f : ↥K₀, f ∈ O' ∧ f ∉ Wx.comap (algebraMap ↥K₀ K) := by
  classical
  haveI := hGfin
  haveI : Fintype ↥G := Fintype.ofFinite ↥G
  intro O' hO' hne
  obtain ⟨Õ', hÕ', hO'Õ'⟩ := hnodes O' hO'
  have hne' : Õ' ≠ Õ := by
    intro h; apply hne; ext f; rw [hO'Õ', hO, h]

  have hsep0 : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∃ f : K, f ∈ Õ' ∧ σ f ∉ Wx := by
    intro σ hσ
    by_contra hall
    push_neg at hall
    obtain ⟨γ, h1, h0, hatt⟩ := hGatt σ hσ
    exact hne' (hsepP Õ' hÕ' γ h1 h0 σ hatt hall)

  let E : Finset (Subring K) := Finset.univ.image (fun σ : ↥G => Õ'.map ((σ : K ≃ₐ[k] K) : K →+* K))
  have hEmem : ∀ O₁ ∈ E, ∃ σ : ↥G, O₁ = Õ'.map ((σ : K ≃ₐ[k] K) : K →+* K) := by
    intro O₁ h; obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp h; exact ⟨σ, rfl⟩
  have hÕ'E : Õ' ∈ E := by
    refine Finset.mem_image.mpr ⟨1, Finset.mem_univ _, ?_⟩
    ext x; rw [mem_map_algEquiv_iff]; rfl
  obtain ⟨hBcÕ', hlocÕ'⟩ := hBcO Õ' hÕ'
  haveI hÕ'loc : IsLocalRing ↥Õ' := hOlocal Õ' hÕ'

  have hBV : ∀ f : K, f ∈ Bc.toSubring → f ∈ Wx := fun f hf => hÕWx f ((hBcO Õ hÕ).1 f hf)
  have hEloc : ∀ O₁ ∈ E, IsLocalRing ↥O₁ := by
    intro O₁ h
    obtain ⟨σ, rfl⟩ := hEmem O₁ h
    exact IsLocalRing.of_surjective' (Õ'.equivMapOfInjective ((σ : K ≃ₐ[k] K) : K →+* K) (σ : K ≃ₐ[k] K).injective).toRingHom
      (Õ'.equivMapOfInjective ((σ : K ≃ₐ[k] K) : K →+* K) (σ : K ≃ₐ[k] K).injective).surjective
  have hBE : ∀ O₁ ∈ E, ∀ f : K, f ∈ Bc.toSubring → f ∈ O₁ := by
    intro O₁ h f hf
    obtain ⟨σ, rfl⟩ := hEmem O₁ h
    rw [mem_map_algEquiv_iff]
    refine hBcÕ' _ (hBcG _ (G.inv_mem σ.2) f hf)
  have hEG : ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∀ O₁ ∈ E, ∃ O₂ ∈ E, ∀ f : K, f ∈ O₂ ↔ τ f ∈ O₁ := by
    intro τ hτ O₁ h
    obtain ⟨σ, rfl⟩ := hEmem O₁ h
    refine ⟨Õ'.map (((⟨τ, hτ⟩⁻¹ * σ : ↥G) : K ≃ₐ[k] K) : K →+* K), Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, fun f => ?_⟩
    rw [mem_map_algEquiv_iff, mem_map_algEquiv_iff]
    change ((⟨τ, hτ⟩⁻¹ * σ : ↥G) : K ≃ₐ[k] K).symm f ∈ Õ' ↔ (σ : K ≃ₐ[k] K).symm (τ f) ∈ Õ'
    have : ((⟨τ, hτ⟩⁻¹ * σ : ↥G) : K ≃ₐ[k] K).symm f = (σ : K ≃ₐ[k] K).symm (τ f) := by
      apply ((⟨τ, hτ⟩⁻¹ * σ : ↥G) : K ≃ₐ[k] K).injective
      rw [AlgEquiv.apply_symm_apply]
      change f = (τ⁻¹ * (σ : K ≃ₐ[k] K)) ((σ : K ≃ₐ[k] K).symm (τ f))
      rw [AlgEquiv.mul_apply, AlgEquiv.apply_symm_apply]
      change f = τ.symm (τ f)
      rw [AlgEquiv.symm_apply_apply]
    rw [this]
  have hsep : ∀ (O₁ : Subring K) (hO₁ : O₁ ∈ E), ∃ (b : K) (hb : b ∈ Bc.toSubring),
      (⟨b, hBV b hb⟩ : ↥Wx) ∈ maximalIdeal ↥Wx ∧ IsUnit (⟨b, hBE O₁ hO₁ b hb⟩ : ↥O₁) := by
    intro O₁ hO₁
    obtain ⟨σ, rfl⟩ := hEmem O₁ hO₁
    obtain ⟨f, hfÕ', hfW⟩ := hsep0 (σ : K ≃ₐ[k] K) σ.2
    obtain ⟨g, h, hg, hh, hhu, hfh⟩ := (hlocÕ' f).mp hfÕ'
    have hσh : (σ : K ≃ₐ[k] K) h ∈ Bc := hBcG _ σ.2 h hh
    refine ⟨(σ : K ≃ₐ[k] K) h, hσh, ?_, ?_⟩
    ·
      by_contra hnot
      have hu : IsUnit (⟨(σ : K ≃ₐ[k] K) h, hBV _ hσh⟩ : ↥Wx) := by
        by_contra hnu; exact hnot ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
      obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp hu
      have hc' : (σ : K ≃ₐ[k] K) h * (c : K) = 1 := congrArg Subtype.val hc
      apply hfW
      have : (σ : K ≃ₐ[k] K) f = (σ : K ≃ₐ[k] K) g * (c : K) := by
        have e1 : (σ : K ≃ₐ[k] K) f * (σ : K ≃ₐ[k] K) h = (σ : K ≃ₐ[k] K) g := by rw [← map_mul, hfh]
        calc (σ : K ≃ₐ[k] K) f = (σ : K ≃ₐ[k] K) f * ((σ : K ≃ₐ[k] K) h * (c : K)) := by rw [hc', mul_one]
          _ = ((σ : K ≃ₐ[k] K) f * (σ : K ≃ₐ[k] K) h) * (c : K) := by ring
          _ = (σ : K ≃ₐ[k] K) g * (c : K) := by rw [e1]
      rw [this]
      exact Wx.toSubring.mul_mem (hBV _ (hBcG _ σ.2 g hg)) c.2
    ·
      have hhu' : IsUnit (⟨h, (hlocÕ' h).mpr ⟨h * h, h, Bc.mul_mem hh hh, hh, hhu, rfl⟩⟩ : ↥Õ') := hhu _
      obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp hhu'
      have hc' : h * (c : K) = 1 := congrArg Subtype.val hc
      refine isUnit_iff_exists_inv.mpr ⟨⟨(σ : K ≃ₐ[k] K) (c : K), ?_⟩, Subtype.ext ?_⟩
      · rw [mem_map_algEquiv_iff, AlgEquiv.symm_apply_apply]; exact c.2
      · change (σ : K ≃ₐ[k] K) h * (σ : K ≃ₐ[k] K) (c : K) = 1
        rw [← map_mul, hc', map_one]
  have hp : ∃ (b : K) (hb : b ∈ Bc.toSubring), b ≠ 0 ∧ (⟨b, hBV b hb⟩ : ↥Wx) ∈ maximalIdeal ↥Wx := by
    obtain ⟨b, hb, hbm, hbu⟩ := hsep Õ' hÕ'E
    exact ⟨b, hb, fun h0 => by apply hbu.ne_zero; exact Subtype.ext h0, hbm⟩
  have hBcG' : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ Bc.toSubring → σ f ∈ Bc.toSubring := fun σ hσ f hf => hBcG σ hσ f hf
  obtain ⟨f, hfG, hfE, hfW⟩ :=
    Subring.exists_forall_algEquiv_apply_eq_and_forall_mem_and_not_mem_valuationSubring G hGfin Bc.toSubring hBcG' Wx hBV hp
      E hEloc hBE hEG hsep
  have hfK₀ : f ∈ K₀ := by
    rw [hK₀, IntermediateField.mem_fixedField_iff]
    intro σ hσ; exact hfG σ hσ
  refine ⟨⟨f, hfK₀⟩, (hO'Õ' _).mpr (hfE Õ' hÕ'E), fun hW => hfW ?_⟩
  exact hW

end S3C4Pernode

open S3C4Glue in

theorem solution
    (q : ℕ)
    [Fact q.Prime]
    (hq3 : q = 3)
    (M' : ℕ)
    [NeZero M']

    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (s : ↥W)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (π₀ : ↥k₀)
    (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (ℓ : ℕ)
    (ζ₀ : ↥k₀)
    (ϖt : ↥k₀)
    (Kb : IntermediateField ↥k₀ (AlgebraicClosure ℚ))
    (Ab : ValuationSubring ↥Kb)
    (hAb : ∀ x : ↥Kb, x ∈ Ab ↔ (x : (AlgebraicClosure ℚ)) ∈ A)
    (ϖb : ↥Ab)
    (ξ : ↥k₀)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ]
    [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ]
    (jℓ : ↥Kℓ)
    [Fact (jℓ ≠ 0)]
    (ϖt' : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (y : Ideal ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ))
    (Bt : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)
    (Wt : ValuationSubring ↥Kℓ)
    (hBW : ∀ f : ↥Kℓ, f ∈ Bt → f ∈ Wt)
    (n : ℕ)
    (γ₀ : SL(2, ℤ))
    (τ₀ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ)
    (m : ℕ)
    (ζc : (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hjK : ModularCurve.jqNModC ↥k₀ q ∈ Kℓ)
    (a₀ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (ends : Finset (Subring ↥Kℓ))
    (hqM' : ¬ q ∣ M')
    (hA : A.LiesOverPrime q)
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
        ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
          ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
            coeffMap (IsLocalRing.residue ↥A) y)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
        Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)
    (hℓ : ℓ.Prime)
    (hℓ3 : 3 ≤ ℓ)
    (hℓq : ℓ ≠ q)
    (hℓM' : ¬ ℓ ∣ M')
    (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))
    (hKb : Kb = ⊥)
    (hϖb : maximalIdeal ↥Ab = Ideal.span {ϖb})
    (hϖb0 : ϖb ≠ 0)
    (htame : IsUnit ((ℓg - 1 : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hξ : IsPrimitiveRoot ξ q)
    (hKℓ : Kℓ = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (hjℓ : ((jℓ : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq)
    (hϖt' : (ϖt' : ↥k₀) = ϖt)
    (hy : y.IsMaximal)
    (hϖy : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨π₀, hπ⟩ ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
        (φ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) →+* Ω), RingHom.ker φ = y → φ (jChartFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ∈ ModularCurve.ssJSet q Ω)
    (hover : (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
        (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
            ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        ∀ (hgK : (coeffEmb ↥k₀ g) ∈ Kℓ)
          (hgC : (⟨_, hgK⟩ : ↥Kℓ) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
        ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
          residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
          (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) -
              algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨c, hc⟩ ∈ y))
    (hOrbit : ∀ y' : Ideal ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), y'.IsMaximal →
        algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨π₀, hπ⟩ ∈ y' →
          (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
            (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
            (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
              0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
              0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
                ↥(modularFunctionFieldBar M'))) →
            (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
            ∀ (hgK : (coeffEmb ↥k₀ g) ∈ Kℓ)
              (hgC : (⟨_, hgK⟩ : ↥Kℓ) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
            ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
              residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
              (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) -
                  algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨c, hc⟩ ∈ y') →
        ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma q) (_ : γ ∈ CongruenceSubgroup.Gamma0 M')
          (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ),
          ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ ∧
          (∀ f : ↥Kℓ, f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ →
            τ f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ∧
          (∀ (f : ↥Kℓ) (hf : f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)
            (hf' : τ f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
            (⟨f, hf⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) ∈ y ↔ (⟨τ f, hf'⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) ∈ y'))
    (hS1 :
        chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ ≤ Bt ∧
        (∀ f : ↥Kℓ, ∃ g h : ↥Bt, (h : ↥Kℓ) ≠ 0 ∧ f * (h : ↥Kℓ) = (g : ↥Kℓ)) ∧

        Algebra.FormallySmooth ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ∧ Algebra.FinitePresentation ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ∧
        Ring.KrullDimLE 1 (↥Bt ⧸ Ideal.span {algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ⟨π₀, hπ⟩}) ∧

        (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ Wt ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) ∧
        maximalIdeal ↥Wt = Ideal.span {(⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hBW _ (Bt.algebraMap_mem ⟨π₀, hπ⟩)⟩ : ↥Wt)} ∧
        IsDiscreteValuationRing ↥Wt ∧
        (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ↔
          ∃ hb : (b : ↥Kℓ) ∈ Wt, (⟨(b : ↥Kℓ), hb⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) ∧
        (∀ f : ↥Kℓ, f ∈ Wt ↔ ∃ g h : ↥Bt, (⟨(h : ↥Kℓ), hBW _ h.2⟩ : ↥Wt) ∉ maximalIdeal ↥Wt ∧ f * (h : ↥Kℓ) = (g : ↥Kℓ)) ∧

        (∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))),
          ∃ (ρ : ↥Bt →+* DrinfeldCurve.CoordRing q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))),
            Function.Surjective ρ ∧
            (∀ b : ↥Bt, ρ b = 0 ↔ (⟨(b : ↥Kℓ), hBW _ b.2⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) ∧
            (∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), ρ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt a) = algebraMap (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (DrinfeldCurve.CoordRing q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) (residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) a)) ∧
            (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                (∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) →
                ∃ (c : (GaloisField q 2)ˣ) (hmem : (ModularCurve.FullLevel.redQ q γ, c) ∈ DrinfeldCurve.hSubgroup q),
                  (∀ (b : ↥Bt) (hb : τ (b : ↥Kℓ) ∈ Bt), ρ ⟨τ (b : ↥Kℓ), hb⟩ = DrinfeldCurve.hAction q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨_, hmem⟩ (ρ b)) ∧
                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥Kℓ, τ k = k) → c ≠ 1) ∧

                  (∃ (γ' : SL(2, ℤ)) (_ : γ' ∈ CongruenceSubgroup.Gamma q) (_ : γ' ∈ CongruenceSubgroup.Gamma0 M') (τ' : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ)
                      (_ : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ'⁻¹ Kℓ τ') (_ : ∀ f : ↥Kℓ, f ∈ Wt ↔ τ' f ∈ Wt)
                      (hmem' : ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)), c) ∈ DrinfeldCurve.hSubgroup q),
                    ∀ (b : ↥Bt) (hb : τ' (b : ↥Kℓ) ∈ Bt), ρ ⟨τ' (b : ↥Kℓ), hb⟩ = DrinfeldCurve.hAction q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨_, hmem'⟩ (ρ b)))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
            ∀ f : ↥Kℓ, f ∈ Bt → τ f ∈ Bt) ∧
        (∀ Q : Ideal ↥Bt, Q.IsPrime → algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ⟨π₀, hπ⟩ ∈ Q →
          ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
            ∃ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ ∧
              ∀ b : ↥Bt, (⟨(b : ↥Kℓ), hBW _ b.2⟩ : ↥Wt) ∈ maximalIdeal ↥Wt → τ (b : ↥Kℓ) ∈ Bt ∧ ∀ hb : τ (b : ↥Kℓ) ∈ Bt, (⟨τ (b : ↥Kℓ), hb⟩ : ↥Bt) ∈ Q) ∧
        (∀ b : ↥Bt, (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
              ∀ hb : τ (b : ↥Kℓ) ∈ Bt, (⟨τ (b : ↥Kℓ), hBW _ hb⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) →
          algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ⟨π₀, hπ⟩ ∣ b))
    (hn1 : 1 ≤ n)
    (hnq : n ∣ q + 1)
    (hγ₀Γ : γ₀ ∈ CongruenceSubgroup.Gamma q)
    (hγ₀Γ0 : γ₀ ∈ CongruenceSubgroup.Gamma0 M')
    (hτ₀ : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ₀⁻¹ Kℓ τ₀)
    (hτ₀W : ∀ f : ↥Kℓ, f ∈ Wt ↔ τ₀ f ∈ Wt)
    (hm1 : 1 ≤ m)
    (hm : ∃ w : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), IsUnit w ∧ ⟨π₀, hπ⟩ ^ m = ϖt' * w)
    (hζc : ζc ^ n = 1)
    (hζcprim : ∀ k : ℕ, 0 < k → k < n → IsUnit (ζc ^ k - 1))
    (hjC : (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)
    (ha₀y : (⟨(⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ), hjC⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) a₀ ∈ y)
    (hR7 : (∀ f : ↥Kℓ, f ∈ Bt → (τ₀ ^ n) f = f) ∧
          (∀ k : ℕ, 0 < k → k < n → ∃ f : ↥Kℓ, f ∈ Bt ∧ (τ₀ ^ k) f ≠ f) ∧
          (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
              (∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) → ∃ k : ℕ, k < n ∧ ∀ f : ↥Kℓ, f ∈ Bt → τ f = (τ₀ ^ k) f) ∧
          ends.card = q + 1 ∧
          (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
              (∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) → ∀ O ∈ ends, ∃ O' ∈ ends, ∀ f : ↥Kℓ, f ∈ O ↔ τ f ∈ O') ∧
          (∀ O ∈ ends, ∀ O' ∈ ends, ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) (_ : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ),
            (∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) ∧ ∀ f : ↥Kℓ, f ∈ O ↔ τ f ∈ O') ∧
          (∀ O ∈ ends, ∀ f : ↥Kℓ, f ∈ O ↔ τ₀ f ∈ O) ∧
          (∀ O ∈ ends, ∀ O' ∈ ends, O ≠ O' → ∃ (f : ↥Kℓ) (hf : f ∈ O) (hf' : f ∈ O'),
            ¬ IsUnit (⟨f, hf⟩ : ↥O) ∧ IsUnit (⟨f, hf'⟩ : ↥O')) ∧

          (∃ Bc : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ, Algebra.FiniteType ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bc ∧
            (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                ∀ f : ↥Kℓ, f ∈ Bc → τ f ∈ Bc) ∧
            ∀ O ∈ ends, (∀ f : ↥Kℓ, f ∈ Bc → f ∈ O) ∧
              (∀ f : ↥Kℓ, f ∈ O ↔ ∃ g h : ↥Kℓ, g ∈ Bc ∧ h ∈ Bc ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g)) ∧

          (∀ O ∈ ends, ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                (∀ f : ↥Kℓ, f ∈ O → τ f ∈ Wt) → ∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) ∧
          (∀ O ∈ ends,

            (∀ f : ↥Kℓ, f ∈ O → f ∈ Wt) ∧ ∃ (_ : IsLocalRing ↥O) (_ : IsNoetherianRing ↥O),
            (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ O) ∧
            (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ O ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) ∧
            (∀ (f : ↥Kℓ) (hf : f ∈ O), ∃ (a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (ha : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a ∈ O), ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, ha⟩)) ∧

            (∃ (hϖO : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ O) (cx cy : ↥O) (u : (↥O)ˣ) (ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)))
               (γU γV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))ˣ) (θ₀ : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)) ≃ₐ[(AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))] (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) (ζc' : (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) (_ : ζc * ζc' = 1)
               (_ : IsLocalRing (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))),
              cx * cy = (⟨_, hϖO⟩ : ↥O) ^ m * (u : ↥O) ∧
              (∀ (a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (ha : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a ∈ O), ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, ha⟩) = UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) a)) ∧
              ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) = (γU : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) * UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ∧
              ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cy) = (γV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) * UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ∧
              (∀ hcy : (cy : ↥Kℓ) ∈ Wt, (⟨(cy : ↥Kℓ), hcy⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) ∧
              (∀ hcx : (cx : ↥Kℓ) ∈ Wt, (⟨(cx : ↥Kℓ), hcx⟩ : ↥Wt) ∉ maximalIdeal ↥Wt) ∧

              (∃ (hjaO : (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a₀ ∈ O) (e : ℕ) (wV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))ˣ), 1 ≤ e ∧
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨(⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a₀, hjaO⟩) =
                  (wV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) * (UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)) ^ e) ∧
              (∀ (f : ↥Kℓ) (hf : f ∈ O) (hf' : τ₀ f ∈ O),
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hf'⟩) = θ₀ (ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨f, hf⟩))) ∧
              θ₀ (UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)) - UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ζc * UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ∈
                (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) ^ 2 ∧
              θ₀ (UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)) - UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ζc' * UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ∈
                (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) ^ 2 ∧

              (∃ Wx : ValuationSubring ↥Kℓ,
                (∀ f : ↥Kℓ, f ∈ O → f ∈ Wx) ∧
                (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ Wx) ∧
                (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ Wx ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) ∧
                IsDiscreteValuationRing ↥Wx ∧
                (∃ hϖWx : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ Wx, maximalIdeal ↥Wx = Ideal.span {(⟨_, hϖWx⟩ : ↥Wx)}) ∧
                (∃ (t : ↥Wx), ∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
                  (∃ hm : Polynomial.aeval (t : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                    ∀ i, p.coeff i ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∧

                (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
                  (∃ hm : Polynomial.aeval (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                    ∀ i, p.coeff i ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∧
                (∀ hcx : (cx : ↥Kℓ) ∈ Wx, (⟨(cx : ↥Kℓ), hcx⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) ∧
                (∀ hcy : (cy : ↥Kℓ) ∈ Wx, (⟨(cy : ↥Kℓ), hcy⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) ∧
                (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) → b ∈ y) ∧
                (∃ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ∧ ∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) ∧

                (∀ O' ∈ ends, O' ≠ O → ∃ f : ↥Kℓ, f ∈ O' ∧ f ∉ Wx) ∧

                (∀ O' ∈ ends, ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
                  ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                    (∀ f : ↥Kℓ, f ∈ O' → τ f ∈ Wx) → O' = O)) ∧

              (∃ Bx : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ,
                (∀ f : ↥Kℓ, f ∈ Bx → f ∈ Bt ∧ f ∈ O) ∧
                Algebra.FiniteType ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bx ∧
                (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
                  ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                    ∀ f : ↥Kℓ, f ∈ Bx → τ f ∈ Bx) ∧
                (∀ f : ↥Kℓ, f ∈ Bx → ∀ P : AlgebraicCurve.Place ↥k₀ ↥Kℓ, 0 ≤ P.ord jℓ → 0 ≤ P.ord f) ∧
                (∀ f : ↥Kℓ, f ∈ O ↔ ∃ g h : ↥Kℓ, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g) ∧

                (∃ b : ↥Kℓ, b ∈ Bx ∧ ∀ V : ValuationSubring ↥Kℓ, (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ V ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
                  (∀ hϖV : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ V, (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hϖV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                  (∀ hjV : (jℓ : ↥Kℓ) ∈ V, (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), p.Monic →
                      ∀ hp : Polynomial.aeval (jℓ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) ∈ V,
                        (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
                    (∃ f : ↥Kℓ, f ∈ O ∧ f ∉ V) → b ∉ V))))) ∧

          (∀ V : ValuationSubring ↥Kℓ, (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ V ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
            (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ V) →
            (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y → ∀ hb : (b : ↥Kℓ) ∈ V, (⟨(b : ↥Kℓ), hb⟩ : ↥V) ∈ maximalIdeal ↥V) →
            (∀ f : ↥Kℓ, f ∈ Bt → f ∈ V) ∨
            (∃ O ∈ ends, ∀ (f : ↥Kℓ) (hfO : f ∈ O), f ∈ V ∧ (¬ IsUnit (⟨f, hfO⟩ : ↥O) → ∀ hfV : f ∈ V, (⟨f, hfV⟩ : ↥V) ∈ maximalIdeal ↥V))))
    (hR9 : (∃ b : ↥Kℓ, b ∈ Bt ∧ ∀ V : ValuationSubring ↥Kℓ, (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ V ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
            (∀ hϖV : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ V, (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hϖV⟩ : ↥V) ∈ maximalIdeal ↥V) →
            (∀ hjV : (jℓ : ↥Kℓ) ∈ V, (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), p.Monic →
                ∀ hp : Polynomial.aeval (jℓ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) ∈ V,
                  (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) → b ∉ V)))
    (hR10 : (∀ y'' : Ideal ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), y''.IsMaximal → algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨π₀, hπ⟩ ∈ y'' →
            (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                ¬ (∀ (b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) (hb : τ (b : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
                    b ∈ y ↔ (⟨τ (b : ↥Kℓ), hb⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) ∈ y'')) →
            ∃ b : ↥Kℓ, b ∈ Bt ∧ ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
              ∀ V : ValuationSubring ↥Kℓ,
                (∀ c : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (c : ↥Kℓ) ∈ V) →
                (∀ (c : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) (hc : τ.symm (c : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
                    (⟨τ.symm (c : ↥Kℓ), hc⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) ∈ y'' → ∀ hcV : (c : ↥Kℓ) ∈ V, (⟨(c : ↥Kℓ), hcV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                b ∉ V))
    (hn : n = 2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (G : Subgroup (↥Kℓ ≃ₐ[↥k₀] ↥Kℓ))
    (hG : G = Subgroup.closure {τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ})
    (K₀ : IntermediateField ↥k₀ ↥Kℓ)
    (hK₀ : K₀ = IntermediateField.fixedField G)
    (B₀ : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)
    (hB₀ : ∀ f : ↥Kℓ, f ∈ B₀ ↔ f ∈ Bt ∧ ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → τ f = f)
    (W₀' : ValuationSubring ↥K₀)
    (hW₀' : ∀ f : ↥K₀, f ∈ W₀' ↔ ((f : ↥Kℓ)) ∈ Wt)

    (nodes : Finset (Subring ↥K₀))
    (hnodes : ∀ O' ∈ nodes, ∃ Õ' ∈ ends, ∀ f : ↥K₀, f ∈ O' ↔ ((f : ↥Kℓ)) ∈ Õ') :
    ∀ Õ ∈ ends, ∀ (O : Subring ↥K₀), O = Õ.comap (algebraMap ↥K₀ ↥Kℓ) →

      (

                (∀ f : ↥K₀, f ∈ O → f ∈ W₀') ∧ ∃ (_ : IsLocalRing ↥O) (_ : IsNoetherianRing ↥O),
                (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥K₀ x ∈ O) ∧
                (∀ (f : ↥K₀) (hf : f ∈ O), ∃ (x : ↥k₀) (hx : algebraMap ↥k₀ ↥K₀ x ∈ O), (x : (AlgebraicClosure ℚ)) ∈ A ∧
                  ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, hx⟩)) ∧

                (∃ (E₀ : ℕ) (_ : 1 ≤ E₀)

                   (_ : ∃ v : ↥k₀, (v : (AlgebraicClosure ℚ)) ∈ A ∧ ((v⁻¹ : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A ∧
                      π₀ ^ E₀ = ϖt ^ (2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))) * v)
                   (hπO : algebraMap ↥k₀ ↥K₀ π₀ ∈ O) (cx cy : ↥O) (u : (↥O)ˣ)
                   (ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))
                   (γU γV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))ˣ),
                  cx * cy = (⟨_, hπO⟩ : ↥O) ^ E₀ * (u : ↥O) ∧
                  (∀ (x : ↥k₀) (hx : (x : (AlgebraicClosure ℚ)) ∈ A) (hxO : algebraMap ↥k₀ ↥K₀ x ∈ O),
                    ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hxO⟩) =
                      UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨x, hx⟩)) ∧
                  ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) = (γU : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) ∧
                  ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cy) = (γV : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) ∧
                  ((cy : ↥K₀) ∈ W₀') ∧ (∀ hcy : (cy : ↥K₀) ∈ W₀', (⟨(cy : ↥K₀), hcy⟩ : ↥W₀') ∈ maximalIdeal ↥W₀') ∧
                  (∀ hcx : (cx : ↥K₀) ∈ W₀', (⟨(cx : ↥K₀), hcx⟩ : ↥W₀') ∉ maximalIdeal ↥W₀') ∧

                  (∃ (hjF : (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a₀ ∈ K₀)
                     (hjO : (⟨_, hjF⟩ : ↥K₀) ∈ O) (e : ℕ) (wV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))ˣ), 1 ≤ e ∧
                    ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hjO⟩) =
                      (wV : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * (UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) ^ e) ∧

                  (∃ Wx : ValuationSubring ↥K₀,
                    (∀ f : ↥K₀, f ∈ O → f ∈ Wx) ∧
                    (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥K₀ x ∈ Wx) ∧
                    IsDiscreteValuationRing ↥Wx ∧
                    (∃ hπW : algebraMap ↥k₀ ↥K₀ π₀ ∈ Wx, maximalIdeal ↥Wx = Ideal.span {(⟨_, hπW⟩ : ↥Wx)}) ∧
                    (∃ t : ↥Wx, ∀ p : Polynomial ↥k₀, (∀ n, ((p.coeff n : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
                      (∃ hm : Polynomial.aeval (t : ↥K₀) p ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                        ∀ n, ∃ hc : algebraMap ↥k₀ ↥K₀ (p.coeff n) ∈ Wx, (⟨_, hc⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) ∧
                    (∀ hcx : (cx : ↥K₀) ∈ Wx, (⟨(cx : ↥K₀), hcx⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) ∧
                    (∀ hcy : (cy : ↥K₀) ∈ Wx, (⟨(cy : ↥K₀), hcy⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) ∧
                    (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
                      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
                      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
                        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
                          ↥(modularFunctionFieldBar M'))) →
                      ∀ (hgK : (coeffEmb ↥k₀ g) ∈ Kℓ), ∃ hF : (⟨(coeffEmb ↥k₀ g), hgK⟩ : ↥Kℓ) ∈ K₀,
                        (⟨_, hF⟩ : ↥K₀) ∈ Wx ∧
                        (∀ hW : (⟨_, hF⟩ : ↥K₀) ∈ Wx, (⟨_, hW⟩ : ↥Wx) ∈ maximalIdeal ↥Wx ↔
                          (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') = 0) ∧
                        ((R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                          (⟨_, hF⟩ : ↥K₀) ∈ O ∧
                          ∀ (hO : (⟨_, hF⟩ : ↥K₀) ∈ O) (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A) (hcO : algebraMap ↥k₀ ↥K₀ c ∈ O),
                            residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
                            ¬ IsUnit ((⟨_, hO⟩ : ↥O) - ⟨_, hcO⟩))) ∧

                    (∀ O' ∈ nodes, O' ≠ O → ∃ f : ↥K₀, f ∈ O' ∧ f ∉ Wx)) ∧

                  (∃ Bx : Subring ↥K₀,
                    (∀ f : ↥K₀, f ∈ Bx → (f : ↥Kℓ) ∈ B₀ ∧ f ∈ O) ∧
                    (∀ (f : ↥K₀), f ∈ Bx → ∀ P : Place ↥k₀ ↥Kℓ,
                      0 ≤ P.ord (jℓ : ↥Kℓ) → 0 ≤ P.ord (f : ↥Kℓ)) ∧
                    (∀ f : ↥K₀, f ∈ O ↔ ∃ g h : ↥K₀, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g) ∧
                    (∀ f : ↥K₀, ∃ g h : ↥K₀, g ∈ Bx ∧ h ∈ Bx ∧ h ≠ 0 ∧ f * h = g) ∧
                    (∃ T : Finset ↥K₀, Bx = Subring.closure
                      ({f : ↥K₀ | ∃ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ∧ f = algebraMap ↥k₀ ↥K₀ x} ∪ (↑T : Set ↥K₀))) ∧

                    (∃ b : ↥K₀, b ∈ Bx ∧ ∀ V : ValuationSubring ↥K₀,
                      (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥K₀ x ∈ V) →
                      (∀ hπV : algebraMap ↥k₀ ↥K₀ π₀ ∈ V, (⟨_, hπV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                      ∀ (hjK' : (coeffEmb ↥k₀ jq) ∈ Kℓ) (hjF : (⟨(coeffEmb ↥k₀ jq), hjK'⟩ : ↥Kℓ) ∈ K₀) (hjV : (⟨_, hjF⟩ : ↥K₀) ∈ V),
                        (∀ p : Polynomial ↥k₀, p.Monic → (∀ i : ℕ, ((p.coeff i : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
                          ∀ hp : Polynomial.aeval (⟨_, hjF⟩ : ↥K₀) (p.map (algebraMap ↥k₀ ↥K₀)) ∈ V,
                            (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
                      (∃ f : ↥K₀, f ∈ O ∧ f ∉ V) → b ∉ V))) ) := by
  classical
  haveI hq0 : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  have hR7' := hR7
  have hS1' := hS1
  obtain ⟨h70, h71, h72, h73, h74, h75, h76, h77, hR7common, hR7one, h78, h79⟩ := hR7
  obtain ⟨hR1a, hR1b, hR2a, hR2b, hR2c, hR3a, hR3b, hR3c, hR3d, hR3e, hR4, hR5a, hR5b, hR5c⟩ := hS1

  have hob1 := S3C4Glue.C3aux_exists_emb k₀ q ξ hξ
  obtain ⟨ι, hι'⟩ := hob1
  have hι : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / q) := ⟨ι, hι'⟩
  have hob2 := ModularCurve.FullLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom_of_eq_levelH_inf_ker q M' hqM' ℓg hℓgM' ↥k₀ ξ hξ hι H₁ hH₁ Kℓ hKℓ
  obtain ⟨huniq, hmul, hone⟩ := hob2
  have hobE1 :=
    ModularCurve.FullLevel.exists_finite_subgroup_forall_mem_iff_exists_isLevelAutAt_of_exists_ringHom_of_eq_levelH_inf_ker
      q M' hqM' ℓg hℓgM' ↥k₀ ξ hξ hι H₁ hH₁ Kℓ hKℓ
  obtain ⟨Gfull, hGfin, hGmem⟩ := hobE1
  have hex := ModularCurve.FullLevel.exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker
      q M' hqM' ℓg hℓgM' ↥k₀ ξ hξ H₁ hH₁ Kℓ hKℓ
  have hone1 : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ 1 Kℓ 1 := hone 1 (Subgroup.one_mem _) (Subgroup.one_mem _) (by simp)

  obtain ⟨Bc, hBcft, hBcG, hBcO⟩ := hR7common
  have hGatt : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ :=
    S3C4Glue.att_of_mem_closure (CongruenceSubgroup.Gamma0 M') (CongruenceSubgroup.Gamma q) (fun γ τ => ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ Kℓ τ)
      huniq hmul hone1 hex G hG
  have hGfin' : Finite ↥G := by
    have hGle : G ≤ Gfull := by
      rw [hG, Subgroup.closure_le]
      rintro τ ⟨γ, -, hγ0, hτ⟩
      exact (hGmem τ).mpr ⟨γ, hγ0, hτ⟩
    haveI := hGfin
    exact Finite.of_injective (Subgroup.inclusion hGle) (Subgroup.inclusion_injective hGle)
  have hOW : ∀ O ∈ ends, ∀ f : ↥Kℓ, f ∈ O → f ∈ Wt := fun O hO => (h78 O hO).1
  have hOlocal : ∀ O ∈ ends, IsLocalRing ↥O := by
    intro O hO
    have hob3 := h78 O hO
    obtain ⟨-, hl, -⟩ := hob3
    exact hl

  have hBcG' : ∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → ∀ f : ↥Kℓ, f ∈ Bc → σ f ∈ Bc := by
    intro σ hσ f hf
    have hob4 := hGatt σ hσ
    obtain ⟨γ, h1, h0, hatt⟩ := hob4
    exact hBcG γ h1 h0 σ hatt f hf
  have hRfix : ∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → ∀ r : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), σ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ r) = algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ r := by
    intro σ _ r
    rw [IsScalarTower.algebraMap_apply ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ r]
    exact σ.commutes _
  have hS : {f : ↥K₀ | ∃ r : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), (f : ↥Kℓ) = algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ r} =
      {f : ↥K₀ | ∃ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ∧ f = algebraMap ↥k₀ ↥K₀ x} := by
    ext f
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨r, hr⟩
      refine ⟨(r : ↥k₀), r.2, Subtype.ext ?_⟩
      rw [hr, IsScalarTower.algebraMap_apply ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ r]
      rfl
    · rintro ⟨x, hx, hfx⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      rw [hfx, IsScalarTower.algebraMap_apply ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ ⟨x, hx⟩]
      rfl
  intro Õ hÕ O hOdef
  subst hOdef
  haveI hÕloc : IsLocalRing ↥Õ := hOlocal Õ hÕ

  have hob5 := h78 Õ hÕ
  obtain ⟨hOW₁, hÕloc', hÕnoeth, hCO, hconstsO, hresO, -⟩ := hob5
  have hob6 := hBcO Õ hÕ
  obtain ⟨hBÕ, hlocÕ⟩ := hob6

  have hτ₀G : τ₀ ∈ G := by
    rw [hG]; exact Subgroup.subset_closure ⟨γ₀, hγ₀Γ, hγ₀Γ0, hτ₀⟩
  have hτ₀n : ∀ f : ↥Kℓ, (τ₀ ^ n) f = f := S3C4Glue.apply_eq_self_of_frac Bt hR1b (τ₀ ^ n) h70
  have hHcyc := S3C4Glue.exists_eq_pow_of_stabilises (CongruenceSubgroup.Gamma0 M') (CongruenceSubgroup.Gamma q)
    (fun γ τ => ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ Kℓ τ) G hGatt Bt Wt hR1b τ₀ n h72 Õ hOW₁ (hR7one Õ hÕ)

  have hInvFin : ∀ (Bx : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ) (BG : Subring ↥Kℓ), Algebra.FiniteType ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bx →
      (∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → ∀ f : ↥Kℓ, f ∈ Bx → σ f ∈ Bx) →
      (∀ f : ↥Kℓ, f ∈ BG ↔ f ∈ Bx ∧ ∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → σ f = f) →
      IsNoetherianRing ↥BG ∧ (∀ (hle : BG ≤ Bx.toSubring), letI := (Subring.inclusion hle).toAlgebra; Module.Finite ↥BG ↥Bx.toSubring) ∧
      (∃ T : Finset ↥K₀, Bx.toSubring.comap (algebraMap ↥K₀ ↥Kℓ) = Subring.closure
        ({f : ↥K₀ | ∃ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ∧ f = algebraMap ↥k₀ ↥K₀ x} ∪ (↑T : Set ↥K₀))) := by
    intro Bx BG hft hBxG hBGdef
    have hBG : BG = S3C4Glue.fixedPart G Bx.toSubring := by
      ext f; rw [hBGdef, S3C4Glue.mem_fixedPart, Subalgebra.mem_toSubring]
    subst hBG
    have hob7 := S3C4Glue.noetherian_and_finite_fixedPart G hGfin' hRfix Bx hBxG hft
    obtain ⟨hno, hfi⟩ := hob7
    have hob8 := S3C4Glue.exists_finset_trace_eq_closure G hGfin' K₀ hK₀ hRfix Bx hBxG hft
    obtain ⟨T, hT⟩ := hob8
    refine ⟨hno, hfi, T, ?_⟩
    rw [hT, hS]

  have hob9 := S3C4Glue.completion_pack q A hA k₀ π₀ hπ hdvr hunif n hnq
  obtain ⟨hAdom, hAdvr, hAcompl, hπhat, hnunit⟩ := hob9
  haveI := hAdom; haveI := hAdvr; haveI := hAcompl
  have hpinu : ¬ IsUnit ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) := by
    intro hu
    have h1 : IsUnit (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) :=
      (isUnit_pow_iff (by omega : m ≠ 0)).mp hu
    have h2 : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩ ∈
        maximalIdeal (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := by
      rw [hπhat]; exact Ideal.mem_span_singleton_self _
    exact (IsLocalRing.mem_maximalIdeal _).mp h2 h1
  haveI hmodelloc : IsLocalRing (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)) :=
    ModularCurve.UVCrossingModel.isLocalRing_of_not_isUnit hpinu
  haveI hmodelcompl := ModularCurve.UVCrossingModel.isAdicComplete_maximalIdeal
    (Ô := AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)

  have hCG : ∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → ∀ f : ↥Kℓ, f ∈ (chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) → σ f ∈ (chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) := by
    intro σ hσ f hf
    have hob10 := hGatt σ hσ
    obtain ⟨γ, -, h0, hatt⟩ := hob10
    exact ModularCurve.FullLevel.map_mem_chartAlgFin_of_isLevelAutAt q M' ↥k₀ q ξ ⟨ι, hι'⟩ Kℓ ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) jℓ hjℓ H₁ γ⁻¹ σ hatt f hf
  have hCWt : ∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ Wt := fun b => hBW _ (hR1a b.2)

  have hsplit₁ := fun (Wx : ValuationSubring ↥Kℓ) (hOWx : ∀ f : ↥Kℓ, f ∈ Õ → f ∈ Wx) (hWxdvr : IsDiscreteValuationRing ↥Wx)
      (hCWx : ∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ Wx) hXy hXne =>
    S3C4Glue.exists_invariant_split G hGfin' (chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) hCG Wt Wx hCWt hCWx y hy hR3d hXy hXne
  have hstabW : ∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → (∀ f : ↥Kℓ, f ∈ Õ → σ f ∈ Wt) → ∀ f : ↥Kℓ, f ∈ Wt ↔ σ f ∈ Wt := by
    intro σ hσ h
    have hob11 := hGatt σ hσ
    obtain ⟨γ, hγq, hγ0, hatt⟩ := hob11
    exact hR7one Õ hÕ γ hγq hγ0 σ hatt h
  have hsplit₂ := fun (c : ↥Kℓ) (hcO : c ∈ Õ) (hcu : ¬ IsUnit (⟨c, hcO⟩ : ↥Õ))
      (hcW : ∀ hcW : c ∈ Wt, (⟨c, hcW⟩ : ↥Wt) ∉ maximalIdeal ↥Wt) =>
    S3C4Glue.exists_invariant_cosplit G hGfin' Bc hBcG' Õ hBÕ hlocÕ hresO Wt hOW₁ hstabW c hcO hcu hcW

  have hN3wit := fun (Wx : ValuationSubring ↥Kℓ) h1 h2 h3 h4 h5 h6 h7 =>
    ModularCurve.FullLevel.Diamond.exists_residuallyTranscendental_trace_of_igusaBranch_of_rigidChart_of_eq_levelH_inf_ker q M' hqM' ℓg hℓg hℓg12 hℓgM' A hA W hW R₀ hR₀ s k₀ π₀ hπ hdvr hunif H₁ hH₁ Kℓ hKℓ jℓ hjℓ y hy hϖy hss hover hjK hjC a₀ ha₀y ξ hξ G hGatt K₀ hK₀ Õ Wx h1 h2 h3 h4 h5 h6 h7
  have hN3laws := fun (Wx : ValuationSubring ↥Kℓ) h1 h2 h3 h4 h5 h6 =>
    ModularCurve.FullLevel.Diamond.levelLaws_trace_of_igusaBranch_of_rigidChart_of_eq_levelH_inf_ker q M' hqM' ℓg hℓg hℓg12 hℓgM' A hA W hW R₀ hR₀ s k₀ π₀ hπ hdvr hunif H₁ hH₁ Kℓ hKℓ jℓ hjℓ y hy hϖy hss hover hjK hjC a₀ ha₀y ξ hξ Wt hR3d G hGatt K₀ hK₀ Õ hCO hOW₁ (Õ.comap (algebraMap ↥K₀ ↥Kℓ)) rfl Wx h1 h2 h3 h4 h5 h6

  have hfracO : ∀ f : ↥Kℓ, ∃ a b : ↥Kℓ, a ∈ Õ ∧ b ∈ Õ ∧ b ≠ 0 ∧ f * b = a := by
    intro f
    haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin ↥k₀ ({(jℓ : ↥Kℓ)} : Set ↥Kℓ)) ↥Kℓ := by
      have h0 := ModularCurve.transcendental_coeffEmb_jq ↥k₀ M'
      have h1 : Transcendental ↥k₀ (coeffEmb ↥k₀ jq : LaurentSeries ↥k₀) :=
        (transcendental_algebraMap_iff (R := ↥k₀) (S := ↥(laurentBaseChange ↥k₀ (modularFunctionFieldFull M')))
          (A := LaurentSeries ↥k₀) Subtype.val_injective).mpr h0
      have h2 : Transcendental ↥k₀ (jℓ : ↥Kℓ) := by
        refine (transcendental_algebraMap_iff (R := ↥k₀) (S := ↥Kℓ) (A := LaurentSeries ↥k₀) Subtype.val_injective).mp ?_
        rw [show algebraMap ↥Kℓ (LaurentSeries ↥k₀) jℓ = (jℓ : LaurentSeries ↥k₀) from rfl, hjℓ]; exact h1
      have hob12 := ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField ↥k₀
        (q ^ 2 * M') H₁
      obtain ⟨hcurve, hess⟩ := hob12
      rw [← hKℓ] at hcurve hess
      haveI := hcurve; haveI := hess
      haveI := AlgebraicCurve.IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType h2
      exact Algebra.IsAlgebraic.of_finite _ _
    haveI hfr := AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ ({(jℓ : ↥Kℓ)} : Set ↥Kℓ)
    have hob13 := IsLocalization.surj (nonZeroDivisors ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) (S := ↥Kℓ) f
    obtain ⟨⟨a, b⟩, hab⟩ := hob13
    refine ⟨(a : ↥Kℓ), (b : ↥Kℓ), hCO a, hCO b, ?_, ?_⟩
    · exact fun h0 => (mem_nonZeroDivisors_iff_ne_zero.mp b.2) (Subtype.ext h0)
    · simpa using hab
  have hN4frac := fun (Bx : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ) (hBxG : ∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → ∀ f : ↥Kℓ, f ∈ Bx → σ f ∈ Bx)
      (hBxO : ∀ f : ↥Kℓ, f ∈ Bx → f ∈ Õ) hloc =>
    S3C4Glue.exists_frac_invariants G hGfin' K₀ hK₀ Bx.toSubring (fun σ hσ f hf => hBxG σ hσ f hf) Õ hBxO hloc hfracO

  have hjfix : ∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → σ (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) = (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) := by
    intro σ hσ
    have hob14 := hGatt σ hσ
    obtain ⟨γ, hγq, hγ0, hatt⟩ := hob14
    exact jOf_fixed_harness q M' hqM' ℓg hℓg hℓg12 hℓgM' k₀ ξ hξ H₁ hH₁ Kℓ hKℓ hjK γ hγq hγ0 σ hatt
  have hN5 := fun (Bx : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ) (hBxG : ∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → ∀ f : ↥Kℓ, f ∈ Bx → σ f ∈ Bx) hRN9 =>
    ModularCurve.FullLevel.Diamond.exists_invariant_notMem_of_endChartPole_of_rigidChart_of_eq_levelH_inf_ker q M' hqM' ℓg hℓg hℓg12 hℓgM' A hA W hW R₀ hR₀ s k₀ π₀ hπ hdvr hunif H₁ hH₁ Kℓ hKℓ jℓ hjℓ y hy hϖy hss hover hjK hjC a₀ ha₀y ξ hξ G hGfin' hGatt K₀ hK₀ Õ (Õ.comap (algebraMap ↥K₀ ↥Kℓ)) rfl Bx hBxG hRN9
  exact ModularCurve.FullLevel.Diamond.pernodeConclusion_of_pernodeHyps_of_rigidChart_linkedScalars_of_eq_three_of_dvd
    q hq3 M' ℓg hℓg hℓg12 hℓgM' A W hle R₀ s k₀ π₀ hπ ℓ ζ₀ ϖt Kb Ab hAb ϖb ξ H₁ hH₁ Kℓ jℓ ϖt' y Bt Wt hBW n γ₀ τ₀ m ζc hjK a₀ ends hqM' hA hW hR₀ hdvr hunif hhens hres hκ hℓ hℓ3 hℓq hℓM' hζ₀ hϖtA hϖt hKb hϖb hϖb0 htame hξ hKℓ hjℓ hϖt' hy hϖy hss hover hOrbit hS1' hn1 hnq hγ₀Γ hγ₀Γ0 hτ₀ hτ₀W hm1 hm hζc hζcprim hjC ha₀y hR7' hR9 hR10 hn G hG K₀ hK₀ B₀ hB₀ W₀' hW₀' nodes
    Õ (Õ.comap (algebraMap ↥K₀ ↥Kℓ)) hÕ (fun f => Iff.rfl) hGfin' hτ₀G hGatt hτ₀n hHcyc hInvFin hAdom hAdvr hAcompl hπhat hnunit hmodelloc hmodelcompl
    hsplit₁ hsplit₂ hN3wit hN3laws hN4frac hjfix hN5
    (fun Wx h1 h2 h3 h4 h5 h6 h7 h8 h9 => S3C4Pernode.hIGSEP_discharge (CongruenceSubgroup.Gamma0 M') (CongruenceSubgroup.Gamma q)
      (fun γ τ => ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ Kℓ τ) G hGfin' hGatt K₀ hK₀ Bc hBcG' ends hOlocal hBcO Õ hÕ nodes hnodes (Õ.comap (algebraMap ↥K₀ ↥Kℓ)) (fun f => Iff.rfl) Wx h1 h9)

end S_ModularCurve_FullLevel_Diamond_pernodeConclusion_traces_of_rigidChart_linkedScalars_of_eq_three_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_pernodeConclusion_traces_of_rigidChart_linkedScalars_of_eq_three_of_dvd (solution)
