-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_prime_map_sup_span_eq_maximalIdeal_and_isUnramifiedAt_of_map_jChartFin_mem_xH_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/1fd273f9-1c70-5b52-b23a-8f57c4786e3e

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_Algebra_isUnramifiedAt_of_height_eq_one_of_not_mem_of_ramificationIndexAlong_eq_one_of_centre
import Theorems.Thm_ModularCurve_FullLevel_ramificationIndexAlong_inclusion_eq_one_of_ord_eq_zero_of_ord_sub_eq_zero_xH_levelH
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_FullLevel_existsUnique_prime_le_jChartFin_sub_mem_map_sup_span_eq_maximalIdeal_chartAlgFin_gamma0_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_prime_map_sup_span_eq_maximalIdeal_and_isUnramifiedAt_of_map_jChartFin_mem_xH_of_isAlgebraic
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure"
p2m_attr_erase "instance" "instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instIsElliptic_tateBase ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord RegularLocalRingQuotientAscent.dualNumberFst_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some"
p2m_attr_erase "simp" "FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun"
p2m_attr_erase "simp" "KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

open AlgebraicCurve.TwoChartIntegralModel

namespace E149ELLAux

open scoped MatrixGroups

scoped instance gammaH_finiteIndex (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : (CohCarrier.GammaH M H).FiniteIndex := by
  refine @Subgroup.finiteIndex_of_le _ _ (CongruenceSubgroup.Gamma1 M) _ inferInstance ?_
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  have h0 : A ∈ CongruenceSubgroup.Gamma0 M := CongruenceSubgroup.Gamma1_in_Gamma0 M hA
  refine ⟨h0, ?_⟩
  have h1 := ((CongruenceSubgroup.Gamma1_mem M A).mp hA).2.1
  have : CohCarrier.gamma0Units M ⟨A, h0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h1
  rw [this]; exact H.one_mem

end E149ELLAux
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_prime_map_sup_span_eq_maximalIdeal_and_isUnramifiedAt_of_map_jChartFin_mem_xH_of_isAlgebraic.E149ELLAux"

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem E149ELL.isUnramifiedAt_of_jChartFin_not_mem
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (hle₀ : K₀ ≤ K)
    [Algebra A ↥K₀] [IsScalarTower A L ↥K₀]
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₀ ≠ 0)]
    (ι : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
    (hι : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀), ((ι b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = IntermediateField.inclusion hle₀ (b : ↥K₀)) :
    letI : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := ι.toAlgebra
    ∀ (𝔔 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) [𝔔.IsPrime], 𝔔.height = 1 →
      algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∉ 𝔔 →
      AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j ∉ 𝔔 →
      AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j - 1728 ∉ 𝔔 →
      Algebra.IsUnramifiedAt ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) 𝔔 := by
  intro 𝔔 _inst hQ1 hϖQ hjQ hj1728Q
  classical

  letI algBB : Algebra ↥(chartAlgFin A (↥K₀) j₀) ↥(chartAlgFin A (↥K) j) := ι.toAlgebra
  set φK : ↥K₀ →ₐ[L] ↥K := IntermediateField.inclusion hle₀ with hφKdef

  haveI : IsIntegrallyClosed ↥(chartAlgFin A (↥K) j) := isIntegrallyClosed_chartAlg A (↥K) _
  haveI : IsIntegrallyClosed ↥(chartAlgFin A (↥K₀) j₀) := isIntegrallyClosed_chartAlg A (↥K₀) _

  have hT : ModularGroup.T ∈ CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :=
    ModularCurve.translation_mem_GammaH _ _
  have hT₀ : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 M' := by
    rw [← CohCarrier.GammaH_top]; exact ModularCurve.translation_mem_GammaH _ _
  haveI hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) hT L K hK j hj
  haveI hFD₀ : FiniteDimensional ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma0 M') hT₀ L K₀ hK₀ j₀ hj₀
  haveI hAlg : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsAlgebraic.of_finite _ _
  haveI hAlg₀ : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ := Algebra.IsAlgebraic.of_finite _ _
  haveI hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI hsep₀ : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  have htj₀ : Transcendental A j₀ := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₀ A j₀ hj₀
  haveI : IsFractionRing ↥(chartAlgFin A (↥K) j) ↥K := isFractionRing_chartAlg A L (↥K) _
  haveI : IsFractionRing ↥(chartAlgFin A (↥K₀) j₀) ↥K₀ := isFractionRing_chartAlg A L (↥K₀) _
  haveI : IsNoetherianRing ↥(chartAlgFin A (↥K₀) j₀) := by
    haveI := (finiteType_chartAlgFin_and_chartAlgInf A L (↥K₀) j₀ htj₀ hFD₀ hsep₀).1
    exact Algebra.FiniteType.isNoetherianRing A _

  have hιj : ι (jChartFin A (↥K₀) j₀) = jChartFin A (↥K) j := by
    apply Subtype.ext
    rw [hι]
    apply Subtype.ext
    show ((jChartFin A (↥K₀) j₀ : ↥K₀) : LaurentSeries L) = ((jChartFin A (↥K) j : ↥K) : LaurentSeries L)
    rw [coe_jChartFin, coe_jChartFin, hj₀, hj]
  haveI : IsScalarTower A ↥(chartAlgFin A (↥K₀) j₀) ↥(chartAlgFin A (↥K) j) := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    symm
    apply Subtype.ext
    show ((ι (algebraMap A ↥(chartAlgFin A (↥K₀) j₀) a) : ↥(chartAlgFin A (↥K) j)) : ↥K) = (algebraMap A ↥(chartAlgFin A (↥K) j) a : ↥K)
    rw [hι]
    apply Subtype.ext
    show ((algebraMap A ↥K₀ a : ↥K₀) : LaurentSeries L) = ((algebraMap A ↥K a : ↥K) : LaurentSeries L)
    rw [IsScalarTower.algebraMap_apply A L ↥K₀, IsScalarTower.algebraMap_apply A L ↥K]
    rfl
  haveI : Module.Finite ↥(chartAlgFin A (↥K₀) j₀) ↥(chartAlgFin A (↥K) j) := by
    letI algP : Algebra (Polynomial A) ↥(chartAlgFin A (↥K) j) := (polynomialToChartFin A (↥K) j).toRingHom.toAlgebra
    letI algP₀ : Algebra (Polynomial A) ↥(chartAlgFin A (↥K₀) j₀) := (polynomialToChartFin A (↥K₀) j₀).toRingHom.toAlgebra
    haveI hfinP : Module.Finite (Polynomial A) ↥(chartAlgFin A (↥K) j) :=
      (finite_polynomial_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD hsep).1
    have hcomp : ι.comp (polynomialToChartFin A (↥K₀) j₀).toRingHom = (polynomialToChartFin A (↥K) j).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro a
        show ι (polynomialToChartFin A (↥K₀) j₀ (Polynomial.C a)) = polynomialToChartFin A (↥K) j (Polynomial.C a)
        rw [Polynomial.C_eq_algebraMap, AlgHom.commutes, AlgHom.commutes]
        exact (IsScalarTower.algebraMap_apply A ↥(chartAlgFin A (↥K₀) j₀) ↥(chartAlgFin A (↥K) j) a).symm
      · show ι (polynomialToChartFin A (↥K₀) j₀ Polynomial.X) = polynomialToChartFin A (↥K) j Polynomial.X
        rw [polynomialToChartFin_X, polynomialToChartFin_X, hιj]
    haveI : IsScalarTower (Polynomial A) ↥(chartAlgFin A (↥K₀) j₀) ↥(chartAlgFin A (↥K) j) := by
      apply IsScalarTower.of_algebraMap_eq
      intro p
      show polynomialToChartFin A (↥K) j p = ι (polynomialToChartFin A (↥K₀) j₀ p)
      exact (congrArg (fun g : Polynomial A →+* ↥(chartAlgFin A (↥K) j) => g p) hcomp).symm
    exact Module.Finite.of_restrictScalars_finite (Polynomial A) _ _
  have hιK : ∀ x : ↥(chartAlgFin A (↥K₀) j₀),
      algebraMap ↥(chartAlgFin A (↥K) j) ↥K (algebraMap ↥(chartAlgFin A (↥K₀) j₀) ↥(chartAlgFin A (↥K) j) x) =
        φK (algebraMap ↥(chartAlgFin A (↥K₀) j₀) ↥K₀ x) := fun x => hι x
  have hint : φK.toRingHom.IsIntegral := by

    set R : IntermediateField L ↥K := IntermediateField.map φK ⊤ with hRdef
    have hjR : j ∈ R := by
      rw [hRdef, IntermediateField.mem_map]
      refine ⟨j₀, IntermediateField.mem_top, ?_⟩
      apply Subtype.ext
      show ((j₀ : ↥K₀) : LaurentSeries L) = ((j : ↥K) : LaurentSeries L)
      rw [hj₀, hj]
    have hER : IntermediateField.adjoin L ({j} : Set ↥K) ≤ R := IntermediateField.adjoin_le_iff.mpr (by
      intro x hx; rw [Set.mem_singleton_iff.mp hx]; exact hjR)

    letI algER : Algebra ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥R := (IntermediateField.inclusion hER).toRingHom.toAlgebra
    haveI : IsScalarTower ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥R ↥K := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    haveI hAlgR : Algebra.IsAlgebraic ↥R ↥K := Algebra.IsAlgebraic.tower_top (K := ↥(IntermediateField.adjoin L ({j} : Set ↥K))) ↥R
    have hRint : (R.val.toRingHom : ↥R →+* ↥K).IsIntegral := fun x => (Algebra.IsIntegral.isIntegral (R := ↥R) x)

    let e : ↥K₀ ≃ₐ[L] ↥R := (IntermediateField.topEquiv).symm.trans (IntermediateField.equivMap ⊤ φK)
    have hcompφ : φK.toRingHom = (R.val.toRingHom : ↥R →+* ↥K).comp e.toAlgHom.toRingHom := by
      ext x; rfl
    rw [hcompφ]
    exact RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ e.surjective) hRint

  have he : ∀ w : AlgebraicCurve.Place L ↥K, (∀ r : ↥(chartAlgFin A (↥K) j), 0 ≤ w.ord (algebraMap _ ↥K r)) →
      (∀ r : ↥(chartAlgFin A (↥K) j), r ≠ 0 → (0 < w.ord (algebraMap _ ↥K r) ↔ r ∈ 𝔔)) →
      AlgebraicCurve.Place.ramificationIndexAlong φK w = 1 := by
    intro w hw0 hw1
    have hjne : jChartFin A (↥K) j ≠ 0 := fun h => hjQ (h ▸ 𝔔.zero_mem)
    have hj1728ne : jChartFin A (↥K) j - 1728 ≠ 0 := fun h => hj1728Q (h ▸ 𝔔.zero_mem)
    have hord0 : w.ord j = 0 := by
      have h1 := hw0 (jChartFin A (↥K) j)
      have h2 := (hw1 _ hjne).not.mpr hjQ
      have h3 : algebraMap ↥(chartAlgFin A (↥K) j) ↥K (jChartFin A (↥K) j) = j := rfl
      rw [h3] at h1 h2
      omega
    have hord1728 : w.ord (j - 1728) = 0 := by
      have h1 := hw0 (jChartFin A (↥K) j - 1728)
      have h2 := (hw1 _ hj1728ne).not.mpr hj1728Q
      have h3 : algebraMap ↥(chartAlgFin A (↥K) j) ↥K (jChartFin A (↥K) j - 1728) = j - 1728 := by
        rw [map_sub]; rfl
      rw [h3] at h1 h2
      omega
    rw [hφKdef]
    exact ModularCurve.FullLevel.ramificationIndexAlong_inclusion_eq_one_of_ord_eq_zero_of_ord_sub_eq_zero_xH_levelH
      q hq M' hqM' L K hK K₀ hK₀ hle₀ j hj w hord0 hord1728
  exact Algebra.isUnramifiedAt_of_height_eq_one_of_not_mem_of_ramificationIndexAlong_eq_one_of_centre
    L A ↥K ↥K₀ φK ↥(chartAlgFin A (↥K) j) ↥(chartAlgFin A (↥K₀) j₀) hιK hint 𝔔 hQ1 he ϖ hϖ hϖQ

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))

    [Algebra.IsAlgebraic ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hmax : y.asIdeal.IsMaximal)
    (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
    (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω)
    (hφ : RingHom.ker φ = y.asIdeal)
    (hord : φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∉ ModularCurve.ssJSet q Ω)
    (hz₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y.asIdeal)

    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (hle₀ : K₀ ≤ K)
    [Algebra A ↥K₀] [IsScalarTower A L ↥K₀]
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₀ ≠ 0)]
    (ι : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
    (hι : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀), ((ι b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = IntermediateField.inclusion hle₀ (b : ↥K₀))
    (hell : φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) = 0 ∨ φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) = 1728) :
    letI : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := ι.toAlgebra
    ∃ 𝔔₀ : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀), 𝔔₀.IsPrime ∧ 𝔔₀ ≤ (y.asIdeal).comap ι ∧
      algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ϖ ∉ 𝔔₀ ∧
      (∀ (O : Type) [CommRing O] [IsLocalRing O] [Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) O]
        [IsLocalization.AtPrime O ((y.asIdeal).comap ι)],
        Ideal.map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) O) 𝔔₀ ⊔ Ideal.span {algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) O (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ϖ)} = IsLocalRing.maximalIdeal O) ∧
      ∀ (𝔔 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) [𝔔.IsPrime], 𝔔 ≤ y.asIdeal → 𝔔.height = 1 →
        algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∉ 𝔔 → 𝔔.comap ι ≠ 𝔔₀ → Algebra.IsUnramifiedAt ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) 𝔔 := by
  classical
  letI algBB : Algebra ↥(chartAlgFin A (↥K₀) j₀) ↥(chartAlgFin A (↥K) j) := ι.toAlgebra
  have halg : ∀ x, algebraMap ↥(chartAlgFin A (↥K₀) j₀) ↥(chartAlgFin A (↥K) j) x = ι x := fun _ => rfl
  haveI : y.asIdeal.IsPrime := y.isPrime

  obtain ⟨c, hc, hφc⟩ : ∃ c : ℕ, (c = 0 ∨ c = 1728) ∧ φ (jChartFin A (↥K) j) = (c : Ω) := by
    rcases hell with h | h
    · exact ⟨0, Or.inl rfl, by rw [h, Nat.cast_zero]⟩
    · exact ⟨1728, Or.inr rfl, by rw [h, Nat.cast_ofNat]⟩

  have hιϖ : ι (algebraMap A ↥(chartAlgFin A (↥K₀) j₀) ϖ) = algebraMap A ↥(chartAlgFin A (↥K) j) ϖ := by
    apply Subtype.ext
    rw [hι]
    apply Subtype.ext
    show ((algebraMap A ↥K₀ ϖ : ↥K₀) : LaurentSeries L) = ((algebraMap A ↥K ϖ : ↥K) : LaurentSeries L)
    rw [IsScalarTower.algebraMap_apply A L ↥K₀, IsScalarTower.algebraMap_apply A L ↥K]
    rfl
  have hιj : ι (jChartFin A (↥K₀) j₀) = jChartFin A (↥K) j := by
    apply Subtype.ext
    rw [hι]
    apply Subtype.ext
    show ((jChartFin A (↥K₀) j₀ : ↥K₀) : LaurentSeries L) = ((jChartFin A (↥K) j : ↥K) : LaurentSeries L)
    rw [coe_jChartFin, coe_jChartFin, hj₀, hj]

  have hϖW : ((algebraMap A ↥(chartAlgFin A (↥K) j) ϖ : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ W₀.nonunits := by
    obtain ⟨W, hW, -, hWm, -, -⟩ :=
      ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
        (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) L K (by rw [hK]; rfl) A j hj
    have hWW : W = W₀ := by
      ext f
      rw [hW, hW₀]
    rw [← hWW]
    have hcoeϖ : ((algebraMap A ↥(chartAlgFin A (↥K) j) ϖ : ↥(chartAlgFin A (↥K) j)) : ↥K) = algebraMap A ↥K ϖ :=
      (IsScalarTower.algebraMap_apply A ↥(chartAlgFin A (↥K) j) ↥K ϖ).symm
    rw [hcoeϖ]
    exact hWm ϖ (by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ)
  have hϖy : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y.asIdeal := hz₀ _ hϖW
  have hϖx₀ : algebraMap A ↥(chartAlgFin A (↥K₀) j₀) ϖ ∈ y.asIdeal.comap ι := by
    rw [Ideal.mem_comap, hιϖ]
    exact hϖy
  have hjy : jChartFin A (↥K) j - (c : ↥(chartAlgFin A (↥K) j)) ∈ y.asIdeal := by
    rw [← hφ, RingHom.mem_ker, map_sub, hφc, map_natCast, sub_self]
  have hjx₀ : jChartFin A (↥K₀) j₀ - (c : ↥(chartAlgFin A (↥K₀) j₀)) ∈ y.asIdeal.comap ι := by
    rw [Ideal.mem_comap, map_sub, hιj, map_natCast]
    exact hjy

  haveI hx₀ : (y.asIdeal.comap ι).IsPrime := Ideal.comap_isPrime ι _
  obtain ⟨𝔔₀, hQ₀prime, hQ₀le, hQ₀j, hQ₀ϖ, hQ₀trans, hQ₀uniq⟩ :=
    ModularCurve.FullLevel.existsUnique_prime_le_jChartFin_sub_mem_map_sup_span_eq_maximalIdeal_chartAlgFin_gamma0_of_not_dvd
      q hq M' hqM' L K₀ hK₀ A hAq j₀ hj₀ ϖ hϖ c hc (y.asIdeal.comap ι) hϖx₀ hjx₀
  refine ⟨𝔔₀, hQ₀prime, hQ₀le, hQ₀ϖ, hQ₀trans, ?_⟩

  intro 𝔔 _inst h𝔔y hQ1 hϖQ hne
  have h1728 : ((1728 : ℕ) : Ω) ≠ 0 := by
    intro h0
    have hdvd : q ∣ 2 ^ 6 * 3 ^ 3 := by
      have := (CharP.cast_eq_zero_iff Ω q 1728).mp h0
      norm_num
      exact this
    have hqp : q.Prime := Fact.out
    rcases (Nat.Prime.dvd_mul hqp).mp hdvd with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) (Nat.Prime.dvd_of_dvd_pow hqp h2); omega
    · have := Nat.le_of_dvd (by norm_num) (Nat.Prime.dvd_of_dvd_pow hqp h3); omega
  have hguard : ∀ c' : ℕ, (c' = 0 ∨ c' = 1728) → jChartFin A (↥K) j - (c' : ↥(chartAlgFin A (↥K) j)) ∉ 𝔔 := by
    intro c' hc' hmem
    have hcc' : (c : Ω) = (c' : Ω) := by
      have hy' := h𝔔y hmem
      rw [← hφ, RingHom.mem_ker, map_sub, map_natCast, hφc, sub_eq_zero] at hy'
      exact hy'
    have hc_eq : c' = c := by
      rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl
      · rfl
      · exact absurd hcc'.symm (by rw [Nat.cast_zero]; exact h1728)
      · exact absurd hcc' (by rw [Nat.cast_zero]; exact h1728)
      · rfl
    subst hc_eq
    apply hne
    apply hQ₀uniq (𝔔.comap ι) (Ideal.comap_isPrime ι _) (Ideal.comap_mono h𝔔y)
    · rw [Ideal.mem_comap, map_sub, hιj, map_natCast]
      exact hmem
    · rw [Ideal.mem_comap, hιϖ]
      exact hϖQ
  have hjQ : jChartFin A (↥K) j ∉ 𝔔 := by
    have h := hguard 0 (Or.inl rfl)
    rwa [Nat.cast_zero, sub_zero] at h
  have hj1728Q : jChartFin A (↥K) j - 1728 ∉ 𝔔 := by
    have h := hguard 1728 (Or.inr rfl)
    rwa [Nat.cast_ofNat] at h
  exact E149ELL.isUnramifiedAt_of_jChartFin_not_mem q hq M' hqM' L K hK A j hj ϖ hϖ K₀ hK₀ hle₀ j₀ hj₀ ι hι
    𝔔 hQ1 hϖQ hjQ hj1728Q

end S_ModularCurve_FullLevel_exists_prime_map_sup_span_eq_maximalIdeal_and_isUnramifiedAt_of_map_jChartFin_mem_xH_of_isAlgebraic
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_prime_map_sup_span_eq_maximalIdeal_and_isUnramifiedAt_of_map_jChartFin_mem_xH_of_isAlgebraic (solution)
