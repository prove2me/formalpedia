-- Prove2me | solution 1 for ModularCurve.FullLevel.existsUnique_prime_le_jChartFin_sub_mem_map_sup_span_eq_maximalIdeal_chartAlgFin_gamma0_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/6cc42371-cd43-5c65-ba20-b1020be68858

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_Algebra_existsUnique_prime_le_map_sup_span_eq_maximalIdeal_of_isUnramifiedAt_of_isDedekindDomain_quotient
import Theorems.Thm_ModularCurve_isUnramifiedAt_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_jChartFin_not_mem
import Theorems.Thm_ModularCurve_isUnramifiedAt_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_mem_of_not_dvd
import Theorems.Thm_ModularCurve_FullLevel_isDedekindDomain_chartAlgFin_quotient_span_algebraMap_gamma0_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_existsUnique_prime_le_jChartFin_sub_mem_map_sup_span_eq_maximalIdeal_chartAlgFin_gamma0_of_not_dvd
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.FullLevel.instAddCommGroupJac ModularCurve.FullLevel.instFintypeIdx ModularCurve.FullLevel.instMulActionAlgEquivRatAlgebraicClosureIdx ModularCurve.FullLevel.instDecidableEqIdx CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instIsElliptic_tateBase ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.FullLevel.coe_diagOneElem ModularCurve.FullLevel.Jac.eval_neg ModularCurve.FullLevel.Jac.eval_zsmul ModularCurve.FullLevel.Jac.mapIdx_eval ModularCurve.FullLevel.Idx.val_pow ModularCurve.FullLevel.Idx.val_mk ModularCurve.FullLevel.Idx.val_smul"
p2m_attr_erase "simp" "ModularCurve.FullLevel.diagJac_eval ModularCurve.FullLevel.Jac.eval_add ModularCurve.FullLevel.Jac.eval_nsmul ModularCurve.FullLevel.Jac.eval_sub ModularCurve.FullLevel.slJac_eval ModularCurve.FullLevel.Jac.eval_zero ModularCurve.FullLevel.Jac.eval_mk ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord RegularLocalRingQuotientAscent.dualNumberFst_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆"
p2m_attr_erase "simp" "ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

namespace CMLocusAux

p2m_open "Polynomial AlgebraicGeometry.Polynomial IsLocalRing AlgebraicCurve.TwoChartIntegralModel"

section RegularBase

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

theorem comap_evalRingHom_maximalIdeal_eq_span (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ}) (c : A) :
    (maximalIdeal A).comap (evalRingHom c) = Ideal.span {C ϖ, X - C c} := by
  apply le_antisymm
  · intro p hp
    rw [Ideal.mem_comap, coe_evalRingHom, hϖ, Ideal.mem_span_singleton] at hp
    obtain ⟨a, ha⟩ := hp
    obtain ⟨r, hr⟩ := X_sub_C_dvd_sub_C_eval (a := c) (p := p)
    have hp' : p = (X - C c) * r + C a * C ϖ := by
      rw [← hr, ha, C_mul]; ring
    rw [hp']
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ?_)) (Ideal.mul_mem_left _ _ (Ideal.subset_span ?_))
    · simp
    · simp
  · rw [Ideal.span_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [SetLike.mem_coe, Ideal.mem_comap, coe_evalRingHom, eval_C, hϖ]
      exact Ideal.mem_span_singleton_self ϖ
    · rw [SetLike.mem_coe, Ideal.mem_comap, coe_evalRingHom, eval_sub, eval_X, eval_C, sub_self]
      exact Ideal.zero_mem _

theorem isMaximal_span_pair (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ}) (c : A) :
    (Ideal.span {C ϖ, X - C c} : Ideal (Polynomial A)).IsMaximal := by
  rw [← comap_evalRingHom_maximalIdeal_eq_span ϖ hϖ c]
  exact Ideal.comap_isMaximal_of_surjective (evalRingHom c) (fun a => ⟨C a, eval_C⟩)

omit [IsDiscreteValuationRing A] in
theorem C_not_mem_span_X_sub_C {a : A} (ha : a ≠ 0) (c : A) : (C a : Polynomial A) ∉ Ideal.span {X - C c} := by
  intro h
  rw [Ideal.mem_span_singleton] at h
  have hdeg := natDegree_le_of_dvd h (C_ne_zero.mpr ha)
  rw [natDegree_X_sub_C, natDegree_C] at hdeg
  exact Nat.not_succ_le_zero 0 hdeg

theorem height_span_pair (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ}) (c : A) :
    (Ideal.span {C ϖ, X - C c} : Ideal (Polynomial A)).height = 2 := by
  haveI hmax := isMaximal_span_pair ϖ hϖ c
  have hϖ0 : ϖ ≠ 0 := by
    intro h; apply IsDiscreteValuationRing.not_a_field A; rw [hϖ, h, Ideal.span_singleton_eq_bot]
  have hnf : ¬ IsField A := fun hF => IsDiscreteValuationRing.not_a_field A
    ((IsLocalRing.isField_iff_maximalIdeal_eq).mp hF)

  have hdimA : ringKrullDim A = 1 := IsPrincipalIdealRing.ringKrullDim_eq_one A hnf
  have hdimAX : ringKrullDim (Polynomial A) = 2 := by
    rw [Polynomial.ringKrullDim_of_isNoetherianRing, hdimA]; rfl
  have hup : ((Ideal.span {C ϖ, X - C c} : Ideal (Polynomial A)).height : WithBot ℕ∞) ≤ 2 := by
    rw [← hdimAX]; exact Ideal.height_le_ringKrullDim_of_ne_top hmax.ne_top

  haveI hp1 : (Ideal.span {X - C c} : Ideal (Polynomial A)).IsPrime :=
    (Ideal.span_singleton_prime (prime_X_sub_C c).ne_zero).mpr (prime_X_sub_C c)
  have h01 : (⊥ : Ideal (Polynomial A)) < Ideal.span {X - C c} := by
    rw [bot_lt_iff_ne_bot, Ne, Ideal.span_singleton_eq_bot]; exact X_sub_C_ne_zero c
  have h12 : (Ideal.span {X - C c} : Ideal (Polynomial A)) < Ideal.span {C ϖ, X - C c} := by
    refine lt_of_le_of_ne (Ideal.span_mono (by simp)) ?_
    intro h
    have : (C ϖ : Polynomial A) ∈ Ideal.span {X - C c} := by rw [h]; exact Ideal.subset_span (by simp)
    exact C_not_mem_span_X_sub_C hϖ0 c this
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime h01
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime h12
  rw [Ideal.height_bot, zero_add] at h1
  have hlow : (2 : ℕ∞) ≤ (Ideal.span {C ϖ, X - C c} : Ideal (Polynomial A)).height := by
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ (Ideal.span {X - C c} : Ideal (Polynomial A)).height + 1 := by gcongr
      _ ≤ _ := h2
  have hup' : (Ideal.span {C ϖ, X - C c} : Ideal (Polynomial A)).height ≤ 2 := by
    have h2 : (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := rfl
    rw [h2] at hup
    exact WithBot.coe_le_coe.mp hup
  exact le_antisymm hup' hlow

theorem isRegularLocalRing_localization_atPrime_span_pair (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ}) (c : A)
    (𝔪 : Ideal (Polynomial A)) [𝔪.IsPrime] (h𝔪 : 𝔪 = Ideal.span {C ϖ, X - C c}) :
    IsRegularLocalRing (Localization.AtPrime 𝔪) ∧ ringKrullDim (Localization.AtPrime 𝔪) = 2 := by
  subst h𝔪
  have hdim : ringKrullDim (Localization.AtPrime (Ideal.span {C ϖ, X - C c} : Ideal (Polynomial A))) = 2 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height (Ideal.span {C ϖ, X - C c} : Ideal (Polynomial A))
      (Localization.AtPrime (Ideal.span {C ϖ, X - C c} : Ideal (Polynomial A))), height_span_pair ϖ hϖ c]
    rfl
  refine ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_, hdim⟩
  rw [hdim, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  set f := algebraMap (Polynomial A) (Localization.AtPrime (Ideal.span {C ϖ, X - C c} : Ideal (Polynomial A))) with hf
  have h := Submodule.spanFinrank_span_le_ncard_of_finite (R := (Localization.AtPrime (Ideal.span {C ϖ, X - C c} : Ideal (Polynomial A)))) (M := (Localization.AtPrime (Ideal.span {C ϖ, X - C c} : Ideal (Polynomial A)))) (Set.toFinite ({f (C ϖ), f (X - C c)} : Set (Localization.AtPrime (Ideal.span {C ϖ, X - C c} : Ideal (Polynomial A)))))
  have h2 : ({f (C ϖ), f (X - C c)} : Set (Localization.AtPrime (Ideal.span {C ϖ, X - C c} : Ideal (Polynomial A)))).ncard ≤ 2 :=
    (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  exact_mod_cast h.trans h2

end RegularBase

section Modular

theorem under_eq_span_pair_of_mem
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {B : Type*} [CommRing B] [Algebra (Polynomial A) B]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ}) (c : A)
    (x₀ : Ideal B) [x₀.IsPrime]
    (hϖx₀ : algebraMap (Polynomial A) B (C ϖ) ∈ x₀) (hjx₀ : algebraMap (Polynomial A) B (X - C c) ∈ x₀) :
    x₀.under (Polynomial A) = Ideal.span {C ϖ, X - C c} := by
  haveI := isMaximal_span_pair ϖ hϖ c
  symm
  refine Ideal.IsMaximal.eq_of_le this (Ideal.IsPrime.ne_top inferInstance) ?_
  rw [Ideal.span_le]
  rintro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact hϖx₀
  · exact hjx₀

end Modular

end CMLocusAux

namespace CMLocusAsm

p2m_open "Polynomial AlgebraicGeometry.Polynomial IsLocalRing AlgebraicCurve.TwoChartIntegralModel"

theorem coprime_1728 (q : ℕ) (hp : q.Prime) (hq : 5 ≤ q) : Nat.Coprime 1728 q := by
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro h
  have h' : q ∣ 2 ^ 6 * 3 ^ 3 := by norm_num; exact h
  rcases (hp.dvd_mul).mp h' with h2 | h3
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2); omega
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3); omega

theorem ofNat_1728_not_mem_maximalIdeal (q : ℕ) (hp : q.Prime) (hq : 5 ≤ q)
    (A : Type*) [CommRing A] [IsLocalRing A] (hAq : (q : A) ∈ maximalIdeal A) :
    (1728 : A) ∉ maximalIdeal A := by
  intro h
  have hc : IsCoprime ((1728 : ℕ) : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr (coprime_1728 q hp hq)
  have hc' : IsCoprime ((1728 : ℕ) : A) (q : A) := by
    have := hc.map (Int.castRingHom A)
    simpa using this
  obtain ⟨a, b, hab⟩ := hc'
  apply (maximalIdeal.isMaximal A).ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ hAq)
  exact_mod_cast h

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem main
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L]
    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K₀] [IsScalarTower A L ↥K₀]
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₀ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (c : ℕ) (hc : c = 0 ∨ c = 1728)
    (x₀ : Ideal ↥(chartAlgFin A (↥K₀) j₀)) [x₀.IsPrime]
    (hϖx₀ : algebraMap A ↥(chartAlgFin A (↥K₀) j₀) ϖ ∈ x₀)
    (hjx₀ : jChartFin A (↥K₀) j₀ - (c : ↥(chartAlgFin A (↥K₀) j₀)) ∈ x₀) :
    ∃ 𝔔₀ : Ideal ↥(chartAlgFin A (↥K₀) j₀), 𝔔₀.IsPrime ∧ 𝔔₀ ≤ x₀ ∧
      jChartFin A (↥K₀) j₀ - (c : ↥(chartAlgFin A (↥K₀) j₀)) ∈ 𝔔₀ ∧
      algebraMap A ↥(chartAlgFin A (↥K₀) j₀) ϖ ∉ 𝔔₀ ∧
      (∀ (O : Type) [CommRing O] [IsLocalRing O] [Algebra ↥(chartAlgFin A (↥K₀) j₀) O] [IsLocalization.AtPrime O x₀],
        Ideal.map (algebraMap ↥(chartAlgFin A (↥K₀) j₀) O) 𝔔₀ ⊔ Ideal.span {algebraMap ↥(chartAlgFin A (↥K₀) j₀) O (algebraMap A ↥(chartAlgFin A (↥K₀) j₀) ϖ)}
          = IsLocalRing.maximalIdeal O) ∧
      ∀ 𝔔 : Ideal ↥(chartAlgFin A (↥K₀) j₀), 𝔔.IsPrime → 𝔔 ≤ x₀ →
        jChartFin A (↥K₀) j₀ - (c : ↥(chartAlgFin A (↥K₀) j₀)) ∈ 𝔔 → algebraMap A ↥(chartAlgFin A (↥K₀) j₀) ϖ ∉ 𝔔 → 𝔔 = 𝔔₀ := by
  classical

  have hT₀ : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 M' := by
    rw [← CohCarrier.GammaH_top]; exact ModularCurve.translation_mem_GammaH _ _
  haveI hFD₀ : FiniteDimensional ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma0 M') hT₀ L K₀ hK₀ j₀ hj₀
  haveI hAlg₀ : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ := Algebra.IsAlgebraic.of_finite _ _
  haveI hsep₀ : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have htj₀ : Transcendental A j₀ := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₀ A j₀ hj₀
  letI algP₀ : Algebra (Polynomial A) ↥(chartAlgFin A (↥K₀) j₀) := (polynomialToChartFin A (↥K₀) j₀).toRingHom.toAlgebra
  haveI hfinP : Module.Finite (Polynomial A) ↥(chartAlgFin A (↥K₀) j₀) :=
    (finite_polynomial_chartAlgFin_and_chartAlgInf A L (↥K₀) j₀ htj₀ hFD₀ hsep₀).1
  haveI : Algebra.IsIntegral (Polynomial A) ↥(chartAlgFin A (↥K₀) j₀) := Algebra.IsIntegral.of_finite _ _
  have hinj : Function.Injective (algebraMap (Polynomial A) ↥(chartAlgFin A (↥K₀) j₀)) := by
    intro p₁ p₂ h
    have hinj' : Function.Injective (Polynomial.aeval (R := A) j₀) := transcendental_iff_injective.mp htj₀
    apply hinj'
    have key : ∀ p : Polynomial A, Polynomial.aeval (R := A) j₀ p =
        ((chartAlgFin A (↥K₀) j₀).val (polynomialToChartFin A (↥K₀) j₀ p)) := by
      intro p
      rw [polynomialToChartFin, ← Polynomial.aeval_algHom_apply]
      rfl
    rw [key, key]
    exact congrArg _ h
  haveI : FaithfulSMul (Polynomial A) ↥(chartAlgFin A (↥K₀) j₀) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : IsIntegrallyClosed ↥(chartAlgFin A (↥K₀) j₀) := isIntegrallyClosed_chartAlg A (↥K₀) _
  haveI hfrB : IsFractionRing ↥(chartAlgFin A (↥K₀) j₀) ↥K₀ := isFractionRing_chartAlg A L (↥K₀) _

  have eϖ : algebraMap (Polynomial A) ↥(chartAlgFin A (↥K₀) j₀) (C ϖ) = algebraMap A ↥(chartAlgFin A (↥K₀) j₀) ϖ := by
    show polynomialToChartFin A (↥K₀) j₀ (C ϖ) = _
    rw [Polynomial.C_eq_algebraMap, AlgHom.commutes]
  have et : algebraMap (Polynomial A) ↥(chartAlgFin A (↥K₀) j₀) (X - C (c : A)) = jChartFin A (↥K₀) j₀ - (c : ↥(chartAlgFin A (↥K₀) j₀)) := by
    show polynomialToChartFin A (↥K₀) j₀ (X - C (c : A)) = _
    rw [map_sub, polynomialToChartFin_X, Polynomial.C_eq_algebraMap, AlgHom.commutes, map_natCast]

  have hϖx₀' : algebraMap (Polynomial A) ↥(chartAlgFin A (↥K₀) j₀) (C ϖ) ∈ x₀ := by rw [eϖ]; exact hϖx₀
  have hjx₀' : algebraMap (Polynomial A) ↥(chartAlgFin A (↥K₀) j₀) (X - C (c : A)) ∈ x₀ := by rw [et]; exact hjx₀
  have hmax : x₀.comap (algebraMap (Polynomial A) ↥(chartAlgFin A (↥K₀) j₀)) = Ideal.span {C ϖ, X - C (c : A)} :=
    CMLocusAux.under_eq_span_pair_of_mem ϖ hϖ (c : A) x₀ hϖx₀' hjx₀'
  haveI hmaxP : (x₀.comap (algebraMap (Polynomial A) ↥(chartAlgFin A (↥K₀) j₀))).IsMaximal := by
    rw [hmax]; exact CMLocusAux.isMaximal_span_pair ϖ hϖ (c : A)
  haveI hx₀max : x₀.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap x₀ hmaxP
  obtain ⟨hreg, hdim⟩ := CMLocusAux.isRegularLocalRing_localization_atPrime_span_pair ϖ hϖ (c : A)
    (x₀.comap (algebraMap (Polynomial A) ↥(chartAlgFin A (↥K₀) j₀))) hmax

  have htp : (Ideal.span ({X - C (c : A)} : Set (Polynomial A))).IsPrime :=
    (Ideal.span_singleton_prime (prime_X_sub_C (c : A)).ne_zero).mpr (prime_X_sub_C (c : A))
  haveI : CharZero A := (algebraMap A L).charZero
  haveI hchar : CharZero (Polynomial A ⧸ Ideal.span ({X - C (c : A)} : Set (Polynomial A))) :=
    ((Polynomial.quotientSpanXSubCAlgEquiv (c : A)) : (Polynomial A ⧸ Ideal.span ({X - C (c : A)} : Set (Polynomial A))) →+* A).charZero

  letI algPK : Algebra (Polynomial A) ↥K₀ := ((algebraMap ↥(chartAlgFin A (↥K₀) j₀) ↥K₀).comp (algebraMap (Polynomial A) ↥(chartAlgFin A (↥K₀) j₀))).toAlgebra
  haveI towPBK : IsScalarTower (Polynomial A) ↥(chartAlgFin A (↥K₀) j₀) ↥K₀ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hinjPK : Function.Injective (algebraMap (Polynomial A) ↥K₀) := by
    rw [IsScalarTower.algebraMap_eq (Polynomial A) ↥(chartAlgFin A (↥K₀) j₀) ↥K₀]
    exact (IsFractionRing.injective ↥(chartAlgFin A (↥K₀) j₀) ↥K₀).comp hinj
  haveI : FaithfulSMul (Polynomial A) ↥K₀ := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinjPK
  letI algFK : Algebra (FractionRing (Polynomial A)) ↥K₀ := FractionRing.liftAlgebra (Polynomial A) ↥K₀
  haveI : IsScalarTower (Polynomial A) (FractionRing (Polynomial A)) ↥K₀ := FractionRing.isScalarTower_liftAlgebra _ _
  haveI : Algebra.IsAlgebraic (Polynomial A) ↥K₀ :=
    (IsFractionRing.isAlgebraic_iff' (Polynomial A) ↥(chartAlgFin A (↥K₀) j₀) ↥K₀).mp inferInstance
  haveI : Algebra.IsAlgebraic (FractionRing (Polynomial A)) ↥K₀ :=
    Algebra.IsAlgebraic.extendScalars (R := Polynomial A) (IsFractionRing.injective (Polynomial A) (FractionRing (Polynomial A)))
  haveI : CharZero (FractionRing (Polynomial A)) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (Polynomial A) (FractionRing (Polynomial A)))
  haveI : Algebra.IsSeparable (FractionRing (Polynomial A)) ↥K₀ := Algebra.IsAlgebraic.isSeparable_of_perfectField

  have hfib : IsDedekindDomain (↥(chartAlgFin A (↥K₀) j₀) ⧸ Ideal.span ({algebraMap (Polynomial A) ↥(chartAlgFin A (↥K₀) j₀) (C ϖ)} : Set ↥(chartAlgFin A (↥K₀) j₀))) := by
    rw [eϖ]
    exact ModularCurve.FullLevel.isDedekindDomain_chartAlgFin_quotient_span_algebraMap_gamma0_of_not_dvd
      q hq M' hqM' L K₀ hK₀ A hAq j₀ hj₀ ϖ hϖ

  have h1728 : (1728 : ↥(chartAlgFin A (↥K₀) j₀)) ∉ x₀ := by
    intro h
    have h' : (1728 : A) ∈ x₀.comap (algebraMap A ↥(chartAlgFin A (↥K₀) j₀)) := by
      rw [Ideal.mem_comap, map_ofNat]; exact h
    have hne : x₀.comap (algebraMap A ↥(chartAlgFin A (↥K₀) j₀)) ≠ ⊤ := Ideal.comap_ne_top _ (Ideal.IsPrime.ne_top inferInstance)
    exact ofNat_1728_not_mem_maximalIdeal q (Fact.out) hq A hAq (IsLocalRing.le_maximalIdeal hne h')
  have hunr : ∀ (Q : Ideal ↥(chartAlgFin A (↥K₀) j₀)) [Q.IsPrime], Q ≤ x₀ → Q.height = 1 →
      algebraMap (Polynomial A) ↥(chartAlgFin A (↥K₀) j₀) (X - C (c : A)) ∉ Q → Algebra.IsUnramifiedAt (Polynomial A) Q := by
    intro Q _ hQle hQ1 htQ
    rw [et] at htQ
    by_cases hϖQ : algebraMap A ↥(chartAlgFin A (↥K₀) j₀) ϖ ∈ Q
    · exact ModularCurve.isUnramifiedAt_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_mem_of_not_dvd
        q M' hqM' L K₀ hK₀ A hAq j₀ hj₀ ϖ hϖ Q hQ1 hϖQ
    · have hj : jChartFin A (↥K₀) j₀ ∉ Q ∧ jChartFin A (↥K₀) j₀ - 1728 ∉ Q := by
        rcases hc with rfl | rfl
        · have e0 : jChartFin A (↥K₀) j₀ - ((0 : ℕ) : ↥(chartAlgFin A (↥K₀) j₀)) = jChartFin A (↥K₀) j₀ := by
            rw [Nat.cast_zero, sub_zero]
          rw [e0] at htQ hjx₀
          refine ⟨htQ, fun h => h1728 ?_⟩
          have := x₀.sub_mem hjx₀ (hQle h)
          rwa [sub_sub_cancel] at this
        · have e1 : ((1728 : ℕ) : ↥(chartAlgFin A (↥K₀) j₀)) = 1728 := by norm_cast
          rw [e1] at htQ hjx₀
          refine ⟨fun h => h1728 ?_, htQ⟩
          have := x₀.sub_mem (hQle h) hjx₀
          rwa [sub_sub_cancel] at this
      exact ModularCurve.isUnramifiedAt_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_jChartFin_not_mem
        M' L K₀ hK₀ A j₀ hj₀ ϖ hϖ Q hQ1 hϖQ hj.1 hj.2

  obtain ⟨𝔔, h𝔔p, h𝔔le, ht𝔔, hϖ𝔔, htrans, huniq⟩ :=
    Algebra.existsUnique_prime_le_map_sup_span_eq_maximalIdeal_of_isUnramifiedAt_of_isDedekindDomain_quotient
      (Polynomial A) (FractionRing (Polynomial A)) ↥(chartAlgFin A (↥K₀) j₀) ↥K₀ (C ϖ) (X - C (c : A)) htp hfib x₀ hmax hreg hdim hunr
  refine ⟨𝔔, h𝔔p, h𝔔le, ?_, ?_, ?_, ?_⟩
  · rw [← et]; exact ht𝔔
  · rw [← eϖ]; exact hϖ𝔔
  · intro O _ _ _ _
    have := htrans O
    rwa [eϖ] at this
  · intro 𝔔' h𝔔'p h𝔔'le ht' hϖ'
    exact huniq 𝔔' h𝔔'p h𝔔'le (by rw [et]; exact ht') (by rw [eϖ]; exact hϖ')

end CMLocusAsm

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L]
    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K₀] [IsScalarTower A L ↥K₀]
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₀ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (c : ℕ) (hc : c = 0 ∨ c = 1728)
    (x₀ : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀)) [x₀.IsPrime]
    (hϖx₀ : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ϖ ∈ x₀)
    (hjx₀ : AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K₀) j₀
      - (c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀)) ∈ x₀) :
    ∃ 𝔔₀ : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀), 𝔔₀.IsPrime ∧ 𝔔₀ ≤ x₀ ∧
      AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K₀) j₀
        - (c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀)) ∈ 𝔔₀ ∧
      algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ϖ ∉ 𝔔₀ ∧
      (∀ (O : Type) [CommRing O] [IsLocalRing O] [Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) O]
        [IsLocalization.AtPrime O x₀],
        Ideal.map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) O) 𝔔₀
          ⊔ Ideal.span {algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) O
              (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ϖ)}
          = IsLocalRing.maximalIdeal O) ∧
      ∀ 𝔔 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀), 𝔔.IsPrime → 𝔔 ≤ x₀ →
        AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K₀) j₀
          - (c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀)) ∈ 𝔔 →
        algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ϖ ∉ 𝔔 → 𝔔 = 𝔔₀ := by
  exact CMLocusAsm.main q hq M' hqM' L K₀ hK₀ A hAq j₀ hj₀ ϖ hϖ c hc x₀ hϖx₀ hjx₀

end S_ModularCurve_FullLevel_existsUnique_prime_le_jChartFin_sub_mem_map_sup_span_eq_maximalIdeal_chartAlgFin_gamma0_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_existsUnique_prime_le_jChartFin_sub_mem_map_sup_span_eq_maximalIdeal_chartAlgFin_gamma0_of_not_dvd (solution)
