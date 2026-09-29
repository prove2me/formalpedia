-- Prove2me | solution 1 for ModularCurve.XOneP.exists_injective_not_isRegularLocalRing_stalk_specialFibre_of_mem_ssJSet_twoChartIntegralModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/05154670-f063-5aec-a7d2-50ea1f1c4313

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_ModularCurve_XOne_exists_injective_algHom_tensorProduct_chartAlgFin_apply_eq_evalAt_x1FunctionFieldC
import Theorems.Thm_ModularCurve_XOneP_not_subsingleton_minimalPrimes_span_germ_of_mem_ssJSet_twoChartIntegralModel_x1_mul
import Theorems.Thm_AlgebraicGeometry_Flat_isDomain_stalk_of_isDomain_stalk
import Theorems.Thm_AlgebraicGeometry_ker_fiberIota_stalkMap_eq_maximalIdeal_map
import Theorems.Thm_ModularCurve_mem_ssJSet_map_of_isAlgClosed
import Theorems.Thm_IsRegularLocalRing_isDomain
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_injective_not_isRegularLocalRing_stalk_specialFibre_of_mem_ssJSet_twoChartIntegralModel_x1_mul
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free ModularCurve.IgusaScheme.isOpenImmersion_fInf"
p2m_attr_erase "instance" "ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"
p2m_attr_erase "simp" "ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero"
p2m_attr_erase "simp" "TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply"
p2m_attr_erase "simp" "CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_baseChangeRingHom ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.cuspCount_one WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero"
p2m_attr_erase "simp" "ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve.TwoChartIntegralModel
open scoped TensorProduct

namespace SSLowerK11

theorem ker_algebraMap_eq_maximalIdeal
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [CharZero L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (Ω₀ : Type) [Field Ω₀] [CharP Ω₀ p] [Algebra A Ω₀] :
    RingHom.ker (algebraMap A Ω₀) = IsLocalRing.maximalIdeal A := by
  haveI : CharZero A := ⟨fun m n hmn => Nat.cast_injective (R := L) (by simpa using congrArg (algebraMap A L) hmn)⟩
  have hp : (p : A) ∈ RingHom.ker (algebraMap A Ω₀) := by
    rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
  have hp0 : (p : A) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  haveI : (RingHom.ker (algebraMap A Ω₀)).IsPrime := RingHom.ker_isPrime _
  have hne : RingHom.ker (algebraMap A Ω₀) ≠ ⊥ := fun h => hp0 (by rw [h, Ideal.mem_bot] at hp; exact hp)
  have hmax : (IsLocalRing.maximalIdeal A) ≠ ⊥ := by
    intro h; exact IsDiscreteValuationRing.not_a_field A h
  obtain ⟨P, hPuniq⟩ := ((IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime A).mp inferInstance).2
  have h1 := hPuniq.2 (RingHom.ker (algebraMap A Ω₀)) ⟨hne, inferInstance⟩
  have h2 := hPuniq.2 (IsLocalRing.maximalIdeal A) ⟨hmax, inferInstance⟩
  rw [h1, h2]

theorem algebraMap_eq_zero_of_mem_maximalIdeal
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [CharZero L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (Ω₀ : Type) [Field Ω₀] [CharP Ω₀ p] [Algebra A Ω₀] {a : A} (ha : a ∈ IsLocalRing.maximalIdeal A) :
    algebraMap A Ω₀ a = 0 := by
  rw [← RingHom.mem_ker, ker_algebraMap_eq_maximalIdeal p L A Ω₀]; exact ha

theorem exists_algHom_chartAlgFin
    (R : Type u) [CommRing R] (F F' : Type u) [Field F] [Field F'] [Algebra R F] [Algebra R F']
    (φ : F →ₐ[R] F') (j : F) (j' : F') [Fact (j ≠ 0)] [Fact (j' ≠ 0)] (hj : φ j = j') :
    ∃ ι : ↥(chartAlgFin R F j) →ₐ[R] ↥(chartAlgFin R F' j'),
      (∀ x, ((ι x : ↥(chartAlgFin R F' j')) : F') = φ x) ∧ Function.Injective ι := by
  classical
  have hadj : ∀ x ∈ Algebra.adjoin R ({j} : Set F), φ x ∈ Algebra.adjoin R ({j'} : Set F') := by
    intro x hx
    have : (Algebra.adjoin R ({j} : Set F)).map φ ≤ Algebra.adjoin R ({j'} : Set F') := by
      rw [AlgHom.map_adjoin, Set.image_singleton, hj]
    exact this ⟨x, hx, rfl⟩
  let ψ : ↥(Algebra.adjoin R ({j} : Set F)) →+* ↥(Algebra.adjoin R ({j'} : Set F')) :=
    (φ.toRingHom.comp (Algebra.adjoin R ({j} : Set F)).val.toRingHom).codRestrict
      (Algebra.adjoin R ({j'} : Set F')).toSubring (fun x => hadj x x.2)
  have hint : ∀ x : F, IsIntegral ↥(Algebra.adjoin R ({j} : Set F)) x →
      IsIntegral ↥(Algebra.adjoin R ({j'} : Set F')) (φ x) := by
    intro x hx
    exact hx.map_of_comp_eq ψ φ.toRingHom (by ext y; rfl)
  let ι : ↥(chartAlgFin R F j) →ₐ[R] ↥(chartAlgFin R F' j') :=
    (φ.comp (chartAlgFin R F j).val).codRestrict (chartAlgFin R F' j')
      (fun x => (mem_chartAlg_iff R F').mpr (hint x x.2))
  refine ⟨ι, fun x => rfl, ?_⟩
  intro x y hxy
  apply Subtype.ext
  exact φ.toRingHom.injective (congrArg (fun z : ↥(chartAlgFin R F' j') => (z : F')) hxy :)

open _root_.Polynomial _root_.AlgebraicGeometry.Polynomial in

theorem finite_chartAlgFin_of_floor
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (L : Type) [Field L] [Algebra A L]
    [IsFractionRing A L] [CharZero L]
    (K K' : IntermediateField L (LaurentSeries L)) (hle : K' ≤ K)
    [Algebra A ↥K] [IsScalarTower A L ↥K] [Algebra A ↥K'] [IsScalarTower A L ↥K']
    (j : ↥K) (j' : ↥K') [Fact (j ≠ 0)] [Fact (j' ≠ 0)]
    (hjj' : (IntermediateField.inclusion hle j' : ↥K) = j)
    (htj : Transcendental A j) (hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K)
    [Algebra ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)]
    [IsScalarTower A ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)]
    (hι : ∀ x : ↥(chartAlgFin A (↥K') j'),
      ((algebraMap _ ↥(chartAlgFin A (↥K) j) x : ↥(chartAlgFin A (↥K) j)) : ↥K) =
        IntermediateField.inclusion hle (x : ↥K')) :
    Module.Finite ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j) := by
  classical
  haveI : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    Algebra.IsSeparable.of_integral _ _
  obtain ⟨hfin, -⟩ := finite_polynomial_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD inferInstance
  letI algP : Algebra A[X] ↥(chartAlgFin A (↥K) j) := (polynomialToChartFin A (↥K) j).toRingHom.toAlgebra
  letI algP' : Algebra A[X] ↥(chartAlgFin A (↥K') j') := (polynomialToChartFin A (↥K') j').toRingHom.toAlgebra
  haveI : Module.Finite A[X] ↥(chartAlgFin A (↥K) j) := hfin
  have key : polynomialToChartFin A (↥K) j =
      (IsScalarTower.toAlgHom A ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)).comp
        (polynomialToChartFin A (↥K') j') := by
    apply Polynomial.algHom_ext
    simp only [polynomialToChartFin, AlgHom.comp_apply, Polynomial.aeval_X, IsScalarTower.coe_toAlgHom']
    apply Subtype.ext
    rw [hι, coe_jChartFin, coe_jChartFin, hjj']
  haveI : IsScalarTower A[X] ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j) :=
    IsScalarTower.of_algebraMap_eq fun P => by
      change polynomialToChartFin A (↥K) j P = algebraMap _ _ (polynomialToChartFin A (↥K') j' P)
      rw [key]
      rfl
  exact Module.Finite.of_restrictScalars_finite A[X] _ _

theorem exists_algHom_extend_of_isIntegral
    {R A' B Ω : Type*} [CommRing R] [CommRing A'] [CommRing B] [Field Ω] [IsAlgClosed Ω]
    [Algebra R A'] [Algebra R B] [Algebra R Ω] [Algebra A' B] [IsScalarTower R A' B]
    [Algebra.IsIntegral A' B] (hinj : Function.Injective (algebraMap A' B)) (χ : A' →ₐ[R] Ω) :
    ∃ χ' : B →ₐ[R] Ω, ∀ a : A', χ' (algebraMap A' B a) = χ a := by
  classical
  let P : Ideal A' := RingHom.ker χ.toRingHom
  haveI hP : P.IsPrime := RingHom.ker_isPrime _
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal B)
    (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  haveI := hQ
  haveI hQover : Q.LiesOver P := ⟨by rw [Ideal.under_def, hQP]⟩
  let χ₀ : A' ⧸ P →+* Ω := RingHom.kerLift χ.toRingHom
  have hχ₀ : Function.Injective χ₀ := RingHom.kerLift_injective _
  letI : Algebra (A' ⧸ P) Ω := χ₀.toAlgebra
  haveI : FaithfulSMul (A' ⧸ P) Ω := (faithfulSMul_iff_algebraMap_injective _ _).mpr hχ₀
  haveI : IsDomain (A' ⧸ P) := Ideal.Quotient.isDomain P
  haveI : IsDomain (B ⧸ Q) := Ideal.Quotient.isDomain Q
  let lam : (B ⧸ Q) →ₐ[A' ⧸ P] Ω := IsAlgClosed.lift
  let χ' : B →+* Ω := lam.toRingHom.comp (Ideal.Quotient.mk Q)
  have hext : ∀ a : A', χ' (algebraMap A' B a) = χ a := by
    intro a
    change lam (Ideal.Quotient.mk Q (algebraMap A' B a)) = χ a
    rw [← Ideal.Quotient.algebraMap_mk_of_liesOver Q P a, lam.commutes]
    rfl
  refine ⟨{ χ' with commutes' := fun r => ?_ }, hext⟩
  change χ' (algebraMap R B r) = algebraMap R Ω r
  rw [IsScalarTower.algebraMap_apply R A' B r, hext, χ.commutes]

section SSTransfer
open ModularCurve

private theorem cast_point_nsmul {k₀ : Type*} [Field k₀] [DecidableEq k₀] {W₁ W₂ : WeierstrassCurve k₀} (e : W₁ = W₂)
    (P : W₁.toAffine.Point) (n : ℕ) : e ▸ (n • P) = n • (e ▸ P) := by subst e; rfl

private theorem cast_point_eq_zero_iff {k₀ : Type*} [Field k₀] [DecidableEq k₀] {W₁ W₂ : WeierstrassCurve k₀} (e : W₁ = W₂)
    (P : W₁.toAffine.Point) : e ▸ P = (0 : W₂.toAffine.Point) ↔ P = 0 := by subst e; exact Iff.rfl

private theorem cast_point_zero {k₀ : Type*} [Field k₀] [DecidableEq k₀] {W₁ W₂ : WeierstrassCurve k₀} (e : W₁ = W₂) :
    e ▸ (0 : W₁.toAffine.Point) = (0 : W₂.toAffine.Point) := by subst e; rfl

theorem mem_ssJSet_of_map_mem {q : ℕ} {k₀ k : Type*} [Field k₀] [Field k] [DecidableEq k₀] [DecidableEq k]
    (θ : k₀ →+* k) (a : k₀) (h : θ a ∈ ssJSet q k) : a ∈ ssJSet q k₀ := by
  rw [mem_ssJSet_iff] at h ⊢
  intro W _ hW P hP
  letI : Algebra k₀ k := θ.toAlgebra
  have e : W = W.baseChange k₀ := by
    rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
  let P' : (W.baseChange k₀).toAffine.Point := e ▸ P
  have hP' : q • P' = 0 := by
    change q • (e ▸ P) = 0
    rw [← cast_point_nsmul e P q, hP]; exact cast_point_zero e
  let f : k₀ →ₐ[k₀] k := Algebra.ofId k₀ k
  haveI : (W.baseChange k).IsElliptic := by dsimp only [WeierstrassCurve.baseChange]; infer_instance
  let Pk : (W.baseChange k).toAffine.Point := WeierstrassCurve.Affine.Point.map f P'
  have hPk : q • Pk = 0 := by
    change q • (WeierstrassCurve.Affine.Point.map f P') = 0
    rw [← map_nsmul, hP', map_zero]
  have hj : (W.baseChange k).j = θ a := by
    simp only [WeierstrassCurve.baseChange]
    rw [WeierstrassCurve.map_j, hW]; rfl
  have hzero : Pk = 0 := h (W.baseChange k) hj Pk hPk
  have hP'0 : P' = 0 := WeierstrassCurve.Affine.Point.map_injective f (by rw [map_zero]; exact hzero)
  exact (cast_point_eq_zero_iff e P).mp hP'0

theorem mem_ssJSet_of_ringHom_of_mem_ssJSet {q : ℕ} [Fact q.Prime]
    {κ Ω₀ Ω : Type*} [CommRing κ] [IsDomain κ] [Field Ω₀] [Field Ω] [CharP Ω₀ q] [CharP Ω q]
    [IsAlgClosed Ω₀] [IsAlgClosed Ω] [DecidableEq Ω₀] [DecidableEq Ω]
    (ψ : κ →+* Ω₀) (χ : κ →+* Ω) (hψ : Function.Injective ψ) (hχ : Function.Injective χ)
    (a : κ) (h : ψ a ∈ ssJSet q Ω₀) : χ a ∈ ssJSet q Ω := by
  classical
  haveI : CharP κ q := ψ.charP hψ q
  let F := FractionRing κ
  let k₁ := AlgebraicClosure F
  let ψF : F →+* Ω₀ := IsFractionRing.lift hψ
  let χF : F →+* Ω := IsFractionRing.lift hχ
  letI algψ : Algebra F Ω₀ := ψF.toAlgebra
  letI algχ : Algebra F Ω := χF.toAlgebra
  let e₀ : k₁ →ₐ[F] Ω₀ := IsAlgClosed.lift
  let e : k₁ →ₐ[F] Ω := IsAlgClosed.lift
  let a₁ : k₁ := algebraMap F k₁ (algebraMap κ F a)
  have h₀ : e₀ a₁ = ψ a := by
    change e₀ (algebraMap F k₁ (algebraMap κ F a)) = ψ a
    rw [e₀.commutes]
    exact IsFractionRing.lift_algebraMap hψ a
  have h₁ : e a₁ = χ a := by
    change e (algebraMap F k₁ (algebraMap κ F a)) = χ a
    rw [e.commutes]
    exact IsFractionRing.lift_algebraMap hχ a
  have hk₁ : a₁ ∈ ssJSet q k₁ := mem_ssJSet_of_map_mem e₀.toRingHom a₁ (by rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h₀]; exact h)
  have := ModularCurve.mem_ssJSet_map_of_isAlgClosed e.toRingHom a₁ hk₁
  rwa [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h₁] at this

end SSTransfer

theorem stalkMap_algebraMap_eq_germ
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (x : ↥X) (r : R) :
    letI : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x)) :=
      AlgebraicGeometry.StructureSheaf.stalkAlgebra (R := R) (f.base x)
    (f.stalkMap x).hom (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x)) r) =
      (X.presheaf.germ ⊤ x trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
  letI : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x)) :=
    AlgebraicGeometry.StructureSheaf.stalkAlgebra (R := R) (f.base x)
  show (f.stalkMap x).hom (AlgebraicGeometry.StructureSheaf.toStalk R (f.base x) r) = _
  simp only [AlgebraicGeometry.StructureSheaf.toStalk, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  erw [Scheme.Hom.germ_stalkMap_apply f ⊤ x trivial]
  rfl

theorem asIdeal_base_eq_maximalIdeal
    {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (x : ↥X) (ϖ : R)
    (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (hx : (X.presheaf.germ ⊤ x trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    (f.base x).asIdeal = IsLocalRing.maximalIdeal R := by
  letI : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x)) :=
    AlgebraicGeometry.StructureSheaf.stalkAlgebra (R := R) (f.base x)
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x)) (f.base x).asIdeal :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk R (f.base x)
  rw [← stalkMap_algebraMap_eq_germ f x ϖ] at hx
  have h1 : algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x)) ϖ ∈
      IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal] at hx ⊢
    exact fun hu => hx (hu.map _)
  have h2 : ϖ ∈ (f.base x).asIdeal :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x)) (f.base x).asIdeal ϖ).mp h1
  refine ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le (f.base x).isPrime.ne_top ?_).symm
  rw [hϖ, Ideal.span_le, Set.singleton_subset_iff]
  exact h2

theorem map_maximalIdeal_stalkMap_eq_span
    {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (x : ↥X) (ϖ : R)
    (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (hfx : (f.base x).asIdeal = IsLocalRing.maximalIdeal R) :
    (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x))).map (f.stalkMap x).hom =
      Ideal.span {(X.presheaf.germ ⊤ x trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))} := by
  letI : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x)) :=
    AlgebraicGeometry.StructureSheaf.stalkAlgebra (R := R) (f.base x)
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x)) (f.base x).asIdeal :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk R (f.base x)
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (f.base x).asIdeal ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x)),
    hfx, hϖ, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, stalkMap_algebraMap_eq_germ]

theorem germ_mem_maximalIdeal_of_mem_asIdeal
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (x : ↥X) (ϖ : R)
    (hx : ϖ ∈ (f.base x).asIdeal) :
    (X.presheaf.germ ⊤ x trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  letI : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x)) :=
    AlgebraicGeometry.StructureSheaf.stalkAlgebra (R := R) (f.base x)
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x)) (f.base x).asIdeal :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk R (f.base x)
  rw [← stalkMap_algebraMap_eq_germ f x ϖ]
  have h1 : algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x)) ϖ ∈ IsLocalRing.maximalIdeal _ :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ (f.base x).asIdeal ϖ).mpr hx
  rw [IsLocalRing.mem_maximalIdeal] at h1 ⊢
  exact fun hu => h1 (isUnit_of_map_unit (f.stalkMap x).hom _ hu)

noncomputable def fibreStalkEquiv
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (s : ↥(Spec (CommRingCat.of R))) (q : ↥(f.fiber s))
    (t : X.presheaf.stalk ((f.fiberι s).base q))
    (ht : (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk (f.base ((f.fiberι s).base q)))).map
        (f.stalkMap ((f.fiberι s).base q)).hom = Ideal.span {t}) :
    ((X.presheaf.stalk ((f.fiberι s).base q)) ⧸ Ideal.span {t}) ≃+* (f.fiber s).presheaf.stalk q :=
  have hsurj : Function.Surjective ((f.fiberι s).stalkMap q).hom := (f.fiberι s).stalkMap_surjective q
  have hker : RingHom.ker ((f.fiberι s).stalkMap q).hom = Ideal.span {t} := by
    rw [AlgebraicGeometry.ker_fiberIota_stalkMap_eq_maximalIdeal_map f s q, ht]
  (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)

theorem not_isDomain_quotient_of_not_subsingleton_minimalPrimes
    {S : Type*} [CommRing S] (t : S) (h : ¬ ((Ideal.span {t} : Ideal S).minimalPrimes).Subsingleton) :
    ¬ IsDomain (S ⧸ Ideal.span {t}) := by
  intro hdom
  apply h
  have hprime : (Ideal.span {t} : Ideal S).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp hdom
  rw [Ideal.minimalPrimes_eq_subsingleton_self]
  exact Set.subsingleton_singleton

theorem localHom_eq_of_forall_apply_germ_eq {K : Type} [Field K] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of K)) (x : ↥Y)
    (φ₁ φ₂ : Y.presheaf.stalk x ⟶ CommRingCat.of K) [IsLocalHom φ₁.hom] [IsLocalHom φ₂.hom]
    (h₁ : ∀ c : K, φ₁.hom ((Y.presheaf.germ ⊤ x trivial).hom (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c))) = c)
    (h₂ : ∀ c : K, φ₂.hom ((Y.presheaf.germ ⊤ x trivial).hom (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c))) = c) :
    φ₁ = φ₂ := by

  let ψ₁ := Y.descResidueField φ₁
  let ψ₂ := Y.descResidueField φ₂
  have hψ₁ : Y.residue x ≫ ψ₁ = φ₁ := Scheme.residue_descResidueField _
  have hψ₂ : Y.residue x ≫ ψ₂ = φ₂ := Scheme.residue_descResidueField _

  let i : K → Y.residueField x := fun c =>
    (Y.residue x).hom ((Y.presheaf.germ ⊤ x trivial).hom (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)))
  have hi₁ : ∀ c, ψ₁.hom (i c) = c := fun c => by
    change (Y.residue x ≫ ψ₁).hom _ = c; rw [hψ₁]; exact h₁ c
  have hi₂ : ∀ c, ψ₂.hom (i c) = c := fun c => by
    change (Y.residue x ≫ ψ₂).hom _ = c; rw [hψ₂]; exact h₂ c

  have hisurj : Function.Surjective i := fun t => ⟨ψ₁.hom t, ψ₁.hom.injective (hi₁ _)⟩
  have hψ : ψ₁ = ψ₂ := by
    ext t
    obtain ⟨c, rfl⟩ := hisurj t
    rw [hi₁, hi₂]
  rw [← hψ₁, ← hψ₂, hψ]

theorem stalkClosedPointTo_germ_appTop {K : Type} [Field K] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of K))
    (s : Spec (CommRingCat.of K) ⟶ Y) (hs : s ≫ g = 𝟙 _) (c : K) :
    (Scheme.stalkClosedPointTo s).hom ((Y.presheaf.germ ⊤ (s.base (IsLocalRing.closedPoint K)) trivial).hom
      (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c))) = c := by
  have h := Scheme.germ_stalkClosedPointTo s ⊤ trivial
  have h' := congrArg (fun φ => φ.hom (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c))) h
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h'
  rw [h']

  have hcomp : (s.app ⊤).hom (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)) =
      ((s ≫ g).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c) := by
    rw [Scheme.Hom.comp_appTop]; rfl
  rw [hcomp, hs]
  simp only [Scheme.Hom.id_appTop, Iso.trans_hom, Functor.mapIso_hom, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply, CommRingCat.hom_id, RingHom.id_apply]
  change (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c) = c
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

theorem section_eq_of_base_eq {K : Type} [Field K] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of K))
    (s₁ s₂ : Spec (CommRingCat.of K) ⟶ Y) (hs₁ : s₁ ≫ g = 𝟙 _) (hs₂ : s₂ ≫ g = 𝟙 _)
    (e : s₁.base (IsLocalRing.closedPoint K) = s₂.base (IsLocalRing.closedPoint K)) : s₁ = s₂ := by
  apply (SpecToEquivOfLocalRing Y (CommRingCat.of K)).injective
  rw [SpecToEquivOfLocalRing_eq_iff]
  refine ⟨e, ?_⟩
  change Scheme.stalkClosedPointTo s₁ = (Y.presheaf.stalkCongr _).hom ≫ Scheme.stalkClosedPointTo s₂
  rw [← Iso.inv_comp_eq]
  haveI : IsLocalHom ((Y.presheaf.stalkCongr (by rw [e] : Inseparable (s₁.base (IsLocalRing.closedPoint K)) (s₂.base (IsLocalRing.closedPoint K)))).inv ≫
      Scheme.stalkClosedPointTo s₁).hom := by
    rw [CommRingCat.hom_comp]; infer_instance
  refine localHom_eq_of_forall_apply_germ_eq g (s₂.base (IsLocalRing.closedPoint K)) _ _ (fun c => ?_)
    (stalkClosedPointTo_germ_appTop g s₂ hs₂)
  rw [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  have hg : ((Y.presheaf.stalkCongr (by rw [e] : Inseparable (s₁.base (IsLocalRing.closedPoint K)) (s₂.base (IsLocalRing.closedPoint K)))).inv).hom
      ((Y.presheaf.germ ⊤ (s₂.base (IsLocalRing.closedPoint K)) trivial).hom (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c))) =
      (Y.presheaf.germ ⊤ (s₁.base (IsLocalRing.closedPoint K)) trivial).hom (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)) := by
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkCongr_inv, TopCat.Presheaf.germ_stalkSpecializes]
  rw [hg]
  exact stalkClosedPointTo_germ_appTop g s₁ hs₁ c

theorem exists_flat_hom_fiber
    {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of A))
    (Ω₀ : Type) [Field Ω₀] [Algebra A Ω₀] (hker : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A Ω₀ a = 0) :
    ∃ h : pullback f (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀))) ⟶ f.fiber (IsLocalRing.closedPoint A),
      Flat h ∧ h ≫ f.fiberι (IsLocalRing.closedPoint A) = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀))) := by
  classical
  let s₀ : ↥(Spec (CommRingCat.of A)) := IsLocalRing.closedPoint A
  have hs₀I : s₀.asIdeal = IsLocalRing.maximalIdeal A := rfl
  haveI hmaxI : s₀.asIdeal.IsMaximal := by rw [hs₀I]; exact IsLocalRing.maximalIdeal.isMaximal A

  let ρ₀ : A ⧸ s₀.asIdeal →+* Ω₀ := Ideal.Quotient.lift _ (algebraMap A Ω₀) (fun a ha => hker a (hs₀I ▸ ha))
  let eq₀ : (A ⧸ s₀.asIdeal) ≃+* s₀.asIdeal.ResidueField :=
    RingEquiv.ofBijective (algebraMap (A ⧸ s₀.asIdeal) s₀.asIdeal.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField s₀.asIdeal)
  let ρ : s₀.asIdeal.ResidueField →+* Ω₀ := ρ₀.comp eq₀.symm.toRingHom
  have hρ : ρ.comp (algebraMap A s₀.asIdeal.ResidueField) = algebraMap A Ω₀ := by
    ext a
    change ρ₀ (eq₀.symm (algebraMap A s₀.asIdeal.ResidueField a)) = algebraMap A Ω₀ a
    have : algebraMap A s₀.asIdeal.ResidueField a = eq₀ (Ideal.Quotient.mk _ a) := by
      change _ = algebraMap (A ⧸ s₀.asIdeal) s₀.asIdeal.ResidueField (Ideal.Quotient.mk _ a)
      rw [IsScalarTower.algebraMap_apply A (A ⧸ s₀.asIdeal) s₀.asIdeal.ResidueField a]
      rfl
    rw [this, RingEquiv.symm_apply_apply]
    rfl

  let τ : Spec (CommRingCat.of Ω₀) ⟶ Spec ((Spec (CommRingCat.of A)).residueField s₀) :=
    Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of A) s₀).hom
  have hτ : τ ≫ (Spec (CommRingCat.of A)).fromSpecResidueField s₀ = Spec.map (CommRingCat.ofHom (algebraMap A Ω₀)) := by
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    change (Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of A) s₀).hom) ≫
      Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of A) s₀).inv ≫ Spec.map (CommRingCat.ofHom (algebraMap A s₀.asIdeal.ResidueField)) = _
    rw [Category.assoc, ← Category.assoc (Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of A) s₀).hom),
      ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]

  let h : pullback f (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀))) ⟶ f.fiber s₀ :=
    pullback.map f (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀))) f ((Spec (CommRingCat.of A)).fromSpecResidueField s₀)
      (𝟙 X) τ (𝟙 _) (by simp) (by rw [Category.comp_id, hτ])
  have hfst : h ≫ f.fiberι s₀ = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀))) := by
    change pullback.map _ _ _ _ _ _ _ _ _ ≫ pullback.fst _ _ = _
    rw [pullback.lift_fst, Category.comp_id]
  have hsnd : h ≫ f.fiberToSpecResidueField s₀ = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀))) ≫ τ := by
    change pullback.map _ _ _ _ _ _ _ _ _ ≫ pullback.snd _ _ = _
    rw [pullback.lift_snd]
  have hsq : IsPullback (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀)))) h τ (f.fiberToSpecResidueField s₀) := by
    refine IsPullback.of_bot ?_ hsnd.symm (IsPullback.of_hasPullback f ((Spec (CommRingCat.of A)).fromSpecResidueField s₀)).flip
    rw [show h ≫ pullback.fst f ((Spec (CommRingCat.of A)).fromSpecResidueField s₀) =
        pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀))) from hfst, hτ]
    exact (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀)))).flip
  haveI hτflat : Flat τ := by
    haveI : Flat (Spec.map (CommRingCat.ofHom ρ)) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      show ρ.Flat
      letI := ρ.toAlgebra
      exact (inferInstance : Module.Flat s₀.asIdeal.ResidueField Ω₀)
    infer_instance
  exact ⟨h, MorphismProperty.of_isPullback hsq hτflat, hfst⟩

end SSLowerK11

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (Ω₀ : Type) [Field Ω₀] [CharP Ω₀ p] [IsAlgClosed Ω₀] [DecidableEq Ω₀] [Algebra A Ω₀]
    (jbar : ↥(ModularCurve.x1FunctionFieldC Ω₀ M)) (hjbar : (jbar : LaurentSeries Ω₀) = ModularCurve.jqModC Ω₀) :
    ∃ ι : {v : AlgebraicCurve.Place Ω₀ ↥(ModularCurve.x1FunctionFieldC Ω₀ M) //
            (jbar : ↥(ModularCurve.x1FunctionFieldC Ω₀ M)) ∈ v.toValuationSubring ∧
              v.evalAt jbar ∈ ModularCurve.ssJSet p Ω₀} →
          ↥(pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
            (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀)))),
      Function.Injective ι ∧
      ∀ v, ¬ IsRegularLocalRing
          ((pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
            (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀)))).presheaf.stalk (ι v)) ∧
        ∃ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j),
          (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y =
            (pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
              (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀)))).base (ι v) ∧
          ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
            (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
            RingHom.ker φ = y.asIdeal →
              φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet p Ω := by
  classical
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩

  let Afin := ↥(chartAlgFin A (↥K) j)
  have hϖ0 : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A Ω₀ a = 0 :=
    fun a ha => SSLowerK11.algebraMap_eq_zero_of_mem_maximalIdeal p L A Ω₀ ha

  let K' : IntermediateField L (LaurentSeries L) := ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M)
  have hK' : K' = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M) := rfl
  have hle : K' ≤ K := by
    rw [hK]
    exact IntermediateField.adjoin.mono L _ _ (Set.image_mono
      (ModularCurve.x1FunctionFieldC_le_of_dvd ℚ (dvd_mul_right M p)))
  letI : Algebra A ↥K' := ((algebraMap L ↥K').comp (algebraMap A L)).toAlgebra
  haveI : IsScalarTower A L ↥K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hjqmem : ModularCurve.coeffEmb L ModularCurve.jq ∈ K' :=
    ModularCurve.coeffEmb_mem_laurentBaseChange L
      (ModularCurve.intFormRatiosC_subset ℚ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ (CongruenceSubgroup.Gamma1 M)))
  let j' : ↥K' := ⟨ModularCurve.coeffEmb L ModularCurve.jq, hjqmem⟩
  have hj' : ((j' : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq := rfl
  have hjj' : (IntermediateField.inclusion hle j' : ↥K) = j := Subtype.ext (by rw [hj]; rfl)
  haveI : Fact (j' ≠ 0) := ⟨fun h0 => (Fact.out : j ≠ 0) (by rw [← hjj', h0, map_zero])⟩
  obtain ⟨ιF, hιF, hιFinj⟩ := SSLowerK11.exists_algHom_chartAlgFin A (↥K') (↥K)
    ((IntermediateField.inclusion hle).restrictScalars A) j' j hjj'
  letI : Algebra ↥(chartAlgFin A (↥K') j') Afin := ιF.toRingHom.toAlgebra
  haveI : IsScalarTower A ↥(chartAlgFin A (↥K') j') Afin :=
    IsScalarTower.of_algebraMap_eq (fun a => (ιF.commutes a).symm)
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T]
  haveI hFD := ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
    (CongruenceSubgroup.Gamma1 (M * p)) hT L K hK j hj
  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  haveI : Module.Finite ↥(chartAlgFin A (↥K') j') Afin :=
    SSLowerK11.finite_chartAlgFin_of_floor A L K K' hle j j' hjj' htj hFD hιF
  haveI : Algebra.IsIntegral ↥(chartAlgFin A (↥K') j') Afin := inferInstance
  have hιFj : algebraMap ↥(chartAlgFin A (↥K') j') Afin (jChartFin A (↥K') j') = jChartFin A (↥K) j := by
    apply Subtype.ext
    change ((ιF (jChartFin A (↥K') j') : Afin) : ↥K) = _
    rw [hιF, coe_jChartFin]
    exact hjj'

  obtain ⟨Φ, hΦinj, hΦj⟩ :=
    ModularCurve.XOne.exists_injective_algHom_tensorProduct_chartAlgFin_apply_eq_evalAt_x1FunctionFieldC
      p M hM hpM L ζ hζ K' hK' A hAp hζA j' hj' Ω₀ jbar hjbar

  let S := {v : AlgebraicCurve.Place Ω₀ ↥(ModularCurve.x1FunctionFieldC Ω₀ M) //
            (jbar : ↥(ModularCurve.x1FunctionFieldC Ω₀ M)) ∈ v.toValuationSubring ∧
              v.evalAt jbar ∈ ModularCurve.ssJSet p Ω₀}
  let pr : S → {v : AlgebraicCurve.Place Ω₀ ↥(ModularCurve.x1FunctionFieldC Ω₀ M) //
            (jbar : ↥(ModularCurve.x1FunctionFieldC Ω₀ M)) ∈ v.toValuationSubring} := fun v => ⟨v.1, v.2.1⟩
  have hpr : Function.Injective pr := fun a b hab =>
    Subtype.ext (congrArg (fun x : {v : AlgebraicCurve.Place Ω₀ ↥(ModularCurve.x1FunctionFieldC Ω₀ M) //
      (jbar : ↥(ModularCurve.x1FunctionFieldC Ω₀ M)) ∈ v.toValuationSubring} => (x : AlgebraicCurve.Place Ω₀ ↥(ModularCurve.x1FunctionFieldC Ω₀ M))) hab)

  let ψ : S → (↥(chartAlgFin A (↥K') j') →ₐ[A] Ω₀) := fun v =>
    ((Φ (pr v)).restrictScalars A).comp
      (Algebra.TensorProduct.includeRight : ↥(chartAlgFin A (↥K') j') →ₐ[A] Ω₀ ⊗[A] ↥(chartAlgFin A (↥K') j'))
  have hψ : ∀ v b, ψ v b = Φ (pr v) (1 ⊗ₜ b) := fun v b => rfl
  have hψinj : Function.Injective ψ := by
    intro v w hvw
    apply hpr
    apply hΦinj
    apply Algebra.TensorProduct.ext'
    intro a b
    have hab : ∀ u, Φ (pr u) (a ⊗ₜ b) = a * Φ (pr u) (1 ⊗ₜ b) := fun u => by
      rw [show a ⊗ₜ[A] b = a • ((1 : Ω₀) ⊗ₜ[A] b) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul,
        smul_eq_mul]
    rw [hab, hab, ← hψ, ← hψ, hvw]

  have hext : ∀ v : S, ∃ χ : Afin →ₐ[A] Ω₀, ∀ b, χ (algebraMap _ Afin b) = ψ v b :=
    fun v => SSLowerK11.exists_algHom_extend_of_isIntegral (R := A) hιFinj (ψ v)
  choose ψt hψt using hext
  have hψtinj : Function.Injective ψt := by
    intro v w hvw
    apply hψinj
    ext b
    rw [← hψt, ← hψt, hvw]

  let X := AlgebraicCurve.TwoChartIntegralModel A (↥K) j
  let tb := AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j
  let sΩ : Spec (CommRingCat.of Ω₀) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom (algebraMap A Ω₀))
  let pt : ↥(Spec (CommRingCat.of Ω₀)) := IsLocalRing.closedPoint Ω₀

  let y : S → ↥(XFin A (↥K) j) := fun v => (Spec.map (CommRingCat.ofHom (ψt v).toRingHom)).base pt
  have hy : ∀ v, (y v).asIdeal = RingHom.ker (ψt v).toRingHom := by
    intro v
    change ((PrimeSpectrum.comap (ψt v).toRingHom) pt).asIdeal = _
    rw [PrimeSpectrum.comap_asIdeal]
    change Ideal.comap _ (IsLocalRing.maximalIdeal Ω₀) = _
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField Ω₀), ← RingHom.ker_eq_comap_bot]

  have hcomm : ∀ v, (Spec.map (CommRingCat.ofHom (ψt v).toRingHom) ≫ ιFin A (↥K) j) ≫ tb = 𝟙 _ ≫ sΩ := by
    intro v
    rw [Category.assoc, ιFin_toBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Category.id_comp]
    change Spec.map (CommRingCat.ofHom ((ψt v).toRingHom.comp (algebraMap A Afin))) = sΩ
    rw [AlgHom.toRingHom_eq_coe, (ψt v).comp_algebraMap]
  let σ : S → (Spec (CommRingCat.of Ω₀) ⟶ pullback tb sΩ) := fun v =>
    pullback.lift (Spec.map (CommRingCat.ofHom (ψt v).toRingHom) ≫ ιFin A (↥K) j) (𝟙 _) (hcomm v)
  have hσfst : ∀ v, σ v ≫ pullback.fst tb sΩ = Spec.map (CommRingCat.ofHom (ψt v).toRingHom) ≫ ιFin A (↥K) j :=
    fun v => pullback.lift_fst _ _ _
  have hσsnd : ∀ v, σ v ≫ pullback.snd tb sΩ = 𝟙 _ := fun v => pullback.lift_snd _ _ _
  let ι : S → ↥(pullback tb sΩ) := fun v => (σ v).base pt
  have hιfst : ∀ v, (pullback.fst tb sΩ).base (ι v) = (ιFin A (↥K) j).base (y v) := by
    intro v
    change ((σ v) ≫ pullback.fst tb sΩ).base pt = _
    rw [hσfst]
    rfl

  have hιinj : Function.Injective ι := by
    intro v w hvw
    have hσ : σ v = σ w := SSLowerK11.section_eq_of_base_eq (pullback.snd tb sΩ) (σ v) (σ w) (hσsnd v) (hσsnd w) hvw
    have h1 : Spec.map (CommRingCat.ofHom (ψt v).toRingHom) ≫ ιFin A (↥K) j =
        Spec.map (CommRingCat.ofHom (ψt w).toRingHom) ≫ ιFin A (↥K) j := by
      rw [← hσfst, ← hσfst, hσ]
    rw [cancel_mono] at h1
    have h2 : CommRingCat.ofHom (ψt v).toRingHom = CommRingCat.ofHom (ψt w).toRingHom := Spec.map_injective h1
    apply hψtinj
    apply AlgHom.coe_ringHom_injective
    have h3 := congrArg CommRingCat.Hom.hom h2
    simpa using h3

  have htoken : ∀ (v : S) (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
      (χ : Afin →+* Ω), RingHom.ker χ = (y v).asIdeal → χ (jChartFin A (↥K) j) ∈ ModularCurve.ssJSet p Ω := by
    intro v Ω _ _ _ _ χ hχ

    have hker : RingHom.ker χ = RingHom.ker (ψt v).toRingHom := by rw [hχ, hy]
    haveI : (RingHom.ker (ψt v).toRingHom).IsPrime := RingHom.ker_isPrime _
    let κv := Afin ⧸ RingHom.ker (ψt v).toRingHom
    haveI : IsDomain κv := Ideal.Quotient.isDomain _
    let ψbar : κv →+* Ω₀ := RingHom.kerLift (ψt v).toRingHom
    let χbar : κv →+* Ω := Ideal.Quotient.lift _ χ (fun a ha => by rwa [← RingHom.mem_ker, hker])
    have hχbar : Function.Injective χbar := by
      rw [injective_iff_map_eq_zero]
      intro a ha
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Ideal.Quotient.lift_mk] at ha
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hker ▸ (RingHom.mem_ker).mpr ha)
    have key := SSLowerK11.mem_ssJSet_of_ringHom_of_mem_ssJSet ψbar χbar (RingHom.kerLift_injective _) hχbar
      (Ideal.Quotient.mk _ (jChartFin A (↥K) j)) (by
        change (ψt v).toRingHom (jChartFin A (↥K) j) ∈ _
        rw [← hιFj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hψt, hψ, hΦj]
        exact v.2.2)
    first | exact key | simpa using key | simpa [χ] using key
  refine ⟨ι, hιinj, fun v => ⟨fun hreg => ?_, y v, (hιfst v).symm, htoken v⟩⟩

  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} := hϖirr.maximalIdeal_eq

  obtain ⟨h, hflat, hhι⟩ := SSLowerK11.exists_flat_hom_fiber tb Ω₀ hϖ0
  let q : ↥(tb.fiber (IsLocalRing.closedPoint A)) := h.base (ι v)
  let z : ↥X := (tb.fiberι (IsLocalRing.closedPoint A)).base q
  have hyz : (ιFin A (↥K) j).base (y v) = z := by
    rw [← hιfst]
    change _ = (h ≫ tb.fiberι (IsLocalRing.closedPoint A)).base (ι v)
    rw [hhι]

  have htbz : ϖ ∈ (tb.base z).asIdeal := by
    rw [← hyz]
    change ϖ ∈ ((ιFin A (↥K) j ≫ tb).base (y v)).asIdeal
    rw [ιFin_toBase]
    change ϖ ∈ ((PrimeSpectrum.comap (algebraMap A Afin)) (y v)).asIdeal
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hy, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes]
    exact hϖ0 ϖ (hϖ ▸ Ideal.mem_span_singleton_self ϖ)
  let ϖz : X.presheaf.stalk z := (X.presheaf.germ ⊤ z trivial).hom (tb.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ))
  have hz : ϖz ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) :=
    SSLowerK11.germ_mem_maximalIdeal_of_mem_asIdeal tb z ϖ htbz

  have h2 := ModularCurve.XOneP.not_subsingleton_minimalPrimes_span_germ_of_mem_ssJSet_twoChartIntegralModel_x1_mul
    p M hM hpM L ζ hζ K hK A hAp hζA j hj ϖ hϖ z ϖz rfl hz (y v) hyz (htoken v)
  have hnd : ¬ IsDomain (X.presheaf.stalk z ⧸ Ideal.span {ϖz}) :=
    SSLowerK11.not_isDomain_quotient_of_not_subsingleton_minimalPrimes ϖz h2

  have hfz : (tb.base z).asIdeal = IsLocalRing.maximalIdeal A := SSLowerK11.asIdeal_base_eq_maximalIdeal tb z ϖ hϖ hz
  have hmax := SSLowerK11.map_maximalIdeal_stalkMap_eq_span tb z ϖ hϖ hfz
  let e := SSLowerK11.fibreStalkEquiv tb (IsLocalRing.closedPoint A) q ϖz hmax
  have hnd' : ¬ IsDomain ((tb.fiber (IsLocalRing.closedPoint A)).presheaf.stalk q) :=
    fun hd => hnd (e.toMulEquiv.isDomain _)

  haveI := hflat
  haveI : IsDomain ((pullback tb sΩ).presheaf.stalk (ι v)) := by
    haveI := hreg; exact IsRegularLocalRing.isDomain _
  exact hnd' (AlgebraicGeometry.Flat.isDomain_stalk_of_isDomain_stalk h (ι v))

#print axioms solution

end S_ModularCurve_XOneP_exists_injective_not_isRegularLocalRing_stalk_specialFibre_of_mem_ssJSet_twoChartIntegralModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_injective_not_isRegularLocalRing_stalk_specialFibre_of_mem_ssJSet_twoChartIntegralModel_x1_mul (solution)
