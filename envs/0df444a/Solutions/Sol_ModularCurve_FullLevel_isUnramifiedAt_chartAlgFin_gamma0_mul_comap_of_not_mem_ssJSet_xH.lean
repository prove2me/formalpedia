-- Prove2me | solution 1 for ModularCurve.FullLevel.isUnramifiedAt_chartAlgFin_gamma0_mul_comap_of_not_mem_ssJSet_xH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/fe294b9c-be6d-5733-b2ea-132fbb59ca52

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_FullLevel_map_jChartFin_mem_ssJSet_of_exists_two_minimalPrimes_span_le_chartAlgFin_laurentBaseChange_gamma0_mul
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_Module_free_of_isIntegrallyClosed_of_finite_of_isRegularLocalRing_of_ringKrullDim_le_two
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
import Theorems.Thm_Subalgebra_ringKrullDim_localization_tensor_eq_one_of_irreducible
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isOpenImmersion_spec_tensor_chartAlgFin
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_IsRegularLocalRing_isDomain
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_FullLevel_exists_sub_inclusion_mem_nonunits_gauss_gamma0_of_mem_gauss_gamma0_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_isUnramifiedAt_chartAlgFin_gamma0_mul_comap_of_not_mem_ssJSet_xH
p2m_attr_erase "instance" "ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1"
p2m_attr_erase "instance" "isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange ModularCurve.instIsElliptic_tateBase ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms"
p2m_attr_erase "instance" "CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_heckeBetaBarRingHom"
p2m_attr_erase "simp" "ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq"
p2m_attr_erase "simp" "TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg RegularLocalRingQuotientAscent.dualNumberFst_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero"
p2m_attr_erase "simp" "PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.coe_baseChangeRingHom ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply"
p2m_attr_erase "simp" "ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut"
p2m_attr_erase "simp" "ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

universe u

namespace OrdRegAux

p2m_open "AlgebraicCurve.TwoChartIntegralModel Polynomial AlgebraicGeometry.Polynomial"

theorem essFiniteType_localization_atPrime_comap
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S] (y : Ideal S) [y.IsPrime] :
    letI := (Localization.localRingHom (y.comap (algebraMap R S)) y (algebraMap R S) rfl).toAlgebra
    Algebra.EssFiniteType (Localization.AtPrime (y.comap (algebraMap R S))) (Localization.AtPrime y) := by
  letI := (Localization.localRingHom (y.comap (algebraMap R S)) y (algebraMap R S) rfl).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime (y.comap (algebraMap R S))) (Localization.AtPrime y) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map]
      exact IsScalarTower.algebraMap_apply R S (Localization.AtPrime y) r
  haveI : Algebra.EssFiniteType R (Localization.AtPrime y) := inferInstance
  exact Algebra.EssFiniteType.of_comp R (Localization.AtPrime (y.comap (algebraMap R S))) (Localization.AtPrime y)

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

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

theorem ringKrullDim_le_of_isIntegral_ringHom
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R := by
  letI : Algebra R S := φ.toAlgebra
  refine Order.krullDim_le_of_strictMono (fun P : PrimeSpectrum S => PrimeSpectrum.comap φ P) ?_
  intro P Q hPQ
  have hle : P.asIdeal ≤ Q.asIdeal := le_of_lt hPQ
  have hne : P.asIdeal ≠ Q.asIdeal := fun h => ne_of_lt hPQ (PrimeSpectrum.ext h)
  obtain ⟨x, hxQ, hxP⟩ : ∃ x ∈ Q.asIdeal, x ∉ P.asIdeal := by
    by_contra h
    exact hne (le_antisymm hle fun y hy => by_contra fun hy' => h ⟨y, hy, hy'⟩)
  change P.asIdeal.comap φ < Q.asIdeal.comap φ
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hxQ, hxP⟩ (hφ x)

theorem ringKrullDim_localization_le {R : Type*} [CommRing R] (M : Submonoid R) (S : Type*) [CommRing S]
    [Algebra R S] [IsLocalization M S] : ringKrullDim S ≤ ringKrullDim R := by
  refine Order.krullDim_le_of_strictMono (fun P : PrimeSpectrum S => PrimeSpectrum.comap (algebraMap R S) P) ?_
  refine Monotone.strictMono_of_injective (fun P Q h => ?_) (PrimeSpectrum.localization_comap_injective S M)
  change (PrimeSpectrum.comap (algebraMap R S) P).asIdeal ≤ (PrimeSpectrum.comap (algebraMap R S) Q).asIdeal
  exact Ideal.comap_mono h

private lemma le_one_of_add_one_le {a : WithBot ℕ∞} (h : a + 1 ≤ (1 : WithBot ℕ∞) + 1) : a ≤ 1 := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe b =>
    induction b using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe n =>
      rw [← WithBot.coe_one, ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe] at h
      have h3 : n + 1 ≤ 1 + 1 := by exact_mod_cast h
      have h4 : n ≤ 1 := by omega
      rw [← WithBot.coe_one, WithBot.coe_le_coe]
      exact_mod_cast h4

section DimCount

variable (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)]

private noncomputable def ψ : A[X] →ₐ[A] ↥(Algebra.adjoin A ({j} : Set K)) :=
  (Polynomial.aeval j).codRestrict (Algebra.adjoin A ({j} : Set K))
    (fun P => by rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨P, rfl⟩)

omit [IsDomain A] [IsDiscreteValuationRing A] [Fact (j ≠ 0)] in
private theorem ψ_surjective : Function.Surjective (ψ A K j) := by
  rintro ⟨y, hy⟩
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
  obtain ⟨P, rfl⟩ := hy
  exact ⟨P, Subtype.ext rfl⟩

private noncomputable def ι : ↥(Algebra.adjoin A ({j} : Set K)) →+* ↥(chartAlgFin A K j) :=
  (Subalgebra.inclusion (adjoin_le_chartAlg A K {j})).toRingHom

omit [IsDomain A] [IsDiscreteValuationRing A] [Fact (j ≠ 0)] in
private theorem ι_isIntegral : (ι A K j).IsIntegral := by
  intro x
  obtain ⟨P, hPm, hP⟩ := (mem_chartAlg_iff A K).mp x.2
  refine ⟨P, hPm, ?_⟩
  apply Subtype.ext
  have h1 := Polynomial.hom_eval₂ P (ι A K j) ((chartAlgFin A K j).val.toRingHom) x
  have h2 : ((chartAlgFin A K j).val.toRingHom).comp (ι A K j) =
      algebraMap ↥(Algebra.adjoin A ({j} : Set K)) K := rfl
  rw [h2] at h1
  exact h1.trans hP

omit [IsDomain A] [IsDiscreteValuationRing A] [Fact (j ≠ 0)] in

private theorem coe_polynomialToChartFin (P : A[X]) :
    ((polynomialToChartFin A K j P : ↥(chartAlgFin A K j)) : K) = Polynomial.aeval j P := by
  rw [show j = (chartAlgFin A K j).val (jChartFin A K j) from rfl, Polynomial.aeval_algHom_apply]
  rfl

set_option synthInstance.maxHeartbeats 1600000 in
omit [Fact (j ≠ 0)] in

theorem ringKrullDim_quotient_localization_eq_one (htj : Transcendental A j)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (y : Ideal ↥(chartAlgFin A K j)) [y.IsMaximal] (hyϖ : algebraMap A _ ϖ ∈ y) :
    ringKrullDim (Localization.AtPrime y ⧸
      Ideal.span {algebraMap (↥(chartAlgFin A K j)) (Localization.AtPrime y) (algebraMap A _ ϖ)}) = 1 := by
  classical

  letI algP : Algebra A[X] ↥(chartAlgFin A K j) := (polynomialToChartFin A K j).toRingHom.toAlgebra
  have halg : ∀ P : A[X], algebraMap A[X] ↥(chartAlgFin A K j) P = polynomialToChartFin A K j P := fun _ => rfl
  have hfact : algebraMap A[X] ↥(chartAlgFin A K j) = (ι A K j).comp (ψ A K j).toRingHom :=
    RingHom.ext fun P => Subtype.ext (by rw [halg, coe_polynomialToChartFin]; rfl)
  haveI hint : Algebra.IsIntegral A[X] ↥(chartAlgFin A K j) := ⟨fun b => by
    show (algebraMap A[X] ↥(chartAlgFin A K j)).IsIntegralElem b
    rw [hfact]
    exact RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ (ψ_surjective A K j))
      (ι_isIntegral A K j) b⟩
  have hinjP : Function.Injective (algebraMap A[X] ↥(chartAlgFin A K j)) := fun P Q h => by
    apply transcendental_iff_injective.mp htj
    have := congrArg (fun b : ↥(chartAlgFin A K j) => (b : K)) h
    simpa only [halg, coe_polynomialToChartFin] using this
  haveI : FaithfulSMul A[X] ↥(chartAlgFin A K j) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinjP
  have hCϖ : algebraMap A[X] ↥(chartAlgFin A K j) (C ϖ) = algebraMap A _ ϖ := by
    rw [halg, polynomialToChartFin, Polynomial.aeval_C]

  have hϖ0 : ϖ ≠ 0 := fun h =>
    IsDiscreteValuationRing.not_a_field A (by rw [hϖ, Ideal.span_singleton_eq_bot]; exact h)
  have hϖB : algebraMap A ↥(chartAlgFin A K j) ϖ ≠ 0 := by
    rw [← hCϖ]
    exact fun h => (Polynomial.C_ne_zero.mpr hϖ0) (hinjP (by rw [h, map_zero]))
  have hϖS : algebraMap (↥(chartAlgFin A K j)) (Localization.AtPrime y) (algebraMap A _ ϖ) ≠ 0 := fun h =>
    hϖB (IsLocalization.injective (Localization.AtPrime y) y.primeCompl_le_nonZeroDivisors (by rw [h, map_zero]))
  apply le_antisymm
  ·
    apply le_one_of_add_one_le
    calc ringKrullDim (Localization.AtPrime y ⧸ Ideal.span {algebraMap (↥(chartAlgFin A K j))
            (Localization.AtPrime y) (algebraMap A _ ϖ)}) + 1
        ≤ ringKrullDim (Localization.AtPrime y) :=
          ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hϖS)
      _ ≤ ringKrullDim ↥(chartAlgFin A K j) := ringKrullDim_localization_le y.primeCompl _
      _ ≤ ringKrullDim A[X] := by
          calc ringKrullDim ↥(chartAlgFin A K j) ≤ ringKrullDim ↥(Algebra.adjoin A ({j} : Set K)) :=
                ringKrullDim_le_of_isIntegral_ringHom (ι A K j) (ι_isIntegral A K j)
            _ ≤ ringKrullDim A[X] := ringKrullDim_le_of_isIntegral_ringHom (ψ A K j).toRingHom
                (RingHom.isIntegral_of_surjective _ (ψ_surjective A K j))
      _ = ringKrullDim A + 1 := Polynomial.ringKrullDim_of_isNoetherianRing
      _ = 1 + 1 := by rw [IsDiscreteValuationRing.ringKrullDim_eq_one]
  ·
    let 𝔭 : Ideal A[X] := Ideal.map (C : A →+* A[X]) (IsLocalRing.maximalIdeal A)
    haveI h𝔭 : 𝔭.IsPrime := Ideal.isPrime_map_C_of_isPrime
    have hCϖ𝔭 : C ϖ ∈ 𝔭 := Ideal.mem_map_of_mem _ (by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ)
    haveI : (y.under A[X]).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal y
    have h𝔭le : 𝔭 ≤ y.under A[X] := by
      rw [Ideal.map_le_iff_le_comap, hϖ, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
      show algebraMap A[X] ↥(chartAlgFin A K j) (C ϖ) ∈ y
      rw [hCϖ]; exact hyϖ
    have h𝔭ne : 𝔭 ≠ y.under A[X] := by
      intro h
      have hmax : 𝔭.IsMaximal := h ▸ inferInstance
      have hf : IsField (A[X] ⧸ 𝔭) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient 𝔭).mp hmax
      exact Polynomial.not_isField (A ⧸ IsLocalRing.maximalIdeal A)
        (MulEquiv.isField hf (Ideal.polynomialQuotientEquivQuotientPolynomial
          (IsLocalRing.maximalIdeal A)).toMulEquiv)
    obtain ⟨Q, hQy, hQprime, hQover⟩ :=
      Ideal.exists_ideal_lt_liesOver_of_lt (p := 𝔭) (q := y.under A[X]) y (lt_of_le_of_ne h𝔭le h𝔭ne)
    have hϖQ : algebraMap A ↥(chartAlgFin A K j) ϖ ∈ Q := by
      have : C ϖ ∈ Q.under A[X] := hQover.over ▸ hCϖ𝔭
      rw [← hCϖ]; exact Ideal.mem_comap.mp this

    let P₁ : Ideal (Localization.AtPrime y) := Q.map (algebraMap _ (Localization.AtPrime y))
    haveI : P₁.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime y hQy.le
    have hP₁lt : P₁ < IsLocalRing.maximalIdeal (Localization.AtPrime y) := by
      refine lt_of_le_of_ne ?_ fun h => hQy.ne ?_
      · rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.map_mono hQy.le
      · rw [← Ideal.under_map_of_isLocalizationAtPrime y (S := Localization.AtPrime y) hQy.le]
        show P₁.under _ = y
        rw [h]; exact Localization.AtPrime.under_maximalIdeal
    rw [ringKrullDim_quotient, Order.one_le_krullDim_iff]
    refine ⟨⟨⟨P₁, inferInstance⟩, ?_⟩, ⟨⟨IsLocalRing.maximalIdeal _, inferInstance⟩, ?_⟩, hP₁lt⟩
    · rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_singleton_le_iff_mem]
      exact Ideal.mem_map_of_mem _ hϖQ
    · rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_singleton_le_iff_mem]
      show _ ∈ IsLocalRing.maximalIdeal (Localization.AtPrime y)
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hyϖ

end DimCount

section Floor

variable (L : Type) [Field L] [CharZero L] (K K' : IntermediateField L (LaurentSeries L)) (hle : K' ≤ K)
  (j : ↥K) (j' : ↥K') (hjj' : (IntermediateField.inclusion hle j' : ↥K) = j)
  (hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K)

set_option synthInstance.maxHeartbeats 1600000 in
include hjj' hFD in
omit [CharZero L] in

theorem isIntegral_inclusion_of_finiteDimensional_adjoin :
    (IntermediateField.inclusion hle).toRingHom.IsIntegral := by
  intro x
  haveI := hFD
  have hx : IsIntegral ↥(IntermediateField.adjoin L ({j} : Set ↥K)) x := Algebra.IsIntegral.isIntegral x
  obtain ⟨P, hPm, hP⟩ := hx

  have hrange : IntermediateField.adjoin L ({j} : Set ↥K) ≤ (IntermediateField.inclusion hle).fieldRange := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨j', hjj'⟩
  set P' : Polynomial ↥K := P.map (algebraMap ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K) with hP'
  have hlifts : P' ∈ Polynomial.lifts (IntermediateField.inclusion hle).toRingHom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [hP', Polynomial.coeff_map]
    obtain ⟨y, hy⟩ := hrange (P.coeff n).2
    exact ⟨y, hy⟩
  obtain ⟨Q, hQP, -, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts (hPm.map _)
  refine ⟨Q, hQm, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hQP, hP', Polynomial.eval_map, hP]

set_option synthInstance.maxHeartbeats 1600000 in
include hjj' hFD in

theorem isSeparable_of_inclusion :
    letI := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    Algebra.IsSeparable ↥K' ↥K := by
  letI := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : Algebra.IsIntegral ↥K' ↥K :=
    ⟨fun x => isIntegral_inclusion_of_finiteDimensional_adjoin L K K' hle j j' hjj' hFD x⟩
  exact Algebra.IsSeparable.of_integral _ _

end Floor

end OrdRegAux

set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open AlgebraicCurve.TwoChartIntegralModel
open scoped TensorProduct

namespace OrdRegL2

section QuotLoc

variable {B : Type} [CommRing B] (P : Ideal B) [P.IsPrime] (x : B)

@[reducible] noncomputable def quotAlg : Algebra (B ⧸ Ideal.span {x})
    (Localization.AtPrime P ⧸ Ideal.span {algebraMap B (Localization.AtPrime P) x}) :=
  (Ideal.quotientMap (Ideal.span {algebraMap B (Localization.AtPrime P) x}) (algebraMap B (Localization.AtPrime P))
    (by rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]; exact Ideal.subset_span rfl)).toAlgebra

theorem isLocalization_quotient_localization [IsDomain B] (Q : Ideal (B ⧸ Ideal.span {x})) [Q.IsPrime]
    (hQ : Q.comap (Ideal.Quotient.mk (Ideal.span {x})) = P) :
    letI := quotAlg P x
    IsLocalization Q.primeCompl
      (Localization.AtPrime P ⧸ Ideal.span {algebraMap B (Localization.AtPrime P) x}) := by
  letI := quotAlg P x
  have halg : ∀ b : B, algebraMap (B ⧸ Ideal.span {x}) (Localization.AtPrime P ⧸ Ideal.span {algebraMap B (Localization.AtPrime P) x})
      (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ (algebraMap B (Localization.AtPrime P) b) := fun _ => rfl
  have hmemP : ∀ b : B, Ideal.Quotient.mk (Ideal.span {x}) b ∈ Q ↔ b ∈ P := by
    intro b
    rw [← hQ, Ideal.mem_comap]
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  ·
    rintro ⟨s, hs⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective s
    have hb : b ∉ P := fun h => hs ((hmemP b).mpr h)
    rw [halg]
    exact (IsLocalization.map_units (Localization.AtPrime P) (⟨b, hb⟩ : P.primeCompl)).map _
  ·
    intro z
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨b, t⟩, hbt⟩ := IsLocalization.surj P.primeCompl w
    refine ⟨⟨Ideal.Quotient.mk _ b, ⟨Ideal.Quotient.mk _ (t : B), fun h => t.2 ((hmemP _).mp h)⟩⟩, ?_⟩
    show Ideal.Quotient.mk _ w * algebraMap _ _ (Ideal.Quotient.mk _ (t : B)) = algebraMap _ _ (Ideal.Quotient.mk _ b)
    rw [halg, halg, ← map_mul, hbt]
  ·
    intro a₁ a₂ h
    obtain ⟨b₁, rfl⟩ := Ideal.Quotient.mk_surjective a₁
    obtain ⟨b₂, rfl⟩ := Ideal.Quotient.mk_surjective a₂
    rw [halg, halg, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h
    obtain ⟨w, hw⟩ := h
    obtain ⟨⟨c, t⟩, hct⟩ := IsLocalization.surj P.primeCompl w

    have h1 : algebraMap B (Localization.AtPrime P) ((t : B) * (b₁ - b₂)) =
        algebraMap B (Localization.AtPrime P) (c * x) := by
      rw [map_mul, map_mul, map_sub, ← hw, ← hct]; ring
    have h2 : (t : B) * (b₁ - b₂) = c * x :=
      IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors h1
    refine ⟨⟨Ideal.Quotient.mk _ (t : B), fun h => t.2 ((hmemP _).mp h)⟩, ?_⟩
    show Ideal.Quotient.mk _ (t : B) * Ideal.Quotient.mk _ b₁ = Ideal.Quotient.mk _ (t : B) * Ideal.Quotient.mk _ b₂
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton']
    exact ⟨c, by rw [← mul_sub, h2, mul_comm]⟩

end QuotLoc

theorem ringKrullDim_le_of_isIntegral_ringHom
    {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R := by
  letI : Algebra R S := φ.toAlgebra
  refine Order.krullDim_le_of_strictMono (fun P : PrimeSpectrum S => PrimeSpectrum.comap φ P) ?_
  intro P Q hPQ
  have hle : P.asIdeal ≤ Q.asIdeal := le_of_lt hPQ
  have hne : P.asIdeal ≠ Q.asIdeal := fun h => ne_of_lt hPQ (PrimeSpectrum.ext h)
  obtain ⟨x, hxQ, hxP⟩ : ∃ x ∈ Q.asIdeal, x ∉ P.asIdeal := by
    by_contra h
    exact hne (le_antisymm hle fun y hy => by_contra fun hy' => h ⟨y, hy, hy'⟩)
  change P.asIdeal.comap φ < Q.asIdeal.comap φ
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hxQ, hxP⟩ (hφ x)

theorem ringKrullDim_chartAlg_singleton_le
    (R : Type) [CommRing R] (F : Type) [Field F] [Algebra R F] (s : F) :
    ringKrullDim ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s}) ≤ ringKrullDim (Polynomial R) := by
  let ψ : Polynomial R →ₐ[R] ↥(Algebra.adjoin R ({s} : Set F)) :=
    (Polynomial.aeval s).codRestrict (Algebra.adjoin R ({s} : Set F))
      (fun P => by
        rw [Algebra.adjoin_singleton_eq_range_aeval]
        exact ⟨P, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨P, rfl⟩ := hy
    exact ⟨P, Subtype.ext rfl⟩
  let ι : ↥(Algebra.adjoin R ({s} : Set F)) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s}) :=
    (Subalgebra.inclusion (AlgebraicCurve.TwoChartIntegralModel.adjoin_le_chartAlg R F {s})).toRingHom
  have hι : ι.IsIntegral := by
    intro x
    obtain ⟨P, hPm, hP⟩ := (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff R F).mp x.2
    refine ⟨P, hPm, ?_⟩
    apply Subtype.ext
    have h1 := Polynomial.hom_eval₂ P ι ((AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s}).val.toRingHom) x
    have h2 : ((AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s}).val.toRingHom).comp ι =
        algebraMap ↥(Algebra.adjoin R ({s} : Set F)) F := rfl
    rw [h2] at h1
    exact h1.trans hP
  calc ringKrullDim ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s})
      ≤ ringKrullDim ↥(Algebra.adjoin R ({s} : Set F)) := ringKrullDim_le_of_isIntegral_ringHom ι hι
    _ ≤ ringKrullDim (Polynomial R) :=
        ringKrullDim_le_of_isIntegral_ringHom ψ.toRingHom (RingHom.isIntegral_of_surjective _ hψ)

theorem ringKrullDim_localization_le {R : Type} [CommRing R] (M : Submonoid R) (S : Type) [CommRing S] [Algebra R S]
    [IsLocalization M S] : ringKrullDim S ≤ ringKrullDim R := by
  refine Order.krullDim_le_of_strictMono (fun P : PrimeSpectrum S => PrimeSpectrum.comap (algebraMap R S) P) ?_
  refine Monotone.strictMono_of_injective (fun P Q h => ?_) (PrimeSpectrum.localization_comap_injective S M)
  change (PrimeSpectrum.comap (algebraMap R S) P).asIdeal ≤ (PrimeSpectrum.comap (algebraMap R S) Q).asIdeal
  exact Ideal.comap_mono h

theorem algebraMap_stalk_eq_germ {S : Type} [CommRing S] (q : ↥(Spec (CommRingCat.of S))) (s : S) :
    letI : Algebra S ((Spec (CommRingCat.of S)).presheaf.stalk q) :=
      AlgebraicGeometry.StructureSheaf.stalkAlgebra (R := S) q
    algebraMap S ((Spec (CommRingCat.of S)).presheaf.stalk q) s =
      ((Spec (CommRingCat.of S)).presheaf.germ ⊤ q trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom s) := by
  show AlgebraicGeometry.StructureSheaf.toStalk S q s = _
  rfl

theorem exists_ringEquiv_stalk_localization
    {S : Type} [CommRing S] {X : Scheme.{0}} (ι : Spec (CommRingCat.of S) ⟶ X) [IsOpenImmersion ι]
    (q : ↥(Spec (CommRingCat.of S))) :
    Nonempty (X.presheaf.stalk (ι.base q) ≃+* Localization.AtPrime q.asIdeal) :=
  ⟨((asIso (ι.stalkMap q)).commRingCatIsoToRingEquiv).trans
    (AlgebraicGeometry.StructureSheaf.stalkIso S q).toRingEquiv.symm⟩

theorem exists_maximal_ringEquiv_localization {R T : Type} [CommRing R] [CommRing T] (e : R ≃+* T)
    (P : Ideal R) [hP : P.IsMaximal] :
    ∃ (Q : Ideal T) (_ : Q.IsMaximal), Nonempty (Localization.AtPrime P ≃+* Localization.AtPrime Q) := by
  let Q : Ideal T := P.comap e.symm.toRingHom
  haveI hQ : Q.IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
  have hMQ : P.primeCompl.map e.toMonoidHom = Q.primeCompl := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ hx
      exact hy (by simpa [Q, Ideal.mem_comap] using hx)
    · intro hx
      refine ⟨e.symm x, fun hy => hx ?_, by simp⟩
      simp only [Q, Ideal.mem_comap, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      simpa using hy
  exact ⟨Q, hQ, ⟨IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime P) (Localization.AtPrime Q) e hMQ⟩⟩

theorem isRegularLocalRing_localization_of_smooth
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (K : Type) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)]
    [Smooth (toBase A K j)] (y : ↥(XFin A K j)) :
    IsRegularLocalRing (Localization.AtPrime y.asIdeal) := by
  have h := AlgebraicGeometry.Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing A (toBase A K j) ((ιFin A K j).base y)
  obtain ⟨E⟩ := exists_ringEquiv_stalk_localization (ιFin A K j) y
  exact @IsRegularLocalRing.of_ringEquiv _ _ h _ _ E

theorem isRegularLocalRing_localization_tensor_of_smooth
    (A : Type) [CommRing A] (K : Type) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)]
    (hs : Smooth (toBase A K j)) (k : Type) [Field k] [Algebra A k]
    (Q : Ideal (↥(chartAlgFin A K j) ⊗[A] k)) [hQ : Q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime Q) := by
  obtain ⟨g, hgo, -, -, -⟩ := AlgebraicCurve.TwoChartIntegralModel.exists_isOpenImmersion_spec_tensor_chartAlgFin A K j k
  haveI := hgo
  haveI hsm : Smooth (pullback.snd (toBase A K j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))) :=
    MorphismProperty.pullback_snd _ _ hs
  let q : ↥(Spec (CommRingCat.of (↥(chartAlgFin A K j) ⊗[A] k))) := ⟨Q, hQ⟩
  have hst := @AlgebraicGeometry.Smooth.isRegularLocalRing_stalk k _ _
    (pullback.snd (toBase A K j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))) hsm (g.base q)
  obtain ⟨E⟩ := exists_ringEquiv_stalk_localization g q
  exact @IsRegularLocalRing.of_ringEquiv _ _ hst _ _ E

theorem exists_ringEquiv_fibre_localization_tensor
    (A : Type) [CommRing A] [IsLocalRing A] (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (B : Type) [CommRing B] [IsDomain B] [Algebra A B]
    (y : Ideal B) [hy : y.IsMaximal] (hyϖ : algebraMap A B ϖ ∈ y) :
    ∃ (Q₁ : Ideal (B ⊗[A] (IsLocalRing.ResidueField A))) (_ : Q₁.IsMaximal)
      (Q₂ : Ideal ((IsLocalRing.ResidueField A) ⊗[A] B)) (_ : Q₂.IsMaximal),
      Nonempty ((Localization.AtPrime y ⧸ Ideal.span {algebraMap B (Localization.AtPrime y) (algebraMap A B ϖ)}) ≃+*
        Localization.AtPrime Q₁) ∧
      Nonempty ((Localization.AtPrime y ⧸ Ideal.span {algebraMap B (Localization.AtPrime y) (algebraMap A B ϖ)}) ≃+*
        Localization.AtPrime Q₂) := by
  classical
  set ϖ' : B := algebraMap A B ϖ with hϖ'def
  let ybar : Ideal (B ⧸ Ideal.span {ϖ'}) := y.map (Ideal.Quotient.mk _)
  haveI hybar : ybar.IsPrime := by
    apply Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker, Ideal.span_singleton_le_iff_mem]; exact hyϖ
  have hycomap : ybar.comap (Ideal.Quotient.mk (Ideal.span {ϖ'})) = y := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left, Ideal.span_singleton_le_iff_mem]
    exact hyϖ
  haveI hybarmax : ybar.IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective hy).resolve_left
      (fun h => hy.ne_top (by
        have := congrArg (Ideal.comap (Ideal.Quotient.mk (Ideal.span {ϖ'}))) h
        rw [hycomap, Ideal.comap_top] at this
        exact this))
  letI := quotAlg y ϖ'
  haveI hloc := isLocalization_quotient_localization y ϖ' ybar hycomap
  let Efib : (Localization.AtPrime y ⧸ Ideal.span {algebraMap B (Localization.AtPrime y) ϖ'}) ≃+* Localization.AtPrime ybar :=
    (IsLocalization.algEquiv ybar.primeCompl
      (Localization.AtPrime y ⧸ Ideal.span {algebraMap B (Localization.AtPrime y) ϖ'}) (Localization.AtPrime ybar)).toRingEquiv
  have hmapϖ : (IsLocalRing.maximalIdeal A).map (algebraMap A B) = Ideal.span {ϖ'} := by
    rw [hϖ, Ideal.map_span, Set.image_singleton]
  let e₁ : (B ⧸ Ideal.span {ϖ'}) ≃+* B ⊗[A] (IsLocalRing.ResidueField A) :=
    (Ideal.quotEquivOfEq hmapϖ.symm).trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (IsLocalRing.maximalIdeal A)).toRingEquiv
  let e₂ : (B ⧸ Ideal.span {ϖ'}) ≃+* (IsLocalRing.ResidueField A) ⊗[A] B :=
    e₁.trans (Algebra.TensorProduct.comm A B (IsLocalRing.ResidueField A)).toRingEquiv
  obtain ⟨Q₁, hQ₁, ⟨E₁⟩⟩ := exists_maximal_ringEquiv_localization e₁ ybar
  obtain ⟨Q₂, hQ₂, ⟨E₂⟩⟩ := exists_maximal_ringEquiv_localization e₂ ybar
  exact ⟨Q₁, hQ₁, Q₂, hQ₂, ⟨Efib.trans E₁⟩, ⟨Efib.trans E₂⟩⟩

set_option maxHeartbeats 3200000 in

theorem L2_floor_regular_of_smooth
    (L : Type) [Field L] [CharZero L]
    (K' : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K'] [IsScalarTower A L ↥K'] (j' : ↥K') [Fact (j' ≠ 0)]
    (htj : Transcendental A j')
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j'} : Set ↥K')) ↥K')
    (hsmooth : Smooth (toBase A (↥K') j'))
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (y' : Ideal ↥(chartAlgFin A (↥K') j')) [hy' : y'.IsMaximal] (hy'ϖ : algebraMap A ↥(chartAlgFin A (↥K') j') ϖ ∈ y') :
    IsRegularLocalRing (Localization.AtPrime y') ∧
    ringKrullDim (Localization.AtPrime y') ≤ 2 ∧
    IsRegularLocalRing (Localization.AtPrime y' ⧸ Ideal.span {algebraMap A (Localization.AtPrime y') ϖ}) ∧
    ringKrullDim (Localization.AtPrime y' ⧸ Ideal.span {algebraMap A (Localization.AtPrime y') ϖ}) = 1 ∧
    IsDomain (Localization.AtPrime y' ⧸ Ideal.span {algebraMap A (Localization.AtPrime y') ϖ}) := by
  classical
  haveI := hFD
  haveI : Algebra.IsIntegral ↥(IntermediateField.adjoin L ({j'} : Set ↥K')) ↥K' := Algebra.IsIntegral.of_finite _ _
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j'} : Set ↥K')) ↥K' := Algebra.IsSeparable.of_integral _ _
  have hFT := AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K') j' htj hFD hsep
  haveI := hsmooth

  have hreg1 : IsRegularLocalRing (Localization.AtPrime y') :=
    isRegularLocalRing_localization_of_smooth A (↥K') j' (⟨y', hy'.isPrime⟩ : ↥(XFin A (↥K') j'))

  have hdim2 : ringKrullDim (Localization.AtPrime y') ≤ 2 := by
    refine (ringKrullDim_localization_le y'.primeCompl (Localization.AtPrime y')).trans ?_
    refine (ringKrullDim_chartAlg_singleton_le A (↥K') (j' : ↥K')).trans ?_
    rw [Polynomial.ringKrullDim_of_isNoetherianRing,
      (IsPrincipalIdealRing.ringKrullDim_eq_one A) (IsDiscreteValuationRing.not_isField A)]
    norm_num

  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, ⟨E₁⟩, ⟨E₂⟩⟩ := exists_ringEquiv_fibre_localization_tensor A ϖ hϖ ↥(chartAlgFin A (↥K') j') y' hy'ϖ

  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  have hϖκ : algebraMap A (IsLocalRing.ResidueField A) ϖ = 0 := by
    rw [show algebraMap A (IsLocalRing.ResidueField A) ϖ = IsLocalRing.residue A ϖ from rfl, IsLocalRing.residue_eq_zero_iff, hϖ]
    exact Ideal.mem_span_singleton_self ϖ
  have hinj : Function.Injective (Polynomial.aeval (R := A) (j' : ↥K')) := transcendental_iff_injective.mp htj
  have hrange : (Polynomial.aeval (R := A) (j' : ↥K')).range = Algebra.adjoin A ({(j' : ↥K')} : Set ↥K') :=
    (Algebra.adjoin_singleton_eq_range_aeval A (j' : ↥K')).symm
  let eR : Polynomial A ≃ₐ[A] ↥(Algebra.adjoin A ({(j' : ↥K')} : Set ↥K')) :=
    (AlgEquiv.ofInjective (Polynomial.aeval (R := A) (j' : ↥K')) hinj).trans (Subalgebra.equivOfEq _ _ hrange)
  have hdimQ₂ : ringKrullDim (Localization.AtPrime Q₂) = 1 :=
    Subalgebra.ringKrullDim_localization_tensor_eq_one_of_irreducible hirr
      (Algebra.adjoin A ({(j' : ↥K')} : Set ↥K')) (chartAlgFin A (↥K') j') eR
      (AlgebraicCurve.TwoChartIntegralModel.adjoin_le_chartAlg A (↥K') {(j' : ↥K')})
      (fun a => (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff A (↥K')).mp a.2)
      hFT.1 (AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg A (↥K') {(j' : ↥K')})
      (IsLocalRing.ResidueField A) hϖκ Q₂

  have hregQ₁ : IsRegularLocalRing (Localization.AtPrime Q₁) :=
    isRegularLocalRing_localization_tensor_of_smooth A (↥K') j' hsmooth (IsLocalRing.ResidueField A) Q₁

  have halgϖ : algebraMap A (Localization.AtPrime y') ϖ =
      algebraMap ↥(chartAlgFin A (↥K') j') (Localization.AtPrime y') (algebraMap A ↥(chartAlgFin A (↥K') j') ϖ) := IsScalarTower.algebraMap_apply _ _ _ _
  rw [halgϖ]
  have hregfib := @IsRegularLocalRing.of_ringEquiv _ _ hregQ₁ _ _ E₁.symm
  haveI := hregfib
  have hdom : IsDomain (Localization.AtPrime y' ⧸ Ideal.span {algebraMap ↥(chartAlgFin A (↥K') j') (Localization.AtPrime y') (algebraMap A ↥(chartAlgFin A (↥K') j') ϖ)}) :=
    @IsRegularLocalRing.isDomain _ _ hregfib
  exact ⟨hreg1, hdim2, hregfib, (ringKrullDim_eq_of_ringEquiv E₂).trans hdimQ₂, hdom⟩

end OrdRegL2

open _root_.Algebra _root_.CategoryTheory.Algebra _root_.TensorProduct.Algebra in

theorem L3_localization
    {A' B : Type u} [CommRing A'] [CommRing B] [IsDomain A'] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra A' B] [Module.Finite A' B] [FaithfulSMul A' B] (y' : Ideal A') [y'.IsPrime] :
    Module.Finite (Localization.AtPrime y') (Localization (algebraMapSubmonoid B y'.primeCompl)) ∧
    IsIntegrallyClosed (Localization (algebraMapSubmonoid B y'.primeCompl)) ∧
    IsDomain (Localization (algebraMapSubmonoid B y'.primeCompl)) ∧
    FaithfulSMul (Localization.AtPrime y') (Localization (algebraMapSubmonoid B y'.primeCompl)) := by
  have hinj := FaithfulSMul.algebraMap_injective A' B
  have hM : algebraMapSubmonoid B y'.primeCompl ≤ nonZeroDivisors B := by
    apply le_nonZeroDivisors_of_noZeroDivisors
    rintro ⟨a, ha, h0⟩
    have : a = 0 := hinj (by rw [h0, map_zero])
    exact ha (this ▸ y'.zero_mem)
  haveI : IsDomain (Localization (algebraMapSubmonoid B y'.primeCompl)) := IsLocalization.isDomain_localization hM
  refine ⟨Module.Finite.of_isLocalization A' B y'.primeCompl, isIntegrallyClosed_of_isLocalization (Localization (algebraMapSubmonoid B y'.primeCompl)) (algebraMapSubmonoid B y'.primeCompl) hM,
    inferInstance, ?_⟩

  rw [faithfulSMul_iff_algebraMap_injective]
  have : algebraMap (Localization.AtPrime y') (Localization (algebraMapSubmonoid B y'.primeCompl)) =
      IsLocalization.map (T := algebraMapSubmonoid B y'.primeCompl) (Localization (algebraMapSubmonoid B y'.primeCompl))
        (algebraMap A' B) (Submonoid.le_comap_map y'.primeCompl) := by
    apply IsLocalization.ringHom_ext y'.primeCompl
    simp only [IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]
  rw [this]
  haveI : IsLocalization (y'.primeCompl.map (algebraMap A' B)) (Localization (algebraMapSubmonoid B y'.primeCompl)) := by
    exact (Localization.isLocalization : IsLocalization (algebraMapSubmonoid B y'.primeCompl) (Localization (algebraMapSubmonoid B y'.primeCompl)))
  exact IsLocalization.map_injective_of_injective (M := y'.primeCompl) (S := Localization.AtPrime y')
    (Q := Localization (algebraMapSubmonoid B y'.primeCompl)) (g := algebraMap A' B) hinj

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open IsLocalRing AlgebraicCurve.TwoChartIntegralModel

namespace OrdRegL4

theorem mem_minimalPrimes_span_singleton_of_height_eq_one
    {B : Type u} [CommRing B] (x : B) (hx : x ∈ nonZeroDivisors B)
    (Q : Ideal B) [Q.IsPrime] (hxQ : x ∈ Q) (hQ : Q.height = 1) :
    Q ∈ (Ideal.span {x}).minimalPrimes := by
  have hle : Ideal.span {x} ≤ Q := (Ideal.span_singleton_le_iff_mem _).mpr hxQ
  haveI : Q.FiniteHeight := Ideal.finiteHeight_iff_lt.mpr (Or.inr (by rw [hQ]; exact ENat.one_lt_top))
  apply Ideal.mem_minimalPrimes_of_height_eq hle
  rw [hQ]
  exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors hx

end OrdRegL4

namespace OrdRegPort
open scoped MatrixGroups
open CongruenceSubgroup

theorem Gamma_le_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    Gamma M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA' := Gamma_mem.mp hA
  have h0 : A ∈ Gamma0 M := by rw [Gamma0_mem]; exact hA'.2.2.1
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    rw [hA'.2.2.2, Units.val_one]
  rw [this]
  exact one_mem H

theorem GammaH_finiteIndex (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma_le_GammaH M H)

end OrdRegPort

namespace ModularCurve
p2m_export "ModularCurve" "translation_mem_GammaH Gamma1_le_GammaH xHFunctionField qExpFunctionFieldC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange FullLevel.levelH ssJSet jqModC jqModC_rat map_jqModC FullLevel.map_jChartFin_mem_ssJSet_of_exists_two_minimalPrimes_span_le_chartAlgFin_laurentBaseChange_gamma0_mul finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange transcendental_of_coe_eq_coeffEmb_jq FullLevel.exists_sub_inclusion_mem_nonunits_gauss_gamma0_of_mem_gauss_gamma0_mul"
namespace O4Eng
p2m_open "ModularCurve~coeffMap_qExpand~transcendental_jqModC~coeffMap_ofPowerSeries~coeffMap_jqModC"

open scoped MatrixGroups
open IsLocalRing

section Laurent

variable {R S : Type*} [CommRing R] [CommRing S]

theorem coeffMap_ofPowerSeries (f : R →+* S) (u : PowerSeries R) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R u) = HahnSeries.ofPowerSeries ℤ S (u.map f) := by
  ext k
  rw [coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

theorem coeffMap_qExpand (f : R →+* S) (n : ℕ) [NeZero n] (x : LaurentSeries R) :
    coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  rw [coeffMap_coeff]
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk, map_zero]

theorem coeffMap_jqModC (f : R →+* S) : coeffMap f (jqModC R) = jqModC S :=
  map_jqModC f

theorem jqModC_coeff_neg_one (K : Type*) [CommRing K] : (jqModC K).coeff (-1) = 1 := by
  have h := HahnSeries.coeff_single_mul_add (r := (1 : K))
    (x := HahnSeries.ofPowerSeries ℤ K (jNum.map (Int.castRingHom K))) (a := 0) (b := -1)
  rw [zero_add] at h
  rw [jqModC, h, one_mul, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum, map_one]

theorem transcendental_of_order_neg {K : Type*} [Field K] (x : LaurentSeries K) (hx : x.order < 0) :
    Transcendental K x := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  rintro ⟨p, hp0, hpx⟩
  set d := p.natDegree with hd
  have hsm : ∀ (c : K) (y : LaurentSeries K) (n : ℤ),
      (algebraMap K (LaurentSeries K) c * y).coeff n = c * y.coeff n := by
    intro c y n
    rw [ModularCurve.algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]
  have key : (Polynomial.aeval x p).coeff (d • x.order) = p.leadingCoeff * (x ^ d).coeff (d • x.order) := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum, Finset.sum_eq_single d]
    · rw [hsm, Polynomial.leadingCoeff]
    · intro i hi hid
      have hi' : i < d := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hid
      rw [hsm, HahnSeries.coeff_eq_zero_of_lt_order, mul_zero]
      rw [HahnSeries.order_pow]
      simp only [nsmul_eq_mul]
      have : (i : ℤ) < d := by exact_mod_cast hi'
      nlinarith
    · intro h
      exact absurd (Finset.self_mem_range_succ d) h
  rw [hpx, HahnSeries.coeff_zero] at key
  have h1 : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
  have h2 : (x ^ d).coeff (d • x.order) ≠ 0 := by
    rw [← HahnSeries.order_pow x d]
    exact (HahnSeries.coeff_order_eq_zero.not.mpr) (pow_ne_zero _ hx0)
  exact mul_ne_zero h1 h2 key.symm

theorem order_neg_of_coeff_ne_zero {K : Type*} [Field K] {x : LaurentSeries K} {n : ℤ} (hn : n < 0)
    (h : x.coeff n ≠ 0) : x.order < 0 :=
  lt_of_le_of_lt (HahnSeries.order_le_of_coeff_ne_zero h) hn

theorem transcendental_jqModC (K : Type*) [Field K] : Transcendental K (jqModC K) :=
  transcendental_of_order_neg _ (order_neg_of_coeff_ne_zero (n := -1) (by norm_num)
    (by rw [jqModC_coeff_neg_one]; exact one_ne_zero))

theorem transcendental_qExpand_jqModC (K : Type*) [Field K] (n : ℕ) [NeZero n] :
    Transcendental K (qExpand K n (jqModC K)) := by
  refine transcendental_of_order_neg _ (order_neg_of_coeff_ne_zero (n := (n : ℤ) * (-1)) ?_ ?_)
  · have : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    linarith
  · rw [qExpand_coeff_mul, jqModC_coeff_neg_one]
    exact one_ne_zero

theorem transcendental_of_coe {K L : Type*} [Field K] [Field L] [Algebra K L] (E : IntermediateField K L)
    (z : E) (h : Transcendental K (z : L)) : Transcendental K z :=
  fun hz => h (IntermediateField.isAlgebraic_iff.mp hz)

end Laurent

theorem mem_or_neg_mem_gammaH_of_mem_gammaH_sup {M : ℕ} (H : Subgroup (ZMod M)ˣ) (γ : SL(2, ℤ))
    (hγ : γ ∈ CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1))) :
    γ ∈ CohCarrier.GammaH M H ∨ -γ ∈ CohCarrier.GammaH M H := by
  obtain ⟨h0, hu⟩ := CohCarrier.mem_GammaH_iff.mp hγ
  rw [Subgroup.mem_sup] at hu
  obtain ⟨y, hy, z, hz, hyz⟩ := hu
  rw [Subgroup.mem_zpowers_iff] at hz
  obtain ⟨k, rfl⟩ := hz
  rcases Int.even_or_odd k with hk | hk
  · rw [hk.neg_one_zpow, mul_one] at hyz
    exact Or.inl (CohCarrier.mem_GammaH_iff.mpr ⟨h0, hyz ▸ hy⟩)
  · rw [hk.neg_one_zpow, mul_neg_one] at hyz
    right
    have h0' : -γ ∈ CongruenceSubgroup.Gamma0 M := by
      rw [CongruenceSubgroup.Gamma0_mem] at h0 ⊢
      simp [h0]
    refine CohCarrier.mem_GammaH_iff.mpr ⟨h0', ?_⟩
    have : CohCarrier.gamma0Units M ⟨-γ, h0'⟩ = -CohCarrier.gamma0Units M ⟨γ, h0⟩ := by
      ext
      simp [CohCarrier.gamma0Units, CongruenceSubgroup.Gamma0Map]
    rw [this, ← hyz, neg_neg]
    exact hy

end ModularCurve.O4Eng

namespace ModularCurve
p2m_export "ModularCurve" "translation_mem_GammaH Gamma1_le_GammaH xHFunctionField qExpFunctionFieldC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange FullLevel.levelH ssJSet jqModC jqModC_rat map_jqModC FullLevel.map_jChartFin_mem_ssJSet_of_exists_two_minimalPrimes_span_le_chartAlgFin_laurentBaseChange_gamma0_mul finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange transcendental_of_coe_eq_coeffEmb_jq FullLevel.exists_sub_inclusion_mem_nonunits_gauss_gamma0_of_mem_gauss_gamma0_mul"
namespace O4Eng
p2m_open "ModularCurve~coeffMap_qExpand~transcendental_jqModC~coeffMap_ofPowerSeries~coeffMap_jqModC"

theorem algebraMap_LS_eq_single {R : Type*} [CommRing R] (r : R) :
    algebraMap R (LaurentSeries R) r = HahnSeries.single 0 r := by
  have h1 : algebraMap R (PowerSeries R) r = PowerSeries.C r := by simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
  rfl

theorem coeffMap_algebraMap' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R) :
    coeffMap f (algebraMap R (LaurentSeries R) r) = algebraMap S (LaurentSeries S) (f r) := by
  rw [algebraMap_LS_eq_single, algebraMap_LS_eq_single, coeffMap_single]

theorem coeffMap_aeval {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (t : LaurentSeries R)
    (P : Polynomial R) :
    coeffMap f (Polynomial.aeval t P) = Polynomial.aeval (coeffMap f t) (P.map f) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂]
  congr 1
  exact RingHom.ext fun r => coeffMap_algebraMap' f r

theorem exists_mul_X_pow_eq_ofPowerSeries {R : Type*} [CommRing R] (g : LaurentSeries R) :
    ∃ (x : PowerSeries R) (d : ℕ), g * HahnSeries.ofPowerSeries ℤ R (PowerSeries.X ^ d) = HahnSeries.ofPowerSeries ℤ R x := by
  by_cases hle : 0 ≤ g.order
  · refine ⟨PowerSeries.X ^ g.order.toNat * g.powerSeriesPart, 0, ?_⟩
    rw [pow_zero, map_one, mul_one, map_mul, map_pow, HahnSeries.ofPowerSeries_X, HahnSeries.single_pow, one_pow,
      ← LaurentSeries.single_order_mul_powerSeriesPart g]
    congr 2
    · simp [Int.toNat_of_nonneg hle]
    · rw [LaurentSeries.single_order_mul_powerSeriesPart]
  · refine ⟨g.powerSeriesPart, (-g.order).toNat, ?_⟩
    rw [HahnSeries.ofPowerSeries_X_pow, LaurentSeries.ofPowerSeries_powerSeriesPart, mul_comm]
    have : 0 ≤ -g.order := by omega
    rw [Int.toNat_of_nonneg this]

end ModularCurve.O4Eng

namespace ModularCurve
p2m_export "ModularCurve" "translation_mem_GammaH Gamma1_le_GammaH xHFunctionField qExpFunctionFieldC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange FullLevel.levelH ssJSet jqModC jqModC_rat map_jqModC FullLevel.map_jChartFin_mem_ssJSet_of_exists_two_minimalPrimes_span_le_chartAlgFin_laurentBaseChange_gamma0_mul finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange transcendental_of_coe_eq_coeffEmb_jq FullLevel.exists_sub_inclusion_mem_nonunits_gauss_gamma0_of_mem_gauss_gamma0_mul"
namespace O4Red
p2m_open "ModularCurve~coeffMap_qExpand~transcendental_jqModC~coeffMap_ofPowerSeries~coeffMap_jqModC"

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel ModularCurve.O4Eng

theorem mem_nonunits_iff' {F : Type*} [Field F] (O : ValuationSubring F) (f : F) :
    f ∈ O.nonunits ↔ f ∈ O ∧ (f = 0 ∨ f⁻¹ ∉ O) := by
  constructor
  · intro h
    exact ⟨(O.valuation_le_one_iff f).mp (le_of_lt ((O.mem_nonunits_iff).mp h)), (O.mem_nonunits_iff_or).mp h⟩
  · rintro ⟨-, h⟩
    exact (O.mem_nonunits_iff_or).mpr h

theorem mem_nonunits_comap_iff {F F' : Type*} [Field F] [Field F'] (O : ValuationSubring F) (ι : F' →+* F)
    (f : F') : f ∈ (O.comap ι).nonunits ↔ ι f ∈ O.nonunits := by
  rw [mem_nonunits_iff', mem_nonunits_iff', ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀,
    map_eq_zero_iff ι ι.injective]

theorem mem_minimalPrimes_of_height_eq_one {B : Type*} [CommRing B] [IsDomain B] (𝔓 : Ideal B) (hP : 𝔓.IsPrime)
    (hh : 𝔓.height = 1) (ϖ : B) (hϖ : ϖ ∈ 𝔓) (hϖ0 : ϖ ≠ 0) : 𝔓 ∈ (Ideal.span {ϖ}).minimalPrimes := by
  haveI := hP
  haveI : 𝔓.FiniteHeight := Ideal.finiteHeight_iff_lt.mpr (Or.inr (by rw [hh]; exact ENat.one_lt_top))
  refine Ideal.mem_minimalPrimes_of_height_eq ((Ideal.span_singleton_le_iff_mem _).mpr hϖ) ?_
  rw [hh]
  exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖ0)

theorem coe_mem_chartAlgFin_of_mem {A : Type} [CommRing A] {L : Type} [Field L]
    (K' K : IntermediateField L (LaurentSeries L)) (hle : K' ≤ K) [Algebra A ↥K'] [Algebra A ↥K]
    (hcompat : ∀ a : A, ((algebraMap A ↥K a : ↥K) : LaurentSeries L) = ((algebraMap A ↥K' a : ↥K') : LaurentSeries L))
    (j' : ↥K') (j : ↥K) (hjj : ((j : ↥K) : LaurentSeries L) = ((j' : ↥K') : LaurentSeries L))
    (b : ↥K') (hb : b ∈ chartAlgFin A (↥K') j') :
    (IntermediateField.inclusion hle b) ∈ chartAlgFin A (↥K) j := by

  let ι : ↥K' →ₐ[A] ↥K :=
    { (IntermediateField.inclusion hle).toRingHom with
      commutes' := fun a => Subtype.ext (by
        show ((IntermediateField.inclusion hle (algebraMap A ↥K' a) : ↥K) : LaurentSeries L) = _
        rw [hcompat]; rfl) }
  have hιapp : ∀ x : ↥K', ι x = IntermediateField.inclusion hle x := fun x => rfl
  have hιj : ι j' = j := by rw [hιapp]; exact Subtype.ext hjj.symm

  have hmap : ∀ x : ↥(Algebra.adjoin A ({j'} : Set ↥K')), ι (x : ↥K') ∈ Algebra.adjoin A ({j} : Set ↥K) := by
    intro x
    have h1 : ι (x : ↥K') ∈ (Algebra.adjoin A ({j'} : Set ↥K')).map ι := Subalgebra.mem_map.mpr ⟨x, x.2, rfl⟩
    rwa [AlgHom.map_adjoin, Set.image_singleton, hιj] at h1
  let φ : ↥(Algebra.adjoin A ({j'} : Set ↥K')) →+* ↥(Algebra.adjoin A ({j} : Set ↥K)) :=
    ((ι.comp (Algebra.adjoin A ({j'} : Set ↥K')).val).codRestrict (Algebra.adjoin A ({j} : Set ↥K)) hmap).toRingHom
  show IsIntegral _ ((IntermediateField.inclusion hle).toRingHom (b : ↥K'))
  exact IsIntegral.map_of_comp_eq φ (IntermediateField.inclusion hle).toRingHom (by ext x; rfl) hb

section Gauss

variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L]

theorem gauss_mem_of_coeffMap (K : IntermediateField L (LaurentSeries L)) (O : ValuationSubring ↥K)
    (hO : ∀ f : ↥K, f ∈ O ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (g : LaurentSeries A) (f : ↥K) (hf : (f : LaurentSeries L) = coeffMap (algebraMap A L) g) : f ∈ O := by
  obtain ⟨x, d, hx⟩ := exists_mul_X_pow_eq_ofPowerSeries g
  rw [hO]
  refine ⟨x, PowerSeries.X ^ d, ?_, ?_⟩
  · rw [map_pow, PowerSeries.map_X]
    exact pow_ne_zero _ PowerSeries.X_ne_zero
  · rw [← coeffMap_ofPowerSeries, ← coeffMap_ofPowerSeries, hf, ← map_mul, hx]

theorem gauss_algebraMap_mem (K : IntermediateField L (LaurentSeries L)) (O : ValuationSubring ↥K)
    (hO : ∀ f : ↥K, f ∈ O ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (a : A) (f : ↥K) (hf : (f : LaurentSeries L) = algebraMap L (LaurentSeries L) (algebraMap A L a)) :
    f ∈ O :=
  gauss_mem_of_coeffMap K O hO (algebraMap A (LaurentSeries A) a) f (by rw [hf, coeffMap_algebraMap'])

theorem gauss_mem_nonunits (K : IntermediateField L (LaurentSeries L)) (O : ValuationSubring ↥K)
    (hO : ∀ f : ↥K, f ∈ O ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hinj : Function.Injective (algebraMap A L)) (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A)
    (f : ↥K) (hf : (f : LaurentSeries L) = algebraMap L (LaurentSeries L) (algebraMap A L a)) :
    f ∈ O.nonunits := by
  rw [mem_nonunits_iff']
  refine ⟨gauss_algebraMap_mem K O hO a f hf, ?_⟩
  by_cases ha0 : a = 0
  · left
    apply Subtype.ext
    rw [hf, ha0, map_zero, map_zero]
    rfl
  · right
    intro hinv
    rw [hO] at hinv
    obtain ⟨x, y, hy, hxy⟩ := hinv
    apply hy

    have hfL : ((f⁻¹ : ↥K) : LaurentSeries L) = (algebraMap L (LaurentSeries L) (algebraMap A L a))⁻¹ := by
      rw [← hf]; rfl
    have haL : algebraMap L (LaurentSeries L) (algebraMap A L a) ≠ 0 := by
      rw [algebraMap_LS_eq_single]
      exact HahnSeries.single_ne_zero ((map_ne_zero_iff _ hinj).mpr ha0)
    rw [hfL, inv_mul_eq_iff_eq_mul₀ haL] at hxy
    have hyx : y.map (algebraMap A L) = (PowerSeries.C a * x).map (algebraMap A L) := by
      apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
      rw [hxy, map_mul, PowerSeries.map_C, map_mul, HahnSeries.ofPowerSeries_C, algebraMap_LS_eq_single]
      rfl
    have hyx' : y = PowerSeries.C a * x := by
      ext n
      have := congrArg (PowerSeries.coeff n) hyx
      simp only [PowerSeries.coeff_map] at this
      exact hinj this
    rw [hyx', map_mul, PowerSeries.map_C, (IsLocalRing.residue_eq_zero_iff _).mpr ha, map_zero, zero_mul]

theorem gauss_aeval_mem_and_inv_mem (K : IntermediateField L (LaurentSeries L)) (O : ValuationSubring ↥K)
    (hO : ∀ f : ↥K, f ∈ O ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    [Algebra A ↥K] [IsScalarTower A L ↥K] [Algebra ℚ L] (hinj : Function.Injective (algebraMap A L))
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    (P : Polynomial A) (hP : P.map (IsLocalRing.residue A) ≠ 0) :
    Polynomial.aeval j P ∈ O ∧ (Polynomial.aeval j P)⁻¹ ∈ O := by
  classical

  set g : LaurentSeries A := Polynomial.aeval (jqModC A) P with hg
  have hjg : (j : LaurentSeries L) = coeffMap (algebraMap A L) (jqModC A) := by
    rw [hj, coeffMap_jqModC]
    show coeffMap (algebraMap ℚ L) jq = jqModC L
    rw [← jqModC_rat, coeffMap_jqModC]
  have hfg : ((Polynomial.aeval j P : ↥K) : LaurentSeries L) = coeffMap (algebraMap A L) g := by
    rw [hg, coeffMap_aeval, ← hjg, ← Polynomial.aeval_map_algebraMap L, ← IntermediateField.coe_val,
      ← Polynomial.aeval_algHom_apply]
  have hmem := gauss_mem_of_coeffMap K O hO g _ hfg
  refine ⟨hmem, ?_⟩

  have hgbar : coeffMap (IsLocalRing.residue A) g ≠ 0 := by
    rw [hg, coeffMap_aeval, coeffMap_jqModC]
    intro h0
    exact transcendental_jqModC (IsLocalRing.ResidueField A) ⟨P.map (IsLocalRing.residue A), hP, h0⟩
  obtain ⟨x, d, hx⟩ := exists_mul_X_pow_eq_ofPowerSeries g
  have hxbar : x.map (IsLocalRing.residue A) ≠ 0 := by
    intro h0
    apply hgbar
    have h1 := congrArg (coeffMap (IsLocalRing.residue A)) hx
    rw [map_mul, coeffMap_ofPowerSeries, coeffMap_ofPowerSeries, h0, map_zero, map_pow, PowerSeries.map_X,
      HahnSeries.ofPowerSeries_X_pow] at h1
    exact (mul_eq_zero.mp h1).resolve_right (by simp)
  rw [hO]
  refine ⟨PowerSeries.X ^ d, x, hxbar, ?_⟩
  have hf0 : ((Polynomial.aeval j P : ↥K) : LaurentSeries L) ≠ 0 := by
    rw [hfg]
    intro h0
    apply hgbar
    have : g = 0 := by
      ext k
      have := congrArg (fun s : LaurentSeries L => s.coeff k) h0
      simp only [coeffMap_coeff, HahnSeries.coeff_zero] at this
      exact (map_eq_zero_iff _ hinj).mp this
    rw [this, map_zero]
  have hxL := congrArg (coeffMap (algebraMap A L)) hx
  rw [map_mul, coeffMap_ofPowerSeries, coeffMap_ofPowerSeries, ← hfg] at hxL
  rw [show (((Polynomial.aeval j P)⁻¹ : ↥K) : LaurentSeries L) = (((Polynomial.aeval j P) : ↥K) : LaurentSeries L)⁻¹ from rfl,
    inv_mul_eq_iff_eq_mul₀ hf0]
  exact hxL.symm

end Gauss

end ModularCurve.O4Red

namespace FLR

open IsLocalRing

section GaussUnif

variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {L : Type} [Field L] [Algebra A L]

open ModularCurve.O4Eng ModularCurve.O4Red in

theorem gauss_nonunit_eq_mul
    (K : IntermediateField L (LaurentSeries L)) (O : ValuationSubring ↥K)
    (hO : ∀ f : ↥K, f ∈ O ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    [Algebra A ↥K] [IsScalarTower A L ↥K] (hinj : Function.Injective (algebraMap A L))
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (f : ↥K) (hf : f ∈ O.nonunits) :
    ∃ g : ↥K, g ∈ O ∧ f = algebraMap A ↥K ϖ * g := by
  classical
  have hϖ0 : ϖ ≠ 0 := fun h =>
    IsDiscreteValuationRing.not_a_field A (by rw [hϖ, Ideal.span_singleton_eq_bot]; exact h)
  have hϖL : algebraMap A L ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ0
  have hϖK : (algebraMap A ↥K ϖ : ↥K) ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A L ↥K]
    exact (map_ne_zero_iff _ (algebraMap L ↥K).injective).mpr hϖL
  have hϖKL : ((algebraMap A ↥K ϖ : ↥K) : LaurentSeries L) = algebraMap L (LaurentSeries L) (algebraMap A L ϖ) := by
    rw [IsScalarTower.algebraMap_apply A L ↥K]; rfl
  rw [mem_nonunits_iff'] at hf
  obtain ⟨hfO, hf⟩ := hf
  rcases hf with h0 | hinv
  · exact ⟨0, O.zero_mem, by rw [h0, mul_zero]⟩
  obtain ⟨x, y, hy, hxy⟩ := (hO f).mp hfO
  have hf0 : (f : LaurentSeries L) ≠ 0 := by
    intro h
    apply hinv
    have : f = 0 := Subtype.ext h
    rw [this, inv_zero]; exact O.zero_mem

  have hxbar : x.map (IsLocalRing.residue A) = 0 := by
    by_contra hx
    apply hinv
    rw [hO]
    refine ⟨y, x, hx, ?_⟩
    rw [show (((f⁻¹ : ↥K)) : LaurentSeries L) = ((f : ↥K) : LaurentSeries L)⁻¹ from rfl,
      inv_mul_eq_iff_eq_mul₀ hf0, hxy]

  have hcoef : ∀ n, ∃ c : A, c * ϖ = PowerSeries.coeff n x := by
    intro n
    have h1 : PowerSeries.coeff n (x.map (IsLocalRing.residue A)) = 0 := by rw [hxbar, map_zero]
    rw [PowerSeries.coeff_map, IsLocalRing.residue_eq_zero_iff, hϖ] at h1
    exact Ideal.mem_span_singleton'.mp h1
  choose c hc using hcoef
  set x₁ : PowerSeries A := PowerSeries.mk c with hx₁
  have hx : x = PowerSeries.C ϖ * x₁ := by
    ext n
    rw [PowerSeries.coeff_C_mul, hx₁, PowerSeries.coeff_mk, mul_comm, hc]
  refine ⟨(algebraMap A ↥K ϖ)⁻¹ * f, ?_, by rw [← mul_assoc, mul_inv_cancel₀ hϖK, one_mul]⟩
  rw [hO]
  refine ⟨x₁, y, hy, ?_⟩
  have hmul : ((((algebraMap A ↥K ϖ)⁻¹ * f : ↥K)) : LaurentSeries L) =
      (algebraMap L (LaurentSeries L) (algebraMap A L ϖ))⁻¹ * (f : LaurentSeries L) := by
    rw [← hϖKL]; rfl
  have hϖLS : algebraMap L (LaurentSeries L) (algebraMap A L ϖ) ≠ 0 := by
    rw [algebraMap_LS_eq_single]; exact HahnSeries.single_ne_zero hϖL
  rw [hmul, mul_assoc, hxy, hx, map_mul, PowerSeries.map_C, map_mul, HahnSeries.ofPowerSeries_C,
    inv_mul_eq_iff_eq_mul₀ hϖLS, algebraMap_LS_eq_single]
  rfl

end GaussUnif

section Generic

p2m_open "Algebra CategoryTheory.Algebra TensorProduct.Algebra"

theorem mem_span_of_mul_mem_span_of_free
    {O B : Type} [CommRing O] [IsDomain O] [CommRing B] [Algebra O B] [Module.Free O B] [Module.Finite O B]
    (ϖ r : O) [IsDomain (O ⧸ Ideal.span {ϖ})]
    (hr : Ideal.Quotient.mk (Ideal.span {ϖ}) r ≠ 0)
    (β : B) (h : algebraMap O B r * β ∈ Ideal.span {algebraMap O B ϖ}) :
    β ∈ Ideal.span {algebraMap O B ϖ} := by
  classical
  obtain ⟨β', hβ'⟩ := Ideal.mem_span_singleton'.mp h
  let bs := Module.Free.chooseBasis O B
  haveI : Finite (Module.Free.ChooseBasisIndex O B) := Module.Finite.finite_basis bs
  letI : Fintype (Module.Free.ChooseBasisIndex O B) := Fintype.ofFinite _
  have hsm : r • β = ϖ • β' := by
    rw [Algebra.smul_def, Algebra.smul_def, ← hβ', mul_comm]
  have hcoord : ∀ i, ∃ c : O, c * ϖ = bs.repr β i := by
    intro i
    have h1 : r * bs.repr β i = ϖ * bs.repr β' i := by
      have := congrArg (fun v => bs.repr v i) hsm
      simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using this
    have h2 : Ideal.Quotient.mk (Ideal.span {ϖ}) r * Ideal.Quotient.mk (Ideal.span {ϖ}) (bs.repr β i) = 0 := by
      rw [← map_mul, h1, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ), zero_mul]
    have h3 := (mul_eq_zero.mp h2).resolve_left hr
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h3
    exact h3
  choose c hc using hcoord
  refine Ideal.mem_span_singleton'.mpr ⟨∑ i, c i • bs i, ?_⟩
  rw [mul_comm, ← Algebra.smul_def, Finset.smul_sum]
  conv_rhs => rw [← bs.sum_repr β]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, mul_comm, hc]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem isUnramifiedAt_of_floor
    {R S : Type} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [IsNoetherianRing R] [Algebra R S]
    [Module.Finite R S] [FaithfulSMul R S] [IsIntegrallyClosed S]
    (p : Ideal R) [p.IsMaximal] (𝔓 : Ideal S) [𝔓.IsPrime] [𝔓.LiesOver p]
    (P : Ideal S) [P.IsPrime] (hPle : P ≤ 𝔓)
    (ϖ : R) (hϖ0 : ϖ ≠ 0) (hϖP : algebraMap R S ϖ ∈ P)
    (hreg : IsRegularLocalRing (Localization.AtPrime p))
    (hdim : ringKrullDim (Localization.AtPrime p) ≤ 2)
    (ϖO : Localization.AtPrime p) (hϖO : ϖO = algebraMap R (Localization.AtPrime p) ϖ)
    (hfreg : IsRegularLocalRing (Localization.AtPrime p ⧸ Ideal.span {ϖO}))
    (hfdim : ringKrullDim (Localization.AtPrime p ⧸ Ideal.span {ϖO}) = 1)
    (hfdom : IsDomain (Localization.AtPrime p ⧸ Ideal.span {ϖO}))
    (huniq : ∀ Q : Ideal S, Q.IsPrime → algebraMap R S ϖ ∈ Q → Q ≤ 𝔓 → P ≤ Q)
    (he : ∀ s ∈ P, ∃ a b : S, b ∉ P ∧ b * s = algebraMap R S ϖ * a)
    (hf : ∀ s : S, ∃ a b : R, b ∉ P.under R ∧ algebraMap R S b * s - algebraMap R S a ∈ P) :
    Algebra.IsUnramifiedAt R 𝔓 := by
  classical
  haveI : Algebra.FiniteType R S := inferInstance
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  letI algOC : Algebra (Localization.AtPrime p) (Localization.AtPrime 𝔓) :=
    (Localization.localRingHom p 𝔓 (algebraMap R S) Ideal.LiesOver.over).toAlgebra
  haveI : Localization.AtPrime.IsLiesOverAlgebra p 𝔓 := ⟨rfl⟩
  haveI hlochom : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime 𝔓)) := inferInstance
  haveI : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime 𝔓) := inferInstance
  set ϖS : S := algebraMap R S ϖ with hϖS
  set ϖC : Localization.AtPrime 𝔓 := algebraMap S (Localization.AtPrime 𝔓) ϖS with hϖC
  have hϖC_R : ϖC = algebraMap R (Localization.AtPrime 𝔓) ϖ := by
    rw [hϖC, hϖS, ← IsScalarTower.algebraMap_apply]
  have hϖC_O : ϖC = algebraMap (Localization.AtPrime p) (Localization.AtPrime 𝔓) ϖO := by
    rw [hϖO, ← IsScalarTower.algebraMap_apply, hϖC_R]
  have hp_over : p = 𝔓.under R := Ideal.LiesOver.over
  have hPunder_le : P.under R ≤ p := by rw [hp_over]; exact Ideal.comap_mono hPle
  have hϖp : ϖ ∈ p := hPunder_le (Ideal.mem_comap.mpr hϖP)
  have hϖCmax : ϖC ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔓) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ (hPle hϖP)
  have hspan_le_max : Ideal.span {ϖC} ≤ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔓) :=
    (Ideal.span_singleton_le_iff_mem _).mpr hϖCmax

  have hF1 : ∀ r : R, r ∉ P.under R →
      Ideal.Quotient.mk (Ideal.span {ϖO}) (algebraMap R (Localization.AtPrime p) r) ≠ 0 := by
    intro r hr h0
    apply hr
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h0
    obtain ⟨c, hc⟩ := h0
    obtain ⟨⟨a, u⟩, hu⟩ := IsLocalization.surj p.primeCompl c
    have h1 : algebraMap R (Localization.AtPrime p) (a * ϖ) = algebraMap R (Localization.AtPrime p) (r * ↑u) := by
      rw [map_mul, map_mul, ← hu, ← hc, hϖO]; ring
    obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists p.primeCompl _).mp h1
    have h2 : (t : R) * (r * ↑u) ∈ P.under R := by
      rw [← ht]; exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_comap.mpr hϖP))
    rcases Ideal.IsPrime.mem_or_mem inferInstance h2 with ht' | hru
    · exact absurd (hPunder_le ht') t.2
    rcases Ideal.IsPrime.mem_or_mem inferInstance hru with hr' | hu'
    · exact hr'
    · exact absurd (hPunder_le hu') u.2

  haveI := hfreg
  haveI := hfdom
  have hVR : ValuationRing (Localization.AtPrime p ⧸ Ideal.span {ϖO}) := by
    have h1 := (IsRegularLocalRing.iff_finrank_cotangentSpace _).mp hfreg
    rw [hfdim] at h1
    have h2 : Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime p ⧸ Ideal.span {ϖO}))
        (IsLocalRing.CotangentSpace (Localization.AtPrime p ⧸ Ideal.span {ϖO})) ≤ 1 := by
      have h3 : (Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime p ⧸ Ideal.span {ϖO}))
        (IsLocalRing.CotangentSpace (Localization.AtPrime p ⧸ Ideal.span {ϖO})) : WithBot ℕ∞) ≤ 1 := h1.le
      exact_mod_cast h3
    exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
      (Localization.AtPrime p ⧸ Ideal.span {ϖO})).out 5 1).mp h2
  haveI := hVR

  obtain ⟨hBfin, hBic, hBdom, hBfaith⟩ := L3_localization (A' := R) (B := S) p
  haveI := hBfin; haveI := hBic; haveI := hBdom; haveI := hBfaith; haveI := hreg
  haveI hBfree : Module.Free (Localization.AtPrime p) (Localization (algebraMapSubmonoid S p.primeCompl)) :=
    Module.free_of_isIntegrallyClosed_of_finite_of_isRegularLocalRing_of_ringKrullDim_le_two
      (Localization.AtPrime p) hdim (Localization (algebraMapSubmonoid S p.primeCompl))
  have hMB : algebraMapSubmonoid S p.primeCompl ≤ nonZeroDivisors S := by
    apply le_nonZeroDivisors_of_noZeroDivisors
    rintro ⟨a, ha, h0⟩
    have : a = 0 := (FaithfulSMul.algebraMap_injective R S) (by rw [h0, map_zero])
    exact ha (this ▸ p.zero_mem)
  have hBinj : Function.Injective (algebraMap S (Localization (algebraMapSubmonoid S p.primeCompl))) :=
    IsLocalization.injective _ hMB

  have hC_iff : ∀ s : S, algebraMap S (Localization.AtPrime 𝔓) s ∈ Ideal.span {ϖC} ↔
      ∃ s' w : S, w ∉ 𝔓 ∧ w * s = ϖS * s' := by
    intro s
    constructor
    · intro h
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
      obtain ⟨⟨a, u⟩, hu⟩ := IsLocalization.surj 𝔓.primeCompl c
      have h1 : algebraMap S (Localization.AtPrime 𝔓) (a * ϖS) = algebraMap S (Localization.AtPrime 𝔓) (↑u * s) := by
        rw [map_mul, map_mul, ← hu, ← hc]; ring
      obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists 𝔓.primeCompl _).mp h1
      refine ⟨↑t * a, ↑t * ↑u, ?_, ?_⟩
      · intro hmem
        rcases Ideal.IsPrime.mem_or_mem inferInstance hmem with h | h
        · exact t.2 h
        · exact u.2 h
      · calc ↑t * ↑u * s = ↑t * (↑u * s) := by ring
          _ = ↑t * (a * ϖS) := ht.symm
          _ = ϖS * (↑t * a) := by ring
    · rintro ⟨s', w, hw, hws⟩
      have hwu : IsUnit (algebraMap S (Localization.AtPrime 𝔓) w) := IsLocalization.map_units _ (⟨w, hw⟩ : 𝔓.primeCompl)
      refine Ideal.mem_span_singleton'.mpr ⟨algebraMap S _ s' * ↑(hwu.unit⁻¹), ?_⟩
      have h1 : algebraMap S (Localization.AtPrime 𝔓) w * algebraMap S _ s = ϖC * algebraMap S _ s' := by
        rw [← map_mul, hws, map_mul]
      calc algebraMap S _ s' * ↑(hwu.unit⁻¹) * ϖC
          = ↑(hwu.unit⁻¹) * (ϖC * algebraMap S _ s') := by ring
        _ = ↑(hwu.unit⁻¹) * (algebraMap S _ w * algebraMap S _ s) := by rw [h1]
        _ = ↑(hwu.unit⁻¹) * ↑(hwu.unit) * algebraMap S _ s := by rw [IsUnit.unit_spec]; ring
        _ = algebraMap S _ s := by rw [Units.inv_mul, one_mul]

  have hT : ∀ r : R, r ∉ P.under R → ∀ s : S,
      (∃ s' w : S, w ∉ 𝔓 ∧ w * (algebraMap R S r * s) = ϖS * s') → (∃ s' w : S, w ∉ 𝔓 ∧ w * s = ϖS * s') := by
    intro r hr s ⟨s', w, hw, hws⟩
    have h1 : algebraMap (Localization.AtPrime p) (Localization (algebraMapSubmonoid S p.primeCompl))
          (algebraMap R (Localization.AtPrime p) r) * algebraMap S _ (w * s) ∈
        Ideal.span {algebraMap (Localization.AtPrime p) (Localization (algebraMapSubmonoid S p.primeCompl)) ϖO} := by
      rw [hϖO, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply R S (Localization (algebraMapSubmonoid S p.primeCompl)),
        IsScalarTower.algebraMap_apply R S (Localization (algebraMapSubmonoid S p.primeCompl)), ← map_mul]
      refine Ideal.mem_span_singleton'.mpr ⟨algebraMap S _ s', ?_⟩
      rw [← map_mul, ← hϖS, mul_comm s' ϖS, ← hws]
      congr 1; ring
    have h2 := FLR.mem_span_of_mul_mem_span_of_free ϖO (algebraMap R _ r) (hF1 r hr) _ h1
    rw [hϖO, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R S (Localization (algebraMapSubmonoid S p.primeCompl))] at h2
    obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton'.mp h2
    obtain ⟨⟨b, v⟩, hv⟩ := IsLocalization.surj (algebraMapSubmonoid S p.primeCompl) β
    have h3 : algebraMap S (Localization (algebraMapSubmonoid S p.primeCompl)) (b * ϖS) =
        algebraMap S _ (↑v * (w * s)) := by
      rw [map_mul, map_mul, ← hv, ← hβ, hϖS]; ring
    have h4 : b * ϖS = ↑v * (w * s) := hBinj h3
    obtain ⟨v0, hv0, hv0eq⟩ := Submonoid.mem_map.mp v.2
    refine ⟨b, ↑v * w, ?_, ?_⟩
    · intro hmem
      rcases Ideal.IsPrime.mem_or_mem inferInstance hmem with h | h
      · rw [← hv0eq] at h
        have : v0 ∈ p := by rw [hp_over]; exact Ideal.mem_comap.mpr h
        exact hv0 this
      · exact hw h
    · calc ↑v * w * s = ↑v * (w * s) := by ring
        _ = b * ϖS := h4.symm
        _ = ϖS * b := by ring
  have hTC : ∀ r : R, r ∉ P.under R → ∀ x : Localization.AtPrime 𝔓,
      algebraMap R (Localization.AtPrime 𝔓) r * x ∈ Ideal.span {ϖC} → x ∈ Ideal.span {ϖC} := by
    intro r hr x hx
    obtain ⟨⟨s', u⟩, hu⟩ := IsLocalization.surj 𝔓.primeCompl x
    have h1 : algebraMap S (Localization.AtPrime 𝔓) (algebraMap R S r * s') ∈ Ideal.span {ϖC} := by
      rw [map_mul, ← IsScalarTower.algebraMap_apply, ← hu, ← mul_assoc]
      exact Ideal.mul_mem_right _ _ hx
    have h3 : algebraMap S (Localization.AtPrime 𝔓) s' ∈ Ideal.span {ϖC} :=
      (hC_iff s').mpr (hT r hr s' ((hC_iff _).mp h1))
    have huu : IsUnit (algebraMap S (Localization.AtPrime 𝔓) u) := IsLocalization.map_units _ u
    have : x = algebraMap S _ s' * ↑(huu.unit⁻¹) := by
      rw [← hu, mul_assoc, IsUnit.mul_val_inv, mul_one]
    rw [this]; exact Ideal.mul_mem_right _ _ h3

  have hA : ∀ s ∈ P, algebraMap S (Localization.AtPrime 𝔓) s ∈ Ideal.span {ϖC} := by
    intro s hs
    obtain ⟨a, b, hb, hbs⟩ := he s hs
    by_contra hnot
    have hm : (Ideal.Quotient.mk (Ideal.span {ϖC}) (algebraMap S _ s)) ≠ 0 := by
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    haveI : IsNoetherianRing (Localization.AtPrime 𝔓) :=
      IsLocalization.isNoetherianRing 𝔓.primeCompl _ inferInstance
    obtain ⟨Q, hQass, hQcolon⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing (Localization.AtPrime 𝔓)
      (Ideal.Quotient.mk (Ideal.span {ϖC}) (algebraMap S _ s)) hm
    obtain ⟨hQpr, m', hQeq⟩ := isAssociatedPrime_iff.mp hQass
    haveI := hQpr
    have hQmem : ∀ x : Localization.AtPrime 𝔓, x ∈ Q ↔ x • m' = 0 := by
      intro x; rw [hQeq, Submodule.mem_colon_singleton, Submodule.mem_bot]
    have hbQ : algebraMap S _ b ∈ Q := by
      apply hQcolon
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
      change Ideal.Quotient.mk (Ideal.span {ϖC}) (algebraMap S _ b * algebraMap S _ s) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, ← map_mul, hbs, map_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    have hm'ne : m' ≠ 0 := by
      intro h0; apply hQpr.ne_top; rw [Submodule.eq_top_iff']; intro x; rw [hQmem, h0, smul_zero]
    have hϖQ : ϖC ∈ Q := by
      rw [hQmem]
      obtain ⟨c', hc'⟩ := Ideal.Quotient.mk_surjective m'
      rw [← hc']
      change Ideal.Quotient.mk (Ideal.span {ϖC}) (ϖC * c') = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    have hQR : Q.under R ≤ P.under R := by
      intro r hr
      by_contra hrP
      apply hm'ne
      obtain ⟨c', hc'⟩ := Ideal.Quotient.mk_surjective m'
      have hr' : algebraMap R (Localization.AtPrime 𝔓) r • m' = 0 := (hQmem _).mp (Ideal.mem_comap.mp hr)
      rw [← hc'] at hr'
      change Ideal.Quotient.mk (Ideal.span {ϖC}) (algebraMap R (Localization.AtPrime 𝔓) r * c') = 0 at hr'
      rw [Ideal.Quotient.eq_zero_iff_mem] at hr'
      rw [← hc', Ideal.Quotient.eq_zero_iff_mem]
      exact hTC r hrP _ hr'
    have hQS_le : Q.under S ≤ 𝔓 := by
      intro x hx
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔓) 𝔓 x).mp
        (IsLocalRing.le_maximalIdeal hQpr.ne_top (Ideal.mem_comap.mp hx))
    have hPQ : P ≤ Q.under S := huniq _ inferInstance (Ideal.mem_comap.mpr hϖQ) hQS_le
    have hQSR : (Q.under S).under R = Q.under R := Ideal.under_under (B := S) Q
    have hPeq : P = Q.under S := by
      by_contra hne
      have hlt : P < Q.under S := lt_of_le_of_ne hPQ hne
      obtain ⟨x, hxQ, hxP⟩ := SetLike.exists_of_lt hlt
      have h1 := Ideal.comap_lt_comap_of_integral_mem_sdiff (R := R) hPQ ⟨hxQ, hxP⟩ (Algebra.IsIntegral.isIntegral x)
      have h2 : Ideal.comap (algebraMap R S) (Q.under S) = Q.under R := hQSR
      rw [h2] at h1
      exact absurd (lt_of_lt_of_le h1 hQR) (lt_irrefl _)
    apply hb
    rw [hPeq]; exact Ideal.mem_comap.mpr hbQ

  have htrans : ∀ x y : Localization.AtPrime p,
      Ideal.Quotient.mk (Ideal.span {ϖO}) x = Ideal.Quotient.mk (Ideal.span {ϖO}) y →
        algebraMap _ (Localization.AtPrime 𝔓) x - algebraMap _ _ y ∈ Ideal.span {ϖC} := by
    intro x y hxy
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hxy
    obtain ⟨d, hd⟩ := hxy
    refine Ideal.mem_span_singleton'.mpr ⟨algebraMap _ _ d, ?_⟩
    rw [hϖC_O, ← map_mul, hd, map_sub]

  have hB : ∀ s : S, ∃ o : Localization.AtPrime p,
      algebraMap S (Localization.AtPrime 𝔓) s - algebraMap _ _ o ∈ Ideal.span {ϖC} := by
    intro s
    obtain ⟨a, b, hb, habs⟩ := hf s
    have h0 := hA _ habs
    rw [map_sub, map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R (Localization.AtPrime p) (Localization.AtPrime 𝔓) b,
      IsScalarTower.algebraMap_apply R (Localization.AtPrime p) (Localization.AtPrime 𝔓) a] at h0
    obtain ⟨c, hc⟩ := ValuationRing.cond (Ideal.Quotient.mk (Ideal.span {ϖO}) (algebraMap R _ a))
      (Ideal.Quotient.mk (Ideal.span {ϖO}) (algebraMap R _ b))
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [← map_mul, ← map_mul] at hc
    rcases hc with hc | hc
    ·
      by_cases haP : a ∈ P.under R
      · refine ⟨0, ?_⟩
        rw [map_zero, sub_zero]
        apply hA
        have h1 : algebraMap R S b * s ∈ P := by
          have := P.add_mem habs (Ideal.mem_comap.mp haP)
          simpa using this
        exact (Ideal.IsPrime.mem_or_mem inferInstance h1).resolve_left hb
      · have h1 := htrans _ _ hc
        rw [map_mul] at h1
        have h2 : algebraMap _ (Localization.AtPrime 𝔓) (algebraMap R (Localization.AtPrime p) a) *
            (algebraMap _ _ c * algebraMap S _ s - 1) ∈ Ideal.span {ϖC} := by
          have : algebraMap _ (Localization.AtPrime 𝔓) (algebraMap R (Localization.AtPrime p) a) *
              (algebraMap _ _ c * algebraMap S _ s - 1) =
            (algebraMap _ _ (algebraMap R (Localization.AtPrime p) a) * algebraMap _ _ c -
                algebraMap _ _ (algebraMap R (Localization.AtPrime p) b)) * algebraMap S _ s +
            (algebraMap _ _ (algebraMap R (Localization.AtPrime p) b) * algebraMap S _ s -
                algebraMap _ _ (algebraMap R (Localization.AtPrime p) a)) := by ring
          rw [this]; exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h1) h0
        rw [← IsScalarTower.algebraMap_apply] at h2
        have h3 := hTC a haP _ h2
        by_cases hcu : IsUnit c
        · refine ⟨↑(hcu.unit⁻¹), ?_⟩
          have : algebraMap S (Localization.AtPrime 𝔓) s - algebraMap _ _ (↑(hcu.unit⁻¹) : Localization.AtPrime p) =
              algebraMap _ _ (↑(hcu.unit⁻¹) : Localization.AtPrime p) * (algebraMap _ _ c * algebraMap S _ s - 1) := by
            rw [mul_sub, mul_one, ← mul_assoc, ← map_mul, IsUnit.val_inv_mul, map_one, one_mul]
          rw [this]; exact Ideal.mul_mem_left _ _ h3
        · exfalso
          apply (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime 𝔓)).ne_top
          rw [Ideal.eq_top_iff_one]
          have h4 : algebraMap _ (Localization.AtPrime 𝔓) c * algebraMap S _ s ∈ IsLocalRing.maximalIdeal _ := by
            refine Ideal.mul_mem_right _ _ ?_
            rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
            exact fun hu => hcu ((isUnit_map_iff (algebraMap _ _) c).mp hu)
          have h5 := Ideal.sub_mem _ h4 (hspan_le_max h3)
          rwa [sub_sub_cancel] at h5
    ·
      have h1 := htrans _ _ hc
      rw [map_mul] at h1
      refine ⟨c, hTC b hb _ ?_⟩
      have : algebraMap R (Localization.AtPrime 𝔓) b * (algebraMap S _ s - algebraMap _ _ c) =
        (algebraMap _ _ (algebraMap R (Localization.AtPrime p) b) * algebraMap S _ s -
            algebraMap _ _ (algebraMap R (Localization.AtPrime p) a)) -
        (algebraMap _ _ (algebraMap R (Localization.AtPrime p) b) * algebraMap _ _ c -
            algebraMap _ _ (algebraMap R (Localization.AtPrime p) a)) := by
        rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime p) (Localization.AtPrime 𝔓) b]; ring
      rw [this]; exact Ideal.sub_mem _ h0 h1

  have hB' : ∀ x : Localization.AtPrime 𝔓, ∃ o : Localization.AtPrime p,
      x - algebraMap _ _ o ∈ Ideal.span {ϖC} := by
    intro x
    obtain ⟨⟨s, u⟩, hu⟩ := IsLocalization.surj 𝔓.primeCompl x
    obtain ⟨os, hos⟩ := hB s
    obtain ⟨ou, hou⟩ := hB u
    have huC : IsUnit (algebraMap S (Localization.AtPrime 𝔓) u) := IsLocalization.map_units _ u
    have houu : IsUnit ou := by
      refine (isUnit_map_iff (algebraMap (Localization.AtPrime p) (Localization.AtPrime 𝔓)) ou).mp ?_
      by_contra hnu
      have h1 : algebraMap _ (Localization.AtPrime 𝔓) ou ∈ IsLocalRing.maximalIdeal _ :=
        (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
      have h2 : algebraMap S (Localization.AtPrime 𝔓) (u : S) ∈ IsLocalRing.maximalIdeal _ := by
        have := Ideal.add_mem _ h1 (hspan_le_max hou)
        rwa [add_sub_cancel] at this
      exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h2)) huC
    refine ⟨os * ↑(houu.unit⁻¹), ?_⟩
    have e1 : Ideal.Quotient.mk (Ideal.span {ϖC}) x * Ideal.Quotient.mk (Ideal.span {ϖC}) (algebraMap _ _ ou) =
        Ideal.Quotient.mk (Ideal.span {ϖC}) (algebraMap _ _ os) := by
      rw [← (Ideal.Quotient.eq (I := Ideal.span {ϖC})).mpr hou, ← (Ideal.Quotient.eq (I := Ideal.span {ϖC})).mpr hos,
        ← map_mul, hu]
    refine (Ideal.Quotient.eq (I := Ideal.span {ϖC})).mp ?_
    rw [map_mul, map_mul, ← e1, mul_assoc, ← map_mul (Ideal.Quotient.mk (Ideal.span {ϖC})),
      ← map_mul (algebraMap (Localization.AtPrime p) (Localization.AtPrime 𝔓)), IsUnit.mul_val_inv, map_one,
      map_one, mul_one]

  refine (Algebra.isUnramifiedAt_iff_map_eq R p 𝔓).mpr ⟨?_, ?_⟩
  · have hsurj : Function.Surjective (algebraMap p.ResidueField 𝔓.ResidueField) := by
      intro z
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
      obtain ⟨o, ho⟩ := hB' x
      refine ⟨IsLocalRing.residue _ o, ?_⟩
      rw [IsLocalRing.ResidueField.algebraMap_residue]
      have h1 : IsLocalRing.residue _ (algebraMap _ (Localization.AtPrime 𝔓) o) - IsLocalRing.residue _ x = 0 := by
        rw [← map_sub, IsLocalRing.residue_eq_zero_iff, ← neg_sub, neg_mem_iff]
        exact hspan_le_max ho
      exact sub_eq_zero.mp h1
    exact ⟨fun z => by obtain ⟨w, rfl⟩ := hsurj z; exact isSeparable_algebraMap w⟩
  · apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      have h1 : algebraMap R S r ∈ 𝔓 := by rw [hp_over] at hr; exact Ideal.mem_comap.mp hr
      rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply R S (Localization.AtPrime 𝔓),
        ← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ h1
    · intro x hx
      obtain ⟨o, ho⟩ := hB' x
      have hoC : algebraMap _ (Localization.AtPrime 𝔓) o ∈ IsLocalRing.maximalIdeal _ := by
        have := Ideal.sub_mem _ hx (hspan_le_max ho)
        rwa [sub_sub_cancel] at this
      have hom : o ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hoC)) (hu.map _)
      rw [← Localization.AtPrime.map_eq_maximalIdeal] at hom
      have h1 : algebraMap _ (Localization.AtPrime 𝔓) o ∈ p.map (algebraMap R (Localization.AtPrime 𝔓)) := by
        rw [IsScalarTower.algebraMap_eq R (Localization.AtPrime p) (Localization.AtPrime 𝔓), ← Ideal.map_map]
        exact Ideal.mem_map_of_mem _ hom
      have h2 : ϖC ∈ p.map (algebraMap R (Localization.AtPrime 𝔓)) := by
        rw [hϖC_R]; exact Ideal.mem_map_of_mem _ hϖp
      have h3 : Ideal.span {ϖC} ≤ p.map (algebraMap R (Localization.AtPrime 𝔓)) :=
        (Ideal.span_singleton_le_iff_mem _).mpr h2
      have h4 : x = (x - algebraMap _ _ o) + algebraMap _ _ o := by ring
      rw [h4]; exact Ideal.add_mem _ (h3 ho) h1

end Generic

end FLR

set_option maxHeartbeats 25600000 in
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
    (hfloor : Smooth (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K₀) j₀))

    (K₀' : IntermediateField L (LaurentSeries L))
    (hK₀' : K₀' = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q * M'))))
    (hle₀' : K₀ ≤ K₀') (hle' : K₀' ≤ K)
    [Algebra A ↥K₀'] [IsScalarTower A L ↥K₀']
    (j₀' : ↥K₀') (hj₀' : ((j₀' : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₀' ≠ 0)]
    (ι₀' : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀'))
    (hι₀' : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀), ((ι₀' b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀')) : ↥K₀') = IntermediateField.inclusion hle₀' (b : ↥K₀))
    (ι' : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀') →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
    (hι' : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀'), ((ι' b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = IntermediateField.inclusion hle' (b : ↥K₀'))
    (hιι : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀), ι b = ι' (ι₀' b)) :
    letI : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀') := ι₀'.toAlgebra
    haveI : ((y.asIdeal).comap ι').IsPrime := Ideal.IsPrime.comap ι'
    Algebra.IsUnramifiedAt ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ((y.asIdeal).comap ι') := by
  classical
  letI algRS : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀') := ι₀'.toAlgebra
  haveI h𝔓pr : ((y.asIdeal).comap ι').IsPrime := Ideal.IsPrime.comap ι'
  show Algebra.IsUnramifiedAt ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ((y.asIdeal).comap ι')
  letI algST : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀') ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := ι'.toAlgebra
  letI algRT : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := ι.toAlgebra
  haveI := hmax

  haveI : (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')).FiniteIndex :=
    OrdRegPort.GammaH_finiteIndex _ _
  have hT : ModularGroup.T ∈ CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :=
    ModularCurve.translation_mem_GammaH _ _
  have hK' : K = ModularCurve.laurentBaseChange L
      (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))) := hK
  haveI hFD := ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
    (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) hT L K hK' j hj
  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  have hT₀ : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 M' := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.T]
  haveI hFD₀ := ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
    (CongruenceSubgroup.Gamma0 M') hT₀ L K₀ hK₀ j₀ hj₀
  have htj₀ : Transcendental A j₀ := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₀ A j₀ hj₀
  haveI : NeZero (q * M') := ⟨mul_ne_zero (Fact.out : q.Prime).ne_zero (NeZero.ne M')⟩
  have hT₀' : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 (q * M') := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.T]
  haveI : (CongruenceSubgroup.Gamma0 (q * M')).FiniteIndex := by
    rw [← CohCarrier.GammaH_top]; exact Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH _ _)
  haveI hFD₀' := ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
    (CongruenceSubgroup.Gamma0 (q * M')) hT₀' L K₀' hK₀' j₀' hj₀'
  have htj₀' : Transcendental A j₀' := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₀' A j₀' hj₀'
  haveI hsep₀' : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j₀'} : Set ↥K₀')) ↥K₀' :=
    Algebra.IsSeparable.of_integral _ _
  haveI hsep₀ : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ :=
    Algebra.IsSeparable.of_integral _ _
  have hjj₀' : ((IntermediateField.inclusion hle₀') j₀ : ↥K₀') = j₀' :=
    Subtype.ext (show ((j₀ : ↥K₀) : LaurentSeries L) = (j₀' : LaurentSeries L) by rw [hj₀, hj₀'])
  have hjj' : ((IntermediateField.inclusion hle') j₀' : ↥K) = j :=
    Subtype.ext (show ((j₀' : ↥K₀') : LaurentSeries L) = (j : LaurentSeries L) by rw [hj₀', hj])
  have hinjAL : Function.Injective (algebraMap A L) := IsFractionRing.injective A L

  haveI : IsScalarTower A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀') := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    apply Subtype.ext
    show ((algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀') a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀')) : ↥K₀') = ((ι₀' (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) a)) : ↥K₀')
    rw [hι₀']
    apply Subtype.ext
    show ((algebraMap A ↥K₀' a) : LaurentSeries L) = ((algebraMap A ↥K₀ a : ↥K₀) : LaurentSeries L)
    rw [IsScalarTower.algebraMap_apply A L ↥K₀', IsScalarTower.algebraMap_apply A L ↥K₀]
    rfl
  haveI : IsScalarTower A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    apply Subtype.ext
    show ((algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = ((ι (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) a)) : ↥K)
    rw [hι]
    apply Subtype.ext
    show ((algebraMap A ↥K a) : LaurentSeries L) = ((algebraMap A ↥K₀ a : ↥K₀) : LaurentSeries L)
    rw [IsScalarTower.algebraMap_apply A L ↥K, IsScalarTower.algebraMap_apply A L ↥K₀]
    rfl
  haveI : IsScalarTower ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀') ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := IsScalarTower.of_algebraMap_eq (fun b => hιι b)

  haveI hfinRS : Module.Finite ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀') :=
    OrdRegAux.finite_chartAlgFin_of_floor A L K₀' K₀ hle₀' j₀' j₀ hjj₀' htj₀' hFD₀' (fun b => hι₀' b)
  have hjj : ((IntermediateField.inclusion hle₀) j₀ : ↥K) = j :=
    Subtype.ext (show ((j₀ : ↥K₀) : LaurentSeries L) = (j : LaurentSeries L) by rw [hj₀, hj])
  haveI hfinRT : Module.Finite ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) :=
    OrdRegAux.finite_chartAlgFin_of_floor A L K K₀ hle₀ j j₀ hjj htj hFD (fun b => hι b)
  have hι₀'inj : Function.Injective ι₀' := by
    intro a b hab
    have h := congrArg (fun z : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀') => (z : ↥K₀')) hab
    simp only [hι₀'] at h
    exact Subtype.ext ((IntermediateField.inclusion hle₀').injective h)
  haveI : FaithfulSMul ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀') := (faithfulSMul_iff_algebraMap_injective _ _).mpr hι₀'inj
  haveI : IsNoetherianRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) := by
    obtain ⟨hft, -⟩ := AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K₀) j₀ htj₀ hFD₀ inferInstance
    exact Algebra.FiniteType.isNoetherianRing A _
  haveI : IsIntegrallyClosed ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀') := AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg A (↥K₀') _

  have hp' : (((y.asIdeal).comap ι').under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀)) = (y.asIdeal).under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) := by
    rw [Ideal.under_def, Ideal.under_def, Ideal.comap_comap]
    congr 1
    exact RingHom.ext fun b => (hιι b).symm
  haveI hpmax : (((y.asIdeal).comap ι').under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀)).IsMaximal := by
    rw [hp']; exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal y.asIdeal
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal A := by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_isField A
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hϖ, h0, Ideal.span_singleton_eq_bot]
  have hϖW₀ : ((algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) ∈ W₀.nonunits := by
    refine ModularCurve.O4Red.gauss_mem_nonunits K W₀ hW₀ hinjAL ϖ hϖm _ ?_
    show ((algebraMap A ↥K ϖ : ↥K) : LaurentSeries L) = _
    rw [IsScalarTower.algebraMap_apply A L ↥K]
    rfl
  have hϖy : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∈ y.asIdeal := hz₀ _ hϖW₀
  have hϖp : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ϖ ∈ (((y.asIdeal).comap ι').under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀)) := by
    rw [hp', Ideal.under_def, Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]; exact hϖy
  have hϖR0 : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ϖ ≠ 0 := by
    intro h0
    apply hϖ0
    apply hinjAL
    have h1 := congrArg (fun b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) => ((b : ↥K₀) : LaurentSeries L)) h0
    simp only [ZeroMemClass.coe_zero] at h1
    have h2 : ((algebraMap A ↥K₀ ϖ : ↥K₀) : LaurentSeries L) = 0 := h1
    rw [IsScalarTower.algebraMap_apply A L ↥K₀] at h2
    have h3 : algebraMap L (LaurentSeries L) (algebraMap A L ϖ) = 0 := h2
    rw [map_eq_zero] at h3
    rw [h3, map_zero]

  obtain ⟨hRreg, hRdim, hRfib, hRfib1, hRdom⟩ :=
    OrdRegL2.L2_floor_regular_of_smooth L K₀ A j₀ htj₀ hFD₀ hfloor ϖ hϖ (((y.asIdeal).comap ι').under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀)) hϖp

  obtain ⟨O₀', hO₀'def⟩ : ∃ O : ValuationSubring ↥K₀', O = W₀.comap (IntermediateField.inclusion hle').toRingHom := ⟨_, rfl⟩
  obtain ⟨O₀, hO₀def⟩ : ∃ O : ValuationSubring ↥K₀, O = W₀.comap (IntermediateField.inclusion hle₀).toRingHom := ⟨_, rfl⟩
  have hO₀' : ∀ f : ↥K₀', f ∈ O₀' ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) := fun f => by
    rw [hO₀'def, ValuationSubring.mem_comap, hW₀]; exact Iff.rfl
  have hO₀ : ∀ f : ↥K₀, f ∈ O₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) := fun f => by
    rw [hO₀def, ValuationSubring.mem_comap, hW₀]; exact Iff.rfl
  have hO₀O₀' : ∀ f : ↥K₀, (IntermediateField.inclusion hle₀') f ∈ O₀' ↔ f ∈ O₀ := fun f => by rw [hO₀, hO₀']; exact Iff.rfl
  have hOA' : ∀ a : A, algebraMap A ↥K₀' a ∈ O₀' := fun a =>
    ModularCurve.O4Red.gauss_algebraMap_mem K₀' O₀' hO₀' a _ (by rw [IsScalarTower.algebraMap_apply A L ↥K₀']; rfl)
  have hOm' : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K₀' a ∈ O₀'.nonunits := fun a ha =>
    ModularCurve.O4Red.gauss_mem_nonunits K₀' O₀' hO₀' hinjAL a ha _ (by rw [IsScalarTower.algebraMap_apply A L ↥K₀']; rfl)
  have hOj' : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j₀' P ∈ O₀' ∧ (Polynomial.aeval j₀' P)⁻¹ ∈ O₀' :=
    fun P hP => ModularCurve.O4Red.gauss_aeval_mem_and_inv_mem K₀' O₀' hO₀' hinjAL j₀' hj₀' P hP
  have hOA₀ : ∀ a : A, algebraMap A ↥K₀ a ∈ O₀ := fun a =>
    ModularCurve.O4Red.gauss_algebraMap_mem K₀ O₀ hO₀ a _ (by rw [IsScalarTower.algebraMap_apply A L ↥K₀]; rfl)
  have hOm₀ : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K₀ a ∈ O₀.nonunits := fun a ha =>
    ModularCurve.O4Red.gauss_mem_nonunits K₀ O₀ hO₀ hinjAL a ha _ (by rw [IsScalarTower.algebraMap_apply A L ↥K₀]; rfl)
  have hOj₀ : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j₀ P ∈ O₀ ∧ (Polynomial.aeval j₀ P)⁻¹ ∈ O₀ :=
    fun P hP => ModularCurve.O4Red.gauss_aeval_mem_and_inv_mem K₀ O₀ hO₀ hinjAL j₀ hj₀ P hP
  obtain ⟨hSO, ⟨P, hPpr, hPht, hPmem, hPmax, hPloc⟩, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
      A L (↥K₀') j₀' htj₀' hFD₀' hsep₀' O₀' hOA' hOm' hOj'
  obtain ⟨hRO, ⟨P₀, hP₀pr, hP₀ht, hP₀mem, hP₀max, hP₀loc⟩, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
      A L (↥K₀) j₀ htj₀ hFD₀ hsep₀ O₀ hOA₀ hOm₀ hOj₀
  haveI := hPpr
  haveI := hP₀pr

  have hPle : P ≤ ((y.asIdeal).comap ι') := by
    intro b hb
    rw [Ideal.mem_comap]
    apply hz₀
    rw [hι']
    have h1 := (hPmem b).mp hb
    rw [hO₀'def] at h1
    exact (ModularCurve.O4Red.mem_nonunits_comap_iff W₀ (IntermediateField.inclusion hle').toRingHom (b : ↥K₀')).mp h1

  have hPunder : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀), b ∈ P.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↔ b ∈ P₀ := by
    intro b
    rw [Ideal.under_def, Ideal.mem_comap, hPmem, hP₀mem]
    show ((ι₀' b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀')) : ↥K₀') ∈ O₀'.nonunits ↔ (b : ↥K₀) ∈ O₀.nonunits
    rw [hι₀', hO₀'def, hO₀def, ModularCurve.O4Red.mem_nonunits_comap_iff, ModularCurve.O4Red.mem_nonunits_comap_iff]
    exact Iff.rfl

  have hϖS : algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀') (algebraMap A _ ϖ) = algebraMap A _ ϖ := (IsScalarTower.algebraMap_apply A _ _ ϖ).symm
  have hϖP : algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀') (algebraMap A _ ϖ) ∈ P := by rw [hϖS]; exact hPmax ϖ hϖm
  have hϖS0 : (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀') ϖ) ≠ 0 := by
    intro h0
    apply hϖ0
    apply hinjAL
    have h1 := congrArg (fun b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀') => ((b : ↥K₀') : LaurentSeries L)) h0
    simp only [ZeroMemClass.coe_zero] at h1
    have h2 : ((algebraMap A ↥K₀' ϖ : ↥K₀') : LaurentSeries L) = 0 := h1
    rw [IsScalarTower.algebraMap_apply A L ↥K₀'] at h2
    have h3 : algebraMap L (LaurentSeries L) (algebraMap A L ϖ) = 0 := h2
    rw [map_eq_zero] at h3
    rw [h3, map_zero]

  have hιj : ι' (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K₀') j₀') = AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j := by
    apply Subtype.ext
    rw [hι', AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin, AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin]
    exact hjj'
  have hK₂ : K₀' = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M' * q))) := by
    rw [Nat.mul_comm]; exact hK₀'
  have hφ' : RingHom.ker (φ.comp ι') = ((y.asIdeal).comap ι') := by
    rw [← RingHom.comap_ker, hφ]
  have huniq : ∀ Q : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀'), Q.IsPrime → algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀') (algebraMap A _ ϖ) ∈ Q → Q ≤ ((y.asIdeal).comap ι') → P ≤ Q := by
    intro Q hQ hϖQ hQle
    haveI := hQ
    rw [hϖS] at hϖQ
    obtain ⟨Q₀, hQ₀min, hQ₀le⟩ := Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem Q).mpr hϖQ)
    have hPmin := ModularCurve.O4Red.mem_minimalPrimes_of_height_eq_one P hPpr hPht _ (hPmax ϖ hϖm) hϖS0
    by_cases hPQ : P = Q₀
    · rw [hPQ]; exact hQ₀le
    · exfalso
      apply hord
      have hss := ModularCurve.FullLevel.map_jChartFin_mem_ssJSet_of_exists_two_minimalPrimes_span_le_chartAlgFin_laurentBaseChange_gamma0_mul
        q M' hqM' L K₀' hK₂ A hAq j₀' hj₀' ϖ hϖ ((y.asIdeal).comap ι') (by rw [← hϖS]; exact hPle hϖP)
        ⟨P, hPmin, Q₀, hQ₀min, hPQ, hPle, hQ₀le.trans hQle⟩ Ω (φ.comp ι') hφ'
      rwa [RingHom.comp_apply, hιj] at hss

  have he : ∀ s ∈ P, ∃ a b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀'), b ∉ P ∧ b * s = algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀') (algebraMap A _ ϖ) * a := by
    intro s hs
    obtain ⟨g, hgO, hg⟩ := FLR.gauss_nonunit_eq_mul K₀' O₀' hO₀' hinjAL ϖ hϖ (s : ↥K₀') ((hPmem s).mp hs)
    obtain ⟨a, b, hb, hab⟩ := (hPloc g).mp hgO
    refine ⟨a, b, hb, Subtype.ext ?_⟩
    rw [hϖS]
    show ((b : ↥K₀') * (s : ↥K₀')) = ((algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀') ϖ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀')) : ↥K₀') * (a : ↥K₀')
    rw [hg, ← hab]
    show (b : ↥K₀') * (algebraMap A ↥K₀' ϖ * g) = algebraMap A ↥K₀' ϖ * (g * (b : ↥K₀'))
    ring

  have hf : ∀ s : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀'), ∃ a b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀), b ∉ P.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ∧ algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀') b * s - algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀') a ∈ P := by
    intro s
    obtain ⟨g, hgO, hsg⟩ := ModularCurve.FullLevel.exists_sub_inclusion_mem_nonunits_gauss_gamma0_of_mem_gauss_gamma0_mul
      q M' hqM' L A hAq K₀ hK₀ K₀' hK₀' hle₀' O₀ hO₀ O₀' hO₀' (s : ↥K₀') (hSO s)
    obtain ⟨a, b, hb, hab⟩ := (hP₀loc g).mp hgO
    refine ⟨a, b, fun h => hb ((hPunder b).mp h), ?_⟩
    rw [hPmem]
    have hcoe : ((algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀') b * s - algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀') a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀')) : ↥K₀') =
        (IntermediateField.inclusion hle₀') (b : ↥K₀) * ((s : ↥K₀') - (IntermediateField.inclusion hle₀') g) := by
      show ((ι₀' b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀')) : ↥K₀') * (s : ↥K₀') - ((ι₀' a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀') j₀')) : ↥K₀') = _
      rw [hι₀', hι₀', ← hab, map_mul]
      ring
    rw [hcoe]
    have h1 : (IntermediateField.inclusion hle₀') (b : ↥K₀) ∈ O₀' := (hO₀O₀' _).mpr (hRO b)
    have hmemO : (s : ↥K₀') - (IntermediateField.inclusion hle₀') g ∈ O₀' := ValuationSubring.nonunits_subset hsg
    have hmax' : (⟨_, hmemO⟩ : ↥O₀') ∈ IsLocalRing.maximalIdeal ↥O₀' :=
      (ValuationSubring.coe_mem_nonunits_iff (a := (⟨_, hmemO⟩ : ↥O₀'))).mp hsg
    have hprod : ((⟨_, h1⟩ : ↥O₀') * ⟨_, hmemO⟩) ∈ IsLocalRing.maximalIdeal ↥O₀' := Ideal.mul_mem_left _ _ hmax'
    exact (ValuationSubring.coe_mem_nonunits_iff (a := (⟨_, h1⟩ : ↥O₀') * ⟨_, hmemO⟩)).mpr hprod

  exact FLR.isUnramifiedAt_of_floor (((y.asIdeal).comap ι').under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀)) ((y.asIdeal).comap ι') P hPle (algebraMap A _ ϖ) hϖR0 hϖP hRreg hRdim
    (algebraMap A _ ϖ) (IsScalarTower.algebraMap_apply A _ _ ϖ) hRfib hRfib1 hRdom huniq he hf

end S_ModularCurve_FullLevel_isUnramifiedAt_chartAlgFin_gamma0_mul_comap_of_not_mem_ssJSet_xH
end P2MW
export P2MW.S_ModularCurve_FullLevel_isUnramifiedAt_chartAlgFin_gamma0_mul_comap_of_not_mem_ssJSet_xH (solution)
