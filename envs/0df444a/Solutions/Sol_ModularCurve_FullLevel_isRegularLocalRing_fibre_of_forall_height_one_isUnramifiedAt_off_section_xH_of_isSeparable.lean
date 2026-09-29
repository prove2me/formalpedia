-- Prove2me | solution 1 for ModularCurve.FullLevel.isRegularLocalRing_fibre_of_forall_height_one_isUnramifiedAt_off_section_xH_of_isSeparable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/6dbb689e-0783-57e0-b177-ecff64df737c

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Theorems.Thm_Module_free_of_isIntegrallyClosed_of_finite_of_isRegularLocalRing_of_ringKrullDim_le_two
import Theorems.Thm_Algebra_isUnramifiedAt_of_forall_le_height_eq_one_of_free_of_isIntegrallyClosed
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_Algebra_FormallyUnramified_isRegularLocalRing_quotient_span_of_ringKrullDim_quotient_eq_one
import Theorems.Thm_Subalgebra_ringKrullDim_localization_tensor_eq_one_of_irreducible
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isOpenImmersion_spec_tensor_chartAlgFin
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_IsRegularLocalRing_isDomain
import Theorems.Thm_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal
import Theorems.Thm_IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_two
import Theorems.Thm_IsRegularLocalRing_exists_ringEquiv_adicCompletion_of_isInvariant_of_isLocalization_atPrime_of_isUnramifiedAt_off
import Theorems.Thm_IsRegularLocalRing_quotient_span_of_ringEquiv_adicCompletion_of_maximalIdeal_eq_span_pair
import Theorems.Thm_IsRegularLocalRing_of_isUnramifiedAt_of_flat_of_maximalIdeal_eq_span_pair
import Theorems.Thm_AdicCompletion_isDomain_and_isIntegrallyClosed_of_isInvariant_of_isLocalization_atPrime_of_tame
import Theorems.Thm_ModularCurve_FullLevel_isUnramifiedAt_chartAlgFin_gamma0_mul_comap_of_not_mem_ssJSet_xH
import Theorems.Thm_ModularCurve_FullLevel_exists_mulSemiringAction_isInvariant_chartAlgFin_isCyclic_inertia_of_not_mem_ssJSet_xH
import Theorems.Thm_ModularCurve_laurentBaseChange_qExpFunctionFieldC_gamma0_le_laurentBaseChange_xHFunctionField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_isRegularLocalRing_fibre_of_forall_height_one_isUnramifiedAt_off_section_xH_of_isSeparable
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions"
p2m_attr_erase "instance" "instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange ModularCurve.instIsElliptic_tateBase ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms"
p2m_attr_erase "instance" "CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AdicCompletion.map_smul_of AdicCompletion.algebraMap_of AdicCompletion.stabilizer_smul_of AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq"
p2m_attr_erase "simp" "GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single"
p2m_attr_erase "simp" "ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply"
p2m_attr_erase "simp" "AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one"
p2m_attr_erase "simp" "TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply"
p2m_attr_erase "simp" "ModularCurve.baseAut_coeffSemilinearAut ModularCurve.coe_baseChangeRingHom ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec"
p2m_attr_erase "simp" "TateCurve.tateTorsionPoint_zero_zero ModularCurve.LevelN.coe_jGen ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec"

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

private theorem _root_.OrdRegAux.finite_chartAlgFin_of_floor
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

p2m_export "OrdRegAux" "finite_chartAlgFin_of_floor"

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

end OrdRegAux

set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing
open AlgebraicCurve.TwoChartIntegralModel

namespace OrdRegL0

theorem algebraMap_stalk_eq_germ {S : Type} [CommRing S] (q : ↥(Spec (CommRingCat.of S))) (s : S) :
    letI : Algebra S ((Spec (CommRingCat.of S)).presheaf.stalk q) :=
      AlgebraicGeometry.StructureSheaf.stalkAlgebra (R := S) q
    algebraMap S ((Spec (CommRingCat.of S)).presheaf.stalk q) s =
      ((Spec (CommRingCat.of S)).presheaf.germ ⊤ q trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom s) := by
  show AlgebraicGeometry.StructureSheaf.toStalk S q s = _
  rfl

theorem exists_ringEquiv_stalk_localization_map_germ_eq
    {A S : Type} [CommRing A] [CommRing S] [Algebra A S] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of A)) (ι : Spec (CommRingCat.of S) ⟶ X) [IsOpenImmersion ι]
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A S))) (q : ↥(Spec (CommRingCat.of S))) :
    ∃ E : X.presheaf.stalk (ι.base q) ≃+* Localization.AtPrime q.asIdeal,
      ∀ a : A, E ((X.presheaf.germ ⊤ (ι.base q) trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) =
        algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap A S a) := by
  have key : ∀ a : A, (ι.stalkMap q).hom ((X.presheaf.germ ⊤ (ι.base q) trivial).hom
      (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) =
      ((Spec (CommRingCat.of S)).presheaf.germ ⊤ q trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (algebraMap A S a)) := by
    intro a
    erw [Scheme.Hom.germ_stalkMap_apply ι ⊤ q trivial]
    congr 1
    show ((f.appTop ≫ ι.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) = _
    rw [← Scheme.Hom.comp_appTop, hι]
    show ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap A S))).appTop).hom a = _
    rw [← Scheme.ΓSpecIso_inv_naturality]
    rfl
  letI : Algebra S ((Spec (CommRingCat.of S)).presheaf.stalk q) :=
    AlgebraicGeometry.StructureSheaf.stalkAlgebra (R := S) q
  let E₁ : X.presheaf.stalk (ι.base q) ≃+* (Spec (CommRingCat.of S)).presheaf.stalk q :=
    (asIso (ι.stalkMap q)).commRingCatIsoToRingEquiv
  let E₂ : ((Spec (CommRingCat.of S)).presheaf.stalk q) ≃ₐ[S] Localization.AtPrime q.asIdeal :=
    (AlgebraicGeometry.StructureSheaf.stalkIso S q).symm
  refine ⟨E₁.trans E₂.toRingEquiv, fun a => ?_⟩
  rw [RingEquiv.trans_apply]
  change E₂ ((ι.stalkMap q).hom _) = _
  rw [key a, ← algebraMap_stalk_eq_germ q (algebraMap A S a)]
  exact E₂.commutes _

variable (A : Type) [CommRing A] (K : Type) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)]

theorem L0_isRegularLocalRing_fibre_of_localization
    (ϖ : A) (z : ↥(AlgebraicCurve.TwoChartIntegralModel A K j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.germ ⊤ z trivial).hom
      (((toBase A K j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (y : ↥(XFin A K j)) (hy : (ιFin A K j).base y = z)
    (h : IsRegularLocalRing (Localization.AtPrime y.asIdeal ⧸
      Ideal.span {algebraMap (↥(chartAlgFin A K j)) (Localization.AtPrime y.asIdeal) (algebraMap A _ ϖ)})) :
    IsRegularLocalRing (((AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.stalk z) ⧸ Ideal.span {ϖz}) := by
  subst hy
  subst hϖz
  obtain ⟨E, hE⟩ := exists_ringEquiv_stalk_localization_map_germ_eq (toBase A K j) (ιFin A K j) (ιFin_toBase A K j) y
  refine @IsRegularLocalRing.of_ringEquiv _ _ h _ _ (Ideal.quotientEquiv _ _ E.symm ?_)
  rw [Ideal.map_span, Set.image_singleton, ← hE ϖ]
  simp only [RingHom.coe_coe, RingEquiv.symm_apply_apply]

theorem exists_ringEquiv_stalk_ιFin_localization (y : ↥(XFin A K j)) :
    ∃ E : (AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.stalk ((ιFin A K j).base y) ≃+*
        Localization.AtPrime y.asIdeal,
      ∀ a : A, E (((AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.germ ⊤ ((ιFin A K j).base y) trivial).hom
          (((toBase A K j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) =
        algebraMap (↥(chartAlgFin A K j)) (Localization.AtPrime y.asIdeal) (algebraMap A _ a) :=
  exists_ringEquiv_stalk_localization_map_germ_eq (toBase A K j) (ιFin A K j) (ιFin_toBase A K j) y

theorem exists_ringEquiv_stalk_ιInf_localization (y : ↥(XInf A K j)) :
    ∃ E : (AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.stalk ((ιInf A K j).base y) ≃+*
        Localization.AtPrime y.asIdeal,
      ∀ a : A, E (((AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.germ ⊤ ((ιInf A K j).base y) trivial).hom
          (((toBase A K j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) =
        algebraMap (↥(chartAlgInf A K j)) (Localization.AtPrime y.asIdeal) (algebraMap A _ a) :=
  exists_ringEquiv_stalk_localization_map_germ_eq (toBase A K j) (ιInf A K j) (ιInf_toBase A K j) y

end OrdRegL0

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

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open IsLocalRing AlgebraicCurve.TwoChartIntegralModel

set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing
open AlgebraicCurve.TwoChartIntegralModel

namespace OrdRegL0

theorem germ_mem_maximalIdeal_iff_of_chart
    {A S : Type} [CommRing A] [CommRing S] [Algebra A S] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of A)) (ι : Spec (CommRingCat.of S) ⟶ X) [IsOpenImmersion ι]
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A S))) (q : ↥(Spec (CommRingCat.of S))) (a : A) :
    (X.presheaf.germ ⊤ (ι.base q) trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk (ι.base q)) ↔
      algebraMap A S a ∈ q.asIdeal := by
  have key : (ι.stalkMap q).hom ((X.presheaf.germ ⊤ (ι.base q) trivial).hom
      (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) =
      ((Spec (CommRingCat.of S)).presheaf.germ ⊤ q trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (algebraMap A S a)) := by
    erw [Scheme.Hom.germ_stalkMap_apply ι ⊤ q trivial]
    congr 1
    show ((f.appTop ≫ ι.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) = _
    rw [← Scheme.Hom.comp_appTop, hι]
    show ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap A S))).appTop).hom a = _
    rw [← Scheme.ΓSpecIso_inv_naturality]
    rfl
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← isUnit_map_iff (ι.stalkMap q).hom, key,
    ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
  letI : Algebra S ((Spec (CommRingCat.of S)).presheaf.stalk q) :=
    AlgebraicGeometry.StructureSheaf.stalkAlgebra (R := S) q
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of S)).presheaf.stalk q) q.asIdeal :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk S q
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff ((Spec (CommRingCat.of S)).presheaf.stalk q) q.asIdeal (algebraMap A S a)

variable (A : Type) [CommRing A] (K : Type) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)]

theorem algebraMap_mem_asIdeal_of_germ_mem_maximalIdeal
    (ϖ : A) (z : ↥(AlgebraicCurve.TwoChartIntegralModel A K j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.germ ⊤ z trivial).hom
      (((toBase A K j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.stalk z))
    (y : ↥(XFin A K j)) (hy : (ιFin A K j).base y = z) :
    algebraMap A (↥(chartAlgFin A K j)) ϖ ∈ y.asIdeal := by
  subst hy
  subst hϖz
  exact (germ_mem_maximalIdeal_iff_of_chart (toBase A K j) (ιFin A K j) (ιFin_toBase A K j) y ϖ).mp hz

theorem germ_mem_maximalIdeal_of_algebraMap_mem_asIdeal
    (ϖ : A) (y : ↥(XFin A K j)) (hy : algebraMap A (↥(chartAlgFin A K j)) ϖ ∈ y.asIdeal) :
    ((AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.germ ⊤ ((ιFin A K j).base y) trivial).hom
      (((toBase A K j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)) ∈
      IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A K j).presheaf.stalk ((ιFin A K j).base y)) :=
  (germ_mem_maximalIdeal_iff_of_chart (toBase A K j) (ιFin A K j) (ιFin_toBase A K j) y ϖ).mpr hy

end OrdRegL0

namespace OrdRegSeams
open IsLocalRing AlgebraicCurve.TwoChartIntegralModel

private theorem _root_.OrdRegSeams.finite_chartAlgFin_of_floor
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] [CharZero L]
    (K K' : IntermediateField L (LaurentSeries L)) (hle : K' ≤ K)
    [Algebra A ↥K] [IsScalarTower A L ↥K] [Algebra A ↥K'] [IsScalarTower A L ↥K']
    (j : ↥K) (j' : ↥K') [Fact (j ≠ 0)] [Fact (j' ≠ 0)] (hjj' : (IntermediateField.inclusion hle j' : ↥K) = j)
    (htj : Transcendental A j) (hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K)
    [Algebra ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)] [IsScalarTower A ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)]
    (hι : ∀ x : ↥(chartAlgFin A (↥K') j'), ((algebraMap _ ↥(chartAlgFin A (↥K) j) x : ↥(chartAlgFin A (↥K) j)) : ↥K) = IntermediateField.inclusion hle (x : ↥K')) :
    Module.Finite ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j) :=
  OrdRegAux.finite_chartAlgFin_of_floor A L K K' hle j j' hjj' htj hFD hι

p2m_export "OrdRegSeams" "finite_chartAlgFin_of_floor"
end OrdRegSeams

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

set_option maxHeartbeats 3200000

open IsLocalRing

namespace KFO2

theorem exists_prime_span_eq_of_minimal {O : Type*} [CommRing O] [IsDomain O] [UniqueFactorizationMonoid O]
    (P : Ideal O) [P.IsPrime] (hP0 : P ≠ ⊥)
    (hmin : ∀ Q : Ideal O, Q.IsPrime → Q ≠ ⊥ → Q ≤ P → Q = P) :
    ∃ s : O, Prime s ∧ P = Ideal.span {s} := by
  classical
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have key : ∀ (m : Multiset O), (∀ q ∈ m, Prime q) → m.prod ∈ P → ∃ q ∈ m, q ∈ P := by
    intro m
    induction m using Multiset.induction_on with
    | empty => intro _ h; exact absurd (Ideal.eq_top_of_isUnit_mem _ (by simpa using h) isUnit_one) ‹P.IsPrime›.ne_top
    | cons a m ih =>
      intro hm hprod
      rw [Multiset.prod_cons] at hprod
      rcases ‹P.IsPrime›.mem_or_mem hprod with ha | hm'
      · exact ⟨a, Multiset.mem_cons_self a m, ha⟩
      · obtain ⟨q, hq, hqP⟩ := ih (fun q hq => hm q (Multiset.mem_cons_of_mem hq)) hm'
        exact ⟨q, Multiset.mem_cons_of_mem hq, hqP⟩
  obtain ⟨m, hm, u, hu⟩ := UniqueFactorizationMonoid.exists_prime_factors x hx0
  have hmprod : m.prod ∈ P := by
    have : x * (u⁻¹ : Oˣ) = m.prod := by rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [← this]; exact Ideal.mul_mem_right _ _ hxP
  obtain ⟨p, hpm, hpP⟩ := key m hm hmprod
  have hp : Prime p := hm p hpm
  haveI : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  refine ⟨p, hp, (hmin (Ideal.span {p}) inferInstance ?_ ?_).symm⟩
  · rw [Ne, Ideal.span_singleton_eq_bot]; exact hp.ne_zero
  · rw [Ideal.span_singleton_le_iff_mem]; exact hpP

theorem exists_span_eq_and_maximalIdeal_eq_of_sup_span_eq
    {O : Type*} [CommRing O] [IsRegularLocalRing O] [IsDomain O] (hdim : ringKrullDim O = 2)
    (P : Ideal O) [P.IsPrime] (hP0 : P ≠ ⊥) (ϖ : O) (hϖ : ϖ ∉ P)
    (hsup : P ⊔ Ideal.span {ϖ} = maximalIdeal O) :
    ∃ s : O, Prime s ∧ P = Ideal.span {s} ∧ maximalIdeal O = Ideal.span {ϖ, s} := by
  classical
  haveI : IsNoetherianRing O := inferInstance
  haveI : IsLocalRing O := inferInstance
  haveI : UniqueFactorizationMonoid O := IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two O hdim.le
  have hPne : P ≠ maximalIdeal O := by
    intro h
    apply hϖ
    rw [h, ← hsup]
    exact Submodule.mem_sup_right (Ideal.mem_span_singleton_self ϖ)
  have hPlt : P < maximalIdeal O := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal ‹P.IsPrime›.ne_top) hPne

  have hmin : ∀ Q : Ideal O, Q.IsPrime → Q ≠ ⊥ → Q ≤ P → Q = P := by
    intro Q hQ hQ0 hQP
    by_contra hne
    have hQlt : Q < P := lt_of_le_of_ne hQP hne
    have hbot : (⊥ : Ideal O) < Q := bot_lt_iff_ne_bot.mpr hQ0

    haveI := hQ
    haveI : (⊥ : Ideal O).IsPrime := Ideal.bot_prime
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hbot
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hQlt
    have h3 := Ideal.height_add_one_le_of_lt_of_isPrime hPlt
    have h4 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := O)
    rw [hdim] at h4
    have h4' : (maximalIdeal O).height = 2 := by
      have : ((maximalIdeal O).height : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := h4
      exact WithBot.coe_injective this
    have hfin : (maximalIdeal O).height ≠ ⊤ := by rw [h4']; decide
    have : (3 : ℕ∞) ≤ (maximalIdeal O).height :=
      calc (3 : ℕ∞) = 0 + 1 + 1 + 1 := by norm_num
        _ ≤ (⊥ : Ideal O).height + 1 + 1 + 1 := by gcongr; exact zero_le
        _ ≤ Q.height + 1 + 1 := by gcongr
        _ ≤ P.height + 1 := by gcongr
        _ ≤ (maximalIdeal O).height := h3
    rw [h4'] at this
    exact absurd this (by decide)
  obtain ⟨s, hs, hPs⟩ := exists_prime_span_eq_of_minimal P hP0 hmin
  refine ⟨s, hs, hPs, ?_⟩
  rw [← hsup, hPs, Ideal.span_insert, sup_comm]

end KFO2

open IsLocalRing

namespace WATCore

theorem eq_of_le_of_ne_bot_of_ne_maximalIdeal {O : Type u} [CommRing O] [IsNoetherianRing O] [IsLocalRing O] [IsDomain O]
    (hdim : ringKrullDim O = 2) (Q₁ Q₂ : Ideal O) [Q₁.IsPrime] [Q₂.IsPrime]
    (h0 : Q₁ ≠ ⊥) (hle : Q₁ ≤ Q₂) (hne : Q₂ ≠ maximalIdeal O) : Q₁ = Q₂ := by
  by_contra hne'
  have hQlt : Q₁ < Q₂ := lt_of_le_of_ne hle hne'
  have hbot : (⊥ : Ideal O) < Q₁ := bot_lt_iff_ne_bot.mpr h0
  have hQ₂lt : Q₂ < maximalIdeal O := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal ‹Q₂.IsPrime›.ne_top) hne
  haveI : (⊥ : Ideal O).IsPrime := Ideal.bot_prime
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hbot
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hQlt
  have h3 := Ideal.height_add_one_le_of_lt_of_isPrime hQ₂lt
  have h4 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := O)
  rw [hdim] at h4
  have h4' : (maximalIdeal O).height = 2 := by
    have : ((maximalIdeal O).height : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := h4
    exact WithBot.coe_injective this
  have : (3 : ℕ∞) ≤ (maximalIdeal O).height :=
    calc (3 : ℕ∞) = 0 + 1 + 1 + 1 := by norm_num
      _ ≤ (⊥ : Ideal O).height + 1 + 1 + 1 := by gcongr; exact zero_le
      _ ≤ Q₁.height + 1 + 1 := by gcongr
      _ ≤ Q₂.height + 1 := by gcongr
      _ ≤ (maximalIdeal O).height := h3
  rw [h4'] at this
  exact absurd this (by decide)

theorem ringKrullDim_le_one_of_span_singleton (T : Type u) [CommRing T] [IsNoetherianRing T] [IsLocalRing T] (a : T)
    (ha : maximalIdeal T = Ideal.span {a}) : ringKrullDim T ≤ 1 := by
  refine (ringKrullDim_le_spanFinrank_maximalIdeal T).trans ?_
  rw [ha]
  exact_mod_cast (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton a)).trans
    (by rw [Set.ncard_singleton])

theorem isDiscreteValuationRing_quotient_of_maximalIdeal_eq_span_pair
    {O : Type u} [CommRing O] [IsNoetherianRing O] [IsLocalRing O] [IsDomain O]
    (ϖ s : O) (hmax : maximalIdeal O = Ideal.span {ϖ, s}) (hs : Prime s) (hϖ : ϖ ∉ Ideal.span {s}) :
    ∃ (_ : IsDomain (O ⧸ Ideal.span {s})), IsDiscreteValuationRing (O ⧸ Ideal.span {s}) := by
  classical
  set I : Ideal O := Ideal.span {s} with hI
  haveI hIp : I.IsPrime := (Ideal.span_singleton_prime hs.ne_zero).mpr hs
  haveI : IsDomain (O ⧸ I) := inferInstance
  haveI : IsLocalRing (O ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : IsNoetherianRing (O ⧸ I) := inferInstance
  have hI𝔪 : I ≤ maximalIdeal O := IsLocalRing.le_maximalIdeal hIp.ne_top
  have hmax'' : maximalIdeal (O ⧸ I) = Ideal.span {Ideal.Quotient.mk I ϖ} := by
    have h1 : (maximalIdeal O).map (Ideal.Quotient.mk I) = maximalIdeal (O ⧸ I) := by
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
        (IsLocalRing.maximalIdeal.isMaximal O) with h | h
      · exfalso
        have h1mem : (1 : O ⧸ I) ∈ (maximalIdeal O).map (Ideal.Quotient.mk I) := by rw [h]; trivial
        rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h1mem
        obtain ⟨m, hm, hm1⟩ := h1mem
        rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq] at hm1
        apply (IsLocalRing.maximalIdeal.isMaximal O).ne_top
        rw [Ideal.eq_top_iff_one]
        have : (1 : O) = m - (m - 1) := by ring
        rw [this]; exact Ideal.sub_mem _ hm (hI𝔪 hm1)
      · exact IsLocalRing.eq_maximalIdeal h
    rw [← h1, hmax, Ideal.map_span, Set.image_insert_eq, Set.image_singleton,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl : s ∈ I)]
    apply le_antisymm
    · rw [Ideal.span_le]; rintro x (rfl | rfl)
      · exact Ideal.subset_span rfl
      · exact Ideal.zero_mem _
    · exact Ideal.span_mono (by simp)
  have hϖ0 : Ideal.Quotient.mk I ϖ ≠ 0 := fun h => hϖ (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hnf : ¬ IsField (O ⧸ I) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmax'', Ideal.span_singleton_eq_bot]
    exact hϖ0
  have hprinc : Submodule.IsPrincipal (maximalIdeal (O ⧸ I)) :=
    ⟨⟨Ideal.Quotient.mk I ϖ, by rw [hmax'', Ideal.submodule_span_eq]⟩⟩
  exact ⟨inferInstance, ((IsDiscreteValuationRing.TFAE (O ⧸ I) hnf).out 4 0).mp hprinc⟩

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

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem WATcore
    {A : Type} [CommRing A] (ϖ : A)
    {A₂ A₃ A₁ : Type} [CommRing A₂] [CommRing A₃] [CommRing A₁]
    [IsDomain A₂] [IsDomain A₃] [IsDomain A₁]
    [IsNoetherianRing A₂] [IsNoetherianRing A₃] [IsNoetherianRing A₁]
    [IsIntegrallyClosed A₃] [IsIntegrallyClosed A₁]
    [Algebra A A₂] [Algebra A A₁]
    [Algebra A₂ A₁] [Algebra A₃ A₁] [Algebra A₂ A₃]
    [IsScalarTower A A₂ A₁] [IsScalarTower A₂ A₃ A₁]
    [Module.Finite A₂ A₁] [Module.Finite A₃ A₁] [FaithfulSMul A₂ A₁] [FaithfulSMul A₃ A₁]
    (y : Ideal A₁) [y.IsMaximal]

    (hRreg : IsRegularLocalRing (Localization.AtPrime (y.comap (algebraMap A₂ A₁))))
    (hRdim : ringKrullDim (Localization.AtPrime (y.comap (algebraMap A₂ A₁))) ≤ 2)
    (hRfib1 : ringKrullDim (Localization.AtPrime (y.comap (algebraMap A₂ A₁)) ⧸
      Ideal.span {algebraMap A (Localization.AtPrime (y.comap (algebraMap A₂ A₁))) ϖ}) = 1)

    (𝔔₀ : Ideal A₂) [𝔔₀.IsPrime]
    (h𝔔₀y : 𝔔₀ ≤ y.comap (algebraMap A₂ A₁)) (h𝔔₀ϖ : algebraMap A A₂ ϖ ∉ 𝔔₀)
    (h𝔔₀reg : Ideal.map (algebraMap A₂ (Localization.AtPrime (y.comap (algebraMap A₂ A₁)))) 𝔔₀ ⊔
      Ideal.span {algebraMap A₂ (Localization.AtPrime (y.comap (algebraMap A₂ A₁))) (algebraMap A A₂ ϖ)} =
        maximalIdeal (Localization.AtPrime (y.comap (algebraMap A₂ A₁))))
    (hunr : ∀ (𝔔 : Ideal A₁) [𝔔.IsPrime], 𝔔 ≤ y → 𝔔.height = 1 → 𝔔.comap (algebraMap A₂ A₁) ≠ 𝔔₀ →
      Algebra.IsUnramifiedAt A₂ 𝔔)
    (hsep : ∀ h : y.comap (algebraMap A₂ A₁) ≤ y.comap (algebraMap A₂ A₁),
      letI : Algebra (A₂ ⧸ y.comap (algebraMap A₂ A₁)) (A₁ ⧸ y) := Ideal.Quotient.algebraQuotientOfLEComap h
      Algebra.IsSeparable (A₂ ⧸ y.comap (algebraMap A₂ A₁)) (A₁ ⧸ y))

    (hP2 : Algebra.IsUnramifiedAt A₂ (y.comap (algebraMap A₃ A₁)))

    {G : Type} [Group G] [Fintype G] [MulSemiringAction G A₁] [SMulCommClass G A₃ A₁] [FaithfulSMul G A₁]
    [Algebra.IsInvariant A₃ A₁ G]
    (e : ℕ) (he : 0 < e) (hIy : Nat.card ↥(y.inertia G) = e) (hIcyc : IsCyclic ↥(y.inertia G))
    (heA : IsUnit ((e : ℕ) : A)) :
    IsRegularLocalRing (Localization.AtPrime y ⧸ Ideal.span {algebraMap A₁ (Localization.AtPrime y) (algebraMap A A₁ ϖ)}) := by
  classical

  have hinj21 : Function.Injective (algebraMap A₂ A₁) := FaithfulSMul.algebraMap_injective A₂ A₁
  have hinj31 : Function.Injective (algebraMap A₃ A₁) := FaithfulSMul.algebraMap_injective A₃ A₁
  have hinj23 : Function.Injective (algebraMap A₂ A₃) := by
    have h : Function.Injective (algebraMap A₃ A₁ ∘ algebraMap A₂ A₃) := by
      rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]; exact hinj21
    exact h.of_comp
  haveI : FaithfulSMul A₂ A₃ := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj23
  haveI : Module.Finite A₂ A₃ :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom A₂ A₃ A₁).toLinearMap hinj31
  haveI : Algebra.IsIntegral A₂ A₁ := inferInstance
  haveI : Algebra.IsIntegral A₃ A₁ := inferInstance
  let y₂ : Ideal A₂ := y.comap (algebraMap A₂ A₁)
  let y₃ : Ideal A₃ := y.comap (algebraMap A₃ A₁)
  haveI hy₂max : y₂.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal y
  haveI hy₃max : y₃.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal y
  haveI hy₂p : y₂.IsPrime := hy₂max.isPrime
  haveI hy₃p : y₃.IsPrime := hy₃max.isPrime
  have hy₃₂ : y₃.comap (algebraMap A₂ A₃) = y₂ := by
    show (y.comap (algebraMap A₃ A₁)).comap (algebraMap A₂ A₃) = y.comap (algebraMap A₂ A₁)
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  haveI hlo : y₃.LiesOver y₂ := ⟨hy₃₂.symm⟩
  haveI := hRreg
  haveI hOdom : IsDomain (Localization.AtPrime y₂) := IsRegularLocalRing.isDomain _

  have hϖ2 : algebraMap A (Localization.AtPrime y₂) ϖ = algebraMap A₂ (Localization.AtPrime y₂) (algebraMap A A₂ ϖ) :=
    IsScalarTower.algebraMap_apply _ _ _ _
  have hne : algebraMap A A₂ ϖ ≠ 0 := fun h => h𝔔₀ϖ (h.symm ▸ 𝔔₀.zero_mem)
  have hϖ0 : algebraMap A₂ (Localization.AtPrime y₂) (algebraMap A A₂ ϖ) ≠ 0 := fun h =>
    hne (IsLocalization.injective (Localization.AtPrime y₂) y₂.primeCompl_le_nonZeroDivisors (by rw [h, map_zero]))

  have hOdim : ringKrullDim (Localization.AtPrime y₂) = 2 := by
    refine le_antisymm hRdim ?_
    have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hϖ0)
    rw [← hϖ2, hRfib1] at h2
    exact (by norm_num : (2 : WithBot ℕ∞) = 1 + 1) ▸ h2
  have hdisj : Disjoint (y₂.primeCompl : Set A₂) (𝔔₀ : Set A₂) :=
    Set.disjoint_left.mpr fun x hx hx' => hx (h𝔔₀y hx')
  haveI h𝔔₀Oprime : (𝔔₀.map (algebraMap A₂ (Localization.AtPrime y₂))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint y₂.primeCompl _ 𝔔₀ inferInstance hdisj
  have h𝔔₀0 : 𝔔₀.map (algebraMap A₂ (Localization.AtPrime y₂)) ≠ ⊥ := by
    intro h0
    have h := h𝔔₀reg
    rw [h0, bot_sup_eq] at h
    have h1 := ringKrullDim_le_one_of_span_singleton (Localization.AtPrime y₂) _ h.symm
    rw [hOdim] at h1
    exact absurd h1 (by decide)
  have hϖnot : algebraMap A₂ (Localization.AtPrime y₂) (algebraMap A A₂ ϖ) ∉ 𝔔₀.map (algebraMap A₂ (Localization.AtPrime y₂)) := by
    intro h
    apply h𝔔₀ϖ
    have := IsLocalization.comap_map_of_isPrime_disjoint y₂.primeCompl (Localization.AtPrime y₂) inferInstance hdisj
    rw [← this]
    exact h
  obtain ⟨s, hsprime, hsO, hmaxO⟩ := KFO2.exists_span_eq_and_maximalIdeal_eq_of_sup_span_eq hOdim
    (𝔔₀.map (algebraMap A₂ (Localization.AtPrime y₂))) h𝔔₀0 (algebraMap A₂ (Localization.AtPrime y₂) (algebraMap A A₂ ϖ)) hϖnot h𝔔₀reg
  have hϖs : algebraMap A₂ (Localization.AtPrime y₂) (algebraMap A A₂ ϖ) ∉ Ideal.span {s} := hsO ▸ hϖnot

  obtain ⟨hDdom, hDdvr⟩ := isDiscreteValuationRing_quotient_of_maximalIdeal_eq_span_pair _ s hmaxO hsprime hϖs
  haveI := hDdom
  haveI := hDdvr

  letI algOO₃ : Algebra (Localization.AtPrime y₂) (Localization.AtPrime y₃) := Localization.AtPrime.algebraOfLiesOver y₂ y₃
  have halgOO₃ : algebraMap (Localization.AtPrime y₂) (Localization.AtPrime y₃) =
      Localization.localRingHom y₂ y₃ (algebraMap A₂ A₃) Ideal.LiesOver.over := rfl
  haveI : IsLocalHom (algebraMap (Localization.AtPrime y₂) (Localization.AtPrime y₃)) := by
    rw [halgOO₃]; exact Localization.isLocalHom_localRingHom y₂ y₃ _ _
  haveI : IsScalarTower A₂ (Localization.AtPrime y₂) (Localization.AtPrime y₃) := inferInstance
  haveI : Algebra.EssFiniteType A₃ (Localization.AtPrime y₃) := Algebra.EssFiniteType.of_isLocalization _ y₃.primeCompl
  haveI : Algebra.EssFiniteType A₂ A₃ := inferInstance
  haveI : Algebra.EssFiniteType A₂ (Localization.AtPrime y₃) := Algebra.EssFiniteType.comp A₂ A₃ _
  haveI : Algebra.EssFiniteType (Localization.AtPrime y₂) (Localization.AtPrime y₃) :=
    Algebra.EssFiniteType.of_comp A₂ _ _

  haveI : Algebra.FormallyUnramified A₂ (Localization.AtPrime y₃) := hP2
  haveI : Algebra.FormallyUnramified (Localization.AtPrime y₂) (Localization.AtPrime y₃) :=
    Algebra.FormallyUnramified.of_restrictScalars A₂ _ _
  haveI : Algebra.IsUnramifiedAt (Localization.AtPrime y₂) (maximalIdeal (Localization.AtPrime y₃)) := by
    show Algebra.FormallyUnramified (Localization.AtPrime y₂) (Localization.AtPrime (maximalIdeal (Localization.AtPrime y₃)))
    haveI : Algebra.FormallyUnramified (Localization.AtPrime y₃) (Localization.AtPrime (maximalIdeal (Localization.AtPrime y₃))) :=
      Algebra.FormallyUnramified.of_isLocalization (maximalIdeal (Localization.AtPrime y₃)).primeCompl
    exact Algebra.FormallyUnramified.comp (Localization.AtPrime y₂) (Localization.AtPrime y₃) _

  haveI : Module.Flat (Localization.AtPrime y₂) (Localization.AtPrime y₃) := by
    obtain ⟨hfin, hic, hdom, hfaith⟩ := L3_localization (A' := A₂) (B := A₃) y₂
    haveI := hfin; haveI := hic; haveI := hdom; haveI := hfaith
    haveI hfree : Module.Free (Localization.AtPrime y₂) (Localization (Algebra.algebraMapSubmonoid A₃ y₂.primeCompl)) :=
      Module.free_of_isIntegrallyClosed_of_finite_of_isRegularLocalRing_of_ringKrullDim_le_two (Localization.AtPrime y₂) hRdim _
    have hMN : Algebra.algebraMapSubmonoid A₃ y₂.primeCompl ≤ y₃.primeCompl := by
      rintro _ ⟨a, ha, rfl⟩ h
      exact ha (show a ∈ y₂ by rw [← hy₃₂]; exact h)
    letI algBO₃ : Algebra (Localization (Algebra.algebraMapSubmonoid A₃ y₂.primeCompl)) (Localization.AtPrime y₃) :=
      IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Algebra.algebraMapSubmonoid A₃ y₂.primeCompl) y₃.primeCompl hMN
    haveI : IsScalarTower A₃ (Localization (Algebra.algebraMapSubmonoid A₃ y₂.primeCompl)) (Localization.AtPrime y₃) :=
      IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hMN
    haveI : IsLocalization ((y₃.primeCompl).map (algebraMap A₃ (Localization (Algebra.algebraMapSubmonoid A₃ y₂.primeCompl))))
        (Localization.AtPrime y₃) :=
      IsLocalization.isLocalization_of_submonoid_le _ _ _ _ hMN
    haveI : Module.Flat (Localization (Algebra.algebraMapSubmonoid A₃ y₂.primeCompl)) (Localization.AtPrime y₃) :=
      IsLocalization.flat _ ((y₃.primeCompl).map (algebraMap A₃ (Localization (Algebra.algebraMapSubmonoid A₃ y₂.primeCompl))))
    haveI : IsScalarTower A₂ (Localization (Algebra.algebraMapSubmonoid A₃ y₂.primeCompl)) (Localization.AtPrime y₃) :=
      IsScalarTower.of_algebraMap_eq (fun a => by
        rw [IsScalarTower.algebraMap_apply A₂ A₃ (Localization (Algebra.algebraMapSubmonoid A₃ y₂.primeCompl)),
          IsScalarTower.algebraMap_apply A₂ A₃ (Localization.AtPrime y₃),
          IsScalarTower.algebraMap_apply A₃ (Localization (Algebra.algebraMapSubmonoid A₃ y₂.primeCompl)) (Localization.AtPrime y₃)])
    haveI : Module.Flat A₂ (Localization.AtPrime y₂) := IsLocalization.flat _ y₂.primeCompl
    haveI : Module.Flat A₂ (Localization (Algebra.algebraMapSubmonoid A₃ y₂.primeCompl)) :=
      Module.Flat.trans A₂ (Localization.AtPrime y₂) _
    haveI : Module.Flat A₂ (Localization.AtPrime y₃) :=
      Module.Flat.trans A₂ (Localization (Algebra.algebraMapSubmonoid A₃ y₂.primeCompl)) _
    exact (Module.flat_iff_of_isLocalization (Localization.AtPrime y₂) y₂.primeCompl (Localization.AtPrime y₃)).mpr this

  obtain ⟨hreg₃, hdim₃, hmax₃, hprime₃, -⟩ :=
    IsRegularLocalRing.of_isUnramifiedAt_of_flat_of_maximalIdeal_eq_span_pair
      (O := Localization.AtPrime y₂) (O' := Localization.AtPrime y₃)
      (algebraMap A₂ (Localization.AtPrime y₂) (algebraMap A A₂ ϖ)) s hmaxO hOdim
      (Ideal.Quotient.mk (Ideal.span {s})) Ideal.Quotient.mk_surjective Ideal.mk_ker

  haveI := hreg₃
  haveI hO₃dom : IsDomain (Localization.AtPrime y₃) := IsRegularLocalRing.isDomain _

  set ϖ₃ : A₃ := algebraMap A₂ A₃ (algebraMap A A₂ ϖ) with hϖ₃def
  set s₃ : Localization.AtPrime y₃ := algebraMap (Localization.AtPrime y₂) (Localization.AtPrime y₃) s with hs₃def
  have hϖO₃ : algebraMap (Localization.AtPrime y₂) (Localization.AtPrime y₃) (algebraMap A₂ (Localization.AtPrime y₂) (algebraMap A A₂ ϖ)) =
      algebraMap A₃ (Localization.AtPrime y₃) ϖ₃ := by
    rw [halgOO₃, Localization.localRingHom_to_map]
  rw [hϖO₃] at hmax₃

  let 𝔔₃ : Ideal A₃ := (Ideal.span {s₃}).comap (algebraMap A₃ (Localization.AtPrime y₃))
  haveI h𝔔₃p : 𝔔₃.IsPrime := Ideal.comap_isPrime _ _
  have h𝔔₃y : 𝔔₃ ≤ y₃ := by
    intro a ha
    have hle : Ideal.span {s₃} ≤ maximalIdeal (Localization.AtPrime y₃) := IsLocalRing.le_maximalIdeal hprime₃.ne_top
    have := hle ha
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime y₃) y₃ a).mp this
  have hsO₃ : 𝔔₃.map (algebraMap A₃ (Localization.AtPrime y₃)) = Ideal.span {s₃} :=
    IsLocalization.map_comap y₃.primeCompl (Localization.AtPrime y₃) _

  have hunr₃ : ∀ (𝔔 : Ideal A₁) [𝔔.IsPrime], 𝔔 ≤ y → 𝔔.height = 1 → 𝔔.comap (algebraMap A₃ A₁) ≠ 𝔔₃ →
      Algebra.IsUnramifiedAt A₃ 𝔔 := by
    intro 𝔔 _ h𝔔y h𝔔1 h𝔔3
    by_cases hc : 𝔔.comap (algebraMap A₂ A₁) = 𝔔₀
    ·
      exfalso
      apply h𝔔3
      set P : Ideal A₃ := 𝔔.comap (algebraMap A₃ A₁) with hPdef
      haveI hPp : P.IsPrime := Ideal.comap_isPrime _ _
      have hPy : P ≤ y₃ := Ideal.comap_mono h𝔔y
      have hP2 : P.comap (algebraMap A₂ A₃) = 𝔔₀ := by
        rw [hPdef, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]; exact hc
      have hdisjP : Disjoint (y₃.primeCompl : Set A₃) (P : Set A₃) := Set.disjoint_left.mpr fun x hx hx' => hx (hPy hx')
      haveI hPO : (P.map (algebraMap A₃ (Localization.AtPrime y₃))).IsPrime :=
        IsLocalization.isPrime_of_isPrime_disjoint y₃.primeCompl _ P hPp hdisjP

      have hsP : Ideal.span {s₃} ≤ P.map (algebraMap A₃ (Localization.AtPrime y₃)) := by
        rw [Ideal.span_singleton_le_iff_mem, hs₃def]
        have hs𝔔₀ : s ∈ 𝔔₀.map (algebraMap A₂ (Localization.AtPrime y₂)) := by rw [hsO]; exact Ideal.mem_span_singleton_self s
        have h1 : (𝔔₀.map (algebraMap A₂ (Localization.AtPrime y₂))).map (algebraMap (Localization.AtPrime y₂) (Localization.AtPrime y₃)) ≤
            P.map (algebraMap A₃ (Localization.AtPrime y₃)) := by
          rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A₂ A₃ (Localization.AtPrime y₃),
            ← Ideal.map_map]
          exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr hP2.ge)
        exact h1 (Ideal.mem_map_of_mem _ hs𝔔₀)

      have hPne : P.map (algebraMap A₃ (Localization.AtPrime y₃)) ≠ maximalIdeal (Localization.AtPrime y₃) := by
        intro hPm
        have : P = y₃ := by
          have h1 := IsLocalization.comap_map_of_isPrime_disjoint y₃.primeCompl (Localization.AtPrime y₃) hPp hdisjP
          rw [hPm] at h1
          rw [← h1]
          exact IsLocalization.AtPrime.comap_maximalIdeal (Localization.AtPrime y₃) y₃
        apply h𝔔₀ϖ
        rw [← hP2, this, hy₃₂]
        show algebraMap A₂ A₁ (algebraMap A A₂ ϖ) ∈ y
        have : algebraMap A₂ (Localization.AtPrime y₂) (algebraMap A A₂ ϖ) ∈ maximalIdeal (Localization.AtPrime y₂) := by
          rw [hmaxO]; exact Ideal.subset_span (by simp)
        exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime y₂) y₂ _).mp this
      have hs₃0 : Ideal.span {s₃} ≠ ⊥ := by
        intro h0
        rw [h0] at hsP
        have h1 := ringKrullDim_le_one_of_span_singleton (Localization.AtPrime y₃) (algebraMap A₃ (Localization.AtPrime y₃) ϖ₃) (by
          rw [hmax₃, Ideal.span_singleton_eq_bot.mp h0]
          apply le_antisymm
          · rw [Ideal.span_le]; rintro x (rfl | rfl)
            · exact Ideal.subset_span rfl
            · exact Ideal.zero_mem _
          · exact Ideal.span_mono (by simp))
        rw [hdim₃] at h1
        exact absurd h1 (by decide)
      have heq := eq_of_le_of_ne_bot_of_ne_maximalIdeal hdim₃ (Ideal.span {s₃}) (P.map (algebraMap A₃ (Localization.AtPrime y₃))) hs₃0 hsP hPne
      have h1 := IsLocalization.comap_map_of_isPrime_disjoint y₃.primeCompl (Localization.AtPrime y₃) hPp hdisjP
      rw [← h1, ← heq]
    · haveI := hunr 𝔔 h𝔔y h𝔔1 hc
      exact Algebra.IsUnramifiedAt.of_restrictScalars A₂ 𝔔

  have hsep₃ : ∀ h : y₃ ≤ y.comap (algebraMap A₃ A₁),
      letI : Algebra (A₃ ⧸ y₃) (A₁ ⧸ y) := Ideal.Quotient.algebraQuotientOfLEComap h
      Algebra.IsSeparable (A₃ ⧸ y₃) (A₁ ⧸ y) := by
    intro h
    letI alg31 : Algebra (A₃ ⧸ y₃) (A₁ ⧸ y) := Ideal.Quotient.algebraQuotientOfLEComap h
    letI alg21 : Algebra (A₂ ⧸ y₂) (A₁ ⧸ y) := Ideal.Quotient.algebraQuotientOfLEComap le_rfl
    letI alg23 : Algebra (A₂ ⧸ y₂) (A₃ ⧸ y₃) := Ideal.Quotient.algebraQuotientOfLEComap hy₃₂.ge
    letI : Field (A₃ ⧸ y₃) := Ideal.Quotient.field y₃
    haveI : IsScalarTower (A₂ ⧸ y₂) (A₃ ⧸ y₃) (A₁ ⧸ y) := by
      refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      show Ideal.Quotient.mk y (algebraMap A₂ A₁ a) = Ideal.Quotient.mk y (algebraMap A₃ A₁ (algebraMap A₂ A₃ a))
      rw [IsScalarTower.algebraMap_apply A₂ A₃ A₁]
    haveI : Algebra.IsSeparable (A₂ ⧸ y₂) (A₁ ⧸ y) := hsep le_rfl
    exact Algebra.isSeparable_tower_top_of_isSeparable (A₂ ⧸ y₂) (A₃ ⧸ y₃) (A₁ ⧸ y)

  have heO₃ : IsUnit ((e : ℕ) : Localization.AtPrime y₃) := by
    have h := (heA.map (algebraMap A A₂)).map (algebraMap A₂ (Localization.AtPrime y₃))
    rwa [map_natCast, map_natCast] at h

  haveI : IsNoetherianRing (Localization.AtPrime y) := inferInstance
  obtain ⟨hSdom, hSnorm⟩ :=
    AdicCompletion.isDomain_and_isIntegrallyClosed_of_isInvariant_of_isLocalization_atPrime_of_tame
      (A₂ := A₃) (A₁ := A₁) (G := G) y y₃ rfl e he hIy hIcyc 𝔔₃ h𝔔₃y ϖ₃ (Localization.AtPrime y₃) s₃ hsO₃ hmax₃ hdim₃ heO₃
      hunr₃ hsep₃ (Localization.AtPrime y)
  obtain ⟨R', _, _, ϖ', τ, hmaxR', hdimR', ιc, hιc⟩ :=
    IsRegularLocalRing.exists_ringEquiv_adicCompletion_of_isInvariant_of_isLocalization_atPrime_of_isUnramifiedAt_off
      (A₂ := A₃) (A₁ := A₁) (G := G) y y₃ rfl e he hIy hIcyc 𝔔₃ h𝔔₃y ϖ₃ (Localization.AtPrime y₃) s₃ hsO₃ hmax₃ hdim₃ heO₃
      (Localization.AtPrime y) hSdom hSnorm hunr₃ hsep₃
  have hϖ₁ : algebraMap A₃ A₁ ϖ₃ = algebraMap A A₁ ϖ := by
    rw [hϖ₃def, ← IsScalarTower.algebraMap_apply A₂ A₃ A₁, ← IsScalarTower.algebraMap_apply A A₂ A₁]
  rw [hϖ₁] at hιc
  exact (IsRegularLocalRing.quotient_span_of_ringEquiv_adicCompletion_of_maximalIdeal_eq_span_pair ϖ' τ hmaxR' hdimR' _ ιc hιc).1

end WATCore

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

namespace P4Aux

open AlgebraicCurve.TwoChartIntegralModel

section Incl

variable (L : Type) [Field L] (A : Type) [CommRing A] [Algebra A L]
  (K K₀ : IntermediateField L (LaurentSeries L)) (hle₀ : K₀ ≤ K)
  [Algebra A ↥K] [IsScalarTower A L ↥K] [Algebra A ↥K₀] [IsScalarTower A L ↥K₀]

noncomputable def inclA : ↥K₀ →ₐ[A] ↥K where
  toRingHom := (IntermediateField.inclusion hle₀).toRingHom
  commutes' a := by
    apply Subtype.ext
    change ((algebraMap A ↥K₀ a : ↥K₀) : LaurentSeries L) = ((algebraMap A ↥K a : ↥K) : LaurentSeries L)
    rw [IsScalarTower.algebraMap_apply A L ↥K₀, IsScalarTower.algebraMap_apply A L ↥K]
    rfl

theorem coe_inclA_apply (x : ↥K₀) : ((inclA L A K K₀ hle₀ x : ↥K) : LaurentSeries L) = (x : LaurentSeries L) := rfl

variable (j : ↥K) (j₀ : ↥K₀) (hjj : (j₀ : LaurentSeries L) = (j : LaurentSeries L))

include hjj in
theorem inclA_j₀ : inclA L A K K₀ hle₀ j₀ = j := Subtype.ext hjj

include hjj in

theorem inclA_mem_chartAlgFin (b : ↥(chartAlgFin A ↥K₀ j₀)) : inclA L A K K₀ hle₀ (b : ↥K₀) ∈ chartAlgFin A ↥K j := by
  have hb : IsIntegral ↥(Algebra.adjoin A ({j₀} : Set ↥K₀)) (b : ↥K₀) := b.2
  have hle : Algebra.adjoin A ({j₀} : Set ↥K₀) ≤ (Algebra.adjoin A ({j} : Set ↥K)).comap (inclA L A K K₀ hle₀) := by
    refine Algebra.adjoin_le ?_
    intro t ht
    rw [Set.mem_singleton_iff.mp ht]
    change j₀ ∈ (Algebra.adjoin A ({j} : Set ↥K)).comap (inclA L A K K₀ hle₀)
    rw [Subalgebra.mem_comap, inclA_j₀ L A K K₀ hle₀ j j₀ hjj]
    exact Algebra.self_mem_adjoin_singleton A j
  have hmap : ∀ x : ↥(Algebra.adjoin A ({j₀} : Set ↥K₀)), inclA L A K K₀ hle₀ (x : ↥K₀) ∈ Algebra.adjoin A ({j} : Set ↥K) :=
    fun x => (Subalgebra.mem_comap ..).1 (hle x.2)
  let ψ : ↥(Algebra.adjoin A ({j₀} : Set ↥K₀)) →+* ↥(Algebra.adjoin A ({j} : Set ↥K)) :=
    ((inclA L A K K₀ hle₀).toRingHom.comp (Algebra.adjoin A ({j₀} : Set ↥K₀)).val.toRingHom).codRestrict
      (Algebra.adjoin A ({j} : Set ↥K)) (fun x => hmap x)
  exact hb.map_of_comp_eq ψ (inclA L A K K₀ hle₀).toRingHom (by ext x; rfl)

noncomputable def iota : ↥(chartAlgFin A ↥K₀ j₀) →+* ↥(chartAlgFin A ↥K j) :=
  ((inclA L A K K₀ hle₀).toRingHom.comp (chartAlgFin A ↥K₀ j₀).val.toRingHom).codRestrict (chartAlgFin A ↥K j)
    (fun b => inclA_mem_chartAlgFin L A K K₀ hle₀ j j₀ hjj b)

theorem coe_iota_apply (b : ↥(chartAlgFin A ↥K₀ j₀)) :
    ((iota L A K K₀ hle₀ j j₀ hjj b : ↥(chartAlgFin A ↥K j)) : ↥K) = IntermediateField.inclusion hle₀ (b : ↥K₀) := rfl

end Incl

theorem gamma0_mul_le (q M' : ℕ) : CongruenceSubgroup.Gamma0 (q * M') ≤ CongruenceSubgroup.Gamma0 M' := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma0_mem] at hγ ⊢
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ ⊢
  exact (dvd_trans (by exact_mod_cast (dvd_mul_left M' q : M' ∣ q * M')) hγ)

theorem laurentBaseChange_gamma0_le_gamma0_mul (L : Type) [Field L] [CharZero L] (q M' : ℕ) :
    ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) ≤
      ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q * M'))) := by
  have hle : ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M') ≤
      ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q * M')) :=
    ModularCurve.qExpFunctionFieldC_mono ℚ (gamma0_mul_le q M')
  exact IntermediateField.adjoin.mono L _ _ (Set.image_mono (fun x hx => hle hx))

end P4Aux

namespace OrdRegWAT

open IsLocalRing AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem ringLevel_of_WAT
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)] (htj : Transcendental A j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (y : Ideal ↥(chartAlgFin A (↥K) j)) [hmax : y.IsMaximal]
    (hyϖ : algebraMap A (↥(chartAlgFin A (↥K) j)) ϖ ∈ y)

    (K' : IntermediateField L (LaurentSeries L)) (hle : K' ≤ K)
    [Algebra A ↥K'] [IsScalarTower A L ↥K']
    (j' : ↥K') [Fact (j' ≠ 0)] (hjj' : (IntermediateField.inclusion hle j' : ↥K) = j)
    (htj' : Transcendental A j')
    (hFD' : FiniteDimensional ↥(IntermediateField.adjoin L ({j'} : Set ↥K')) ↥K')
    (hsmooth : Smooth (toBase A (↥K') j'))
    [Algebra ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)]
    [IsScalarTower A ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)]
    (hι : ∀ x : ↥(chartAlgFin A (↥K') j'),
      ((algebraMap ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j) x : ↥(chartAlgFin A (↥K) j)) : ↥K) = IntermediateField.inclusion hle (x : ↥K'))

    (K'' : IntermediateField L (LaurentSeries L)) (hle'' : K'' ≤ K)
    [Algebra A ↥K''] [IsScalarTower A L ↥K'']
    (j'' : ↥K'') [Fact (j'' ≠ 0)] (hjj'' : (IntermediateField.inclusion hle'' j'' : ↥K) = j)
    (htj'' : Transcendental A j'')
    (hFD'' : FiniteDimensional ↥(IntermediateField.adjoin L ({j''} : Set ↥K'')) ↥K'')
    [Algebra ↥(chartAlgFin A (↥K'') j'') ↥(chartAlgFin A (↥K) j)]
    [IsScalarTower A ↥(chartAlgFin A (↥K'') j'') ↥(chartAlgFin A (↥K) j)]
    (hι'' : ∀ x : ↥(chartAlgFin A (↥K'') j''),
      ((algebraMap ↥(chartAlgFin A (↥K'') j'') ↥(chartAlgFin A (↥K) j) x : ↥(chartAlgFin A (↥K) j)) : ↥K) = IntermediateField.inclusion hle'' (x : ↥K''))
    [Algebra ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K'') j'')]
    [IsScalarTower ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K'') j'') ↥(chartAlgFin A (↥K) j)]

    (𝔔₀ : Ideal ↥(chartAlgFin A (↥K') j')) [𝔔₀.IsPrime]
    (h𝔔₀y : 𝔔₀ ≤ y.comap (algebraMap ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)))
    (h𝔔₀ϖ : algebraMap A ↥(chartAlgFin A (↥K') j') ϖ ∉ 𝔔₀)
    (h𝔔₀reg : ∀ (O : Type) [CommRing O] [IsLocalRing O] [Algebra ↥(chartAlgFin A (↥K') j') O]
      [IsLocalization.AtPrime O (y.comap (algebraMap ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)))],
      Ideal.map (algebraMap ↥(chartAlgFin A (↥K') j') O) 𝔔₀ ⊔ Ideal.span {algebraMap ↥(chartAlgFin A (↥K') j') O (algebraMap A ↥(chartAlgFin A (↥K') j') ϖ)} =
        IsLocalRing.maximalIdeal O)
    (hunr : ∀ (𝔔 : Ideal ↥(chartAlgFin A (↥K) j)) [𝔔.IsPrime], 𝔔 ≤ y → 𝔔.height = 1 →
      𝔔.comap (algebraMap ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)) ≠ 𝔔₀ → Algebra.IsUnramifiedAt ↥(chartAlgFin A (↥K') j') 𝔔)
    (hsep : ∀ h : y.comap (algebraMap ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)) ≤ y.comap (algebraMap ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)),
      letI : Algebra (↥(chartAlgFin A (↥K') j') ⧸ y.comap (algebraMap ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j))) (↥(chartAlgFin A (↥K) j) ⧸ y) :=
        Ideal.Quotient.algebraQuotientOfLEComap h
      Algebra.IsSeparable (↥(chartAlgFin A (↥K') j') ⧸ y.comap (algebraMap ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j))) (↥(chartAlgFin A (↥K) j) ⧸ y))

    (hP2 : Algebra.IsUnramifiedAt ↥(chartAlgFin A (↥K') j') (y.comap (algebraMap ↥(chartAlgFin A (↥K'') j'') ↥(chartAlgFin A (↥K) j))))

    (G : Type) [Group G] [Fintype G] [MulSemiringAction G ↥(chartAlgFin A (↥K) j)]
    [SMulCommClass G ↥(chartAlgFin A (↥K'') j'') ↥(chartAlgFin A (↥K) j)] [FaithfulSMul G ↥(chartAlgFin A (↥K) j)]
    [Algebra.IsInvariant ↥(chartAlgFin A (↥K'') j'') ↥(chartAlgFin A (↥K) j) G]
    (e : ℕ) (he : 0 < e) (hIy : Nat.card ↥(y.inertia G) = e) (hIcyc : IsCyclic ↥(y.inertia G)) (heA : IsUnit ((e : ℕ) : A)) :
    IsRegularLocalRing (Localization.AtPrime y ⧸
      Ideal.span {algebraMap (↥(chartAlgFin A (↥K) j)) (Localization.AtPrime y) (algebraMap A _ ϖ)}) := by
  classical
  haveI := hFD
  haveI := hFD'
  haveI := hFD''
  haveI hsepj : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsSeparable.of_integral _ _

  have hιinj : Function.Injective (algebraMap ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)) := by
    intro a b hab
    have h := congrArg (fun z : ↥(chartAlgFin A (↥K) j) => (z : ↥K)) hab
    simp only [hι] at h
    exact Subtype.ext ((IntermediateField.inclusion hle).injective h)
  have hι''inj : Function.Injective (algebraMap ↥(chartAlgFin A (↥K'') j'') ↥(chartAlgFin A (↥K) j)) := by
    intro a b hab
    have h := congrArg (fun z : ↥(chartAlgFin A (↥K) j) => (z : ↥K)) hab
    simp only [hι''] at h
    exact Subtype.ext ((IntermediateField.inclusion hle'').injective h)
  haveI hfinAA : Module.Finite ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j) :=
    OrdRegSeams.finite_chartAlgFin_of_floor A L K K' hle j j' hjj' htj hFD hι
  haveI hfinAA'' : Module.Finite ↥(chartAlgFin A (↥K'') j'') ↥(chartAlgFin A (↥K) j) :=
    OrdRegSeams.finite_chartAlgFin_of_floor A L K K'' hle'' j j'' hjj'' htj hFD hι''
  haveI : IsNoetherianRing ↥(chartAlgFin A (↥K') j') := by
    haveI : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j'} : Set ↥K')) ↥K' := Algebra.IsSeparable.of_integral _ _
    obtain ⟨hft, -⟩ := AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K') j' htj' hFD' inferInstance
    exact Algebra.FiniteType.isNoetherianRing A _
  haveI : IsNoetherianRing ↥(chartAlgFin A (↥K'') j'') := by
    haveI : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j''} : Set ↥K'')) ↥K'' := Algebra.IsSeparable.of_integral _ _
    obtain ⟨hft, -⟩ := AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K'') j'' htj'' hFD'' inferInstance
    exact Algebra.FiniteType.isNoetherianRing A _
  haveI : IsNoetherianRing ↥(chartAlgFin A (↥K) j) := by
    obtain ⟨hft, -⟩ := AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD inferInstance
    exact Algebra.FiniteType.isNoetherianRing A _
  haveI : IsIntegrallyClosed ↥(chartAlgFin A (↥K'') j'') := AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg A (↥K'') _
  haveI : IsIntegrallyClosed ↥(chartAlgFin A (↥K) j) := AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg A (↥K) _
  haveI : FaithfulSMul ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hιinj
  haveI : FaithfulSMul ↥(chartAlgFin A (↥K'') j'') ↥(chartAlgFin A (↥K) j) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hι''inj

  haveI : Algebra.IsIntegral ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j) := inferInstance
  haveI hy'max : (y.comap (algebraMap ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal y
  have hy'ϖ : algebraMap A ↥(chartAlgFin A (↥K') j') ϖ ∈ y.comap (algebraMap ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)) := by
    show algebraMap _ (↥(chartAlgFin A (↥K) j)) (algebraMap A ↥(chartAlgFin A (↥K') j') ϖ) ∈ y
    rw [← IsScalarTower.algebraMap_apply]; exact hyϖ
  obtain ⟨hRreg, hRdim, -, hRfib1, -⟩ :=
    OrdRegL2.L2_floor_regular_of_smooth L K' A j' htj' hFD' hsmooth ϖ hϖ
      (y.comap (algebraMap ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j))) hy'ϖ

  exact WATCore.WATcore ϖ y hRreg hRdim hRfib1 𝔔₀ h𝔔₀y h𝔔₀ϖ (h𝔔₀reg _) hunr hsep hP2 e he hIy hIcyc heA

end OrdRegWAT

open AlgebraicCurve.TwoChartIntegralModel in
set_option maxHeartbeats 6400000 in
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
    (hιb : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀), ((ι b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = IntermediateField.inclusion hle₀ (b : ↥K₀))
    (hfloor : Smooth (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K₀) j₀))

    (𝔔₀ : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀)) [𝔔₀.IsPrime]
    (h𝔔₀y : 𝔔₀ ≤ (y.asIdeal).comap ι) (h𝔔₀ϖ : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ϖ ∉ 𝔔₀)

    (h𝔔₀reg : ∀ (O : Type) [CommRing O] [IsLocalRing O] [Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) O]
      [IsLocalization.AtPrime O ((y.asIdeal).comap ι)],
      Ideal.map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) O) 𝔔₀ ⊔ Ideal.span {algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) O (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ϖ)} = IsLocalRing.maximalIdeal O) :
    letI : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := ι.toAlgebra

    (∀ (𝔔 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) [𝔔.IsPrime], 𝔔 ≤ y.asIdeal → 𝔔.height = 1 → 𝔔.comap ι ≠ 𝔔₀ →
      Algebra.IsUnramifiedAt ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) 𝔔) →

    (∀ h : (y.asIdeal).comap ι ≤ (y.asIdeal).comap (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
      letI : Algebra (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ⧸ (y.asIdeal).comap ι) (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ y.asIdeal) := Ideal.Quotient.algebraQuotientOfLEComap h
      Algebra.IsSeparable (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ⧸ (y.asIdeal).comap ι) (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ y.asIdeal)) →
    IsRegularLocalRing (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ⧸ Ideal.span {ϖz}) := by
  intro hunr hsep
  classical
  letI algK : Algebra ↥K₀ ↥K := (IntermediateField.inclusion hle₀).toRingHom.toAlgebra
  letI algι : Algebra ↥(chartAlgFin A (↥K₀) j₀) ↥(chartAlgFin A (↥K) j) := ι.toAlgebra
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
  have hjj' : (IntermediateField.inclusion hle₀ j₀ : ↥K) = j :=
    Subtype.ext (show ((j₀ : ↥K₀) : LaurentSeries L) = (j : LaurentSeries L) by rw [hj₀, hj])

  haveI : IsScalarTower A ↥(chartAlgFin A (↥K₀) j₀) ↥(chartAlgFin A (↥K) j) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    apply Subtype.ext
    show ((algebraMap A ↥(chartAlgFin A (↥K) j) a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((ι (algebraMap A ↥(chartAlgFin A (↥K₀) j₀) a)) : ↥K)
    rw [hιb]
    apply Subtype.ext
    show ((algebraMap A ↥K a) : LaurentSeries L) = ((algebraMap A ↥K₀ a : ↥K₀) : LaurentSeries L)
    rw [IsScalarTower.algebraMap_apply A L ↥K, IsScalarTower.algebraMap_apply A L ↥K₀]
    rfl
  have hyϖ : algebraMap A (↥(chartAlgFin A (↥K) j)) ϖ ∈ y.asIdeal :=
    OrdRegL0.algebraMap_mem_asIdeal_of_germ_mem_maximalIdeal A (↥K) j ϖ z ϖz hϖz hz y hy

  obtain ⟨K₀', hK₀'⟩ : ∃ K₀' : IntermediateField L (LaurentSeries L),
      K₀' = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q * M'))) := ⟨_, rfl⟩
  have hle' : K₀' ≤ K := by
    rw [hK, hK₀']
    exact ModularCurve.laurentBaseChange_qExpFunctionFieldC_gamma0_le_laurentBaseChange_xHFunctionField L (q * M') (q ^ 2 * M')
      ⟨q, by ring⟩ (ModularCurve.FullLevel.levelH q M')
  have hle₀' : K₀ ≤ K₀' := by
    rw [hK₀, hK₀']
    exact P4Aux.laurentBaseChange_gamma0_le_gamma0_mul L q M'
  letI algAK₀' : Algebra A ↥K₀' := ((algebraMap L ↥K₀').comp (algebraMap A L)).toAlgebra
  haveI istAK₀' : IsScalarTower A L ↥K₀' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  obtain ⟨j₀', hj₀'⟩ : ∃ j₀' : ↥K₀', ((j₀' : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq :=
    ⟨⟨(j₀ : LaurentSeries L), hle₀' j₀.2⟩, hj₀⟩
  have hjj₀' : (j₀' : LaurentSeries L) = (j : LaurentSeries L) := hj₀'.trans hj.symm
  have hjj₀₀' : (j₀ : LaurentSeries L) = (j₀' : LaurentSeries L) := hj₀.trans hj₀'.symm
  haveI hj₀'0 : Fact (j₀' ≠ 0) := ⟨fun h => (Fact.out : j ≠ 0) (by
    apply Subtype.ext
    change (j : LaurentSeries L) = ((0 : ↥K) : LaurentSeries L)
    rw [← hjj₀', h]
    rfl)⟩
  have hjj'' : (IntermediateField.inclusion hle' j₀' : ↥K) = j := Subtype.ext hjj₀'
  have hqM'0 : NeZero (q * M') := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (NeZero.ne M')⟩
  have hT₀' : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 (q * M') := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.T]
  haveI hFD₀' := ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
    (CongruenceSubgroup.Gamma0 (q * M')) hT₀' L K₀' hK₀' j₀' hj₀'
  have htj₀' : Transcendental A j₀' := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₀' A j₀' hj₀'

  obtain ⟨ι', hι'⟩ : ∃ ι' : ↥(chartAlgFin A (↥K₀') j₀') →+* ↥(chartAlgFin A (↥K) j),
      ∀ b : ↥(chartAlgFin A (↥K₀') j₀'), ((ι' b : ↥(chartAlgFin A (↥K) j)) : ↥K) = IntermediateField.inclusion hle' (b : ↥K₀') :=
    ⟨P4Aux.iota L A K K₀' hle' j j₀' hjj₀', fun b => rfl⟩
  obtain ⟨ι₀', hι₀'⟩ : ∃ ι₀' : ↥(chartAlgFin A (↥K₀) j₀) →+* ↥(chartAlgFin A (↥K₀') j₀'),
      ∀ b : ↥(chartAlgFin A (↥K₀) j₀), ((ι₀' b : ↥(chartAlgFin A (↥K₀') j₀')) : ↥K₀') = IntermediateField.inclusion hle₀' (b : ↥K₀) :=
    ⟨P4Aux.iota L A K₀' K₀ hle₀' j₀' j₀ hjj₀₀', fun b => rfl⟩
  have hιι : ∀ b : ↥(chartAlgFin A (↥K₀) j₀), ι b = ι' (ι₀' b) := by
    intro b
    apply Subtype.ext
    rw [hιb, hι']
    apply Subtype.ext
    show ((b : ↥K₀) : LaurentSeries L) = (((ι₀' b : ↥(chartAlgFin A (↥K₀') j₀')) : ↥K₀') : LaurentSeries L)
    rw [hι₀']
    rfl
  letI algι' : Algebra ↥(chartAlgFin A (↥K₀') j₀') ↥(chartAlgFin A (↥K) j) := ι'.toAlgebra
  letI algι₀' : Algebra ↥(chartAlgFin A (↥K₀) j₀) ↥(chartAlgFin A (↥K₀') j₀') := ι₀'.toAlgebra
  haveI : IsScalarTower ↥(chartAlgFin A (↥K₀) j₀) ↥(chartAlgFin A (↥K₀') j₀') ↥(chartAlgFin A (↥K) j) :=
    IsScalarTower.of_algebraMap_eq (fun b => hιι b)
  haveI : IsScalarTower A ↥(chartAlgFin A (↥K₀') j₀') ↥(chartAlgFin A (↥K) j) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    apply Subtype.ext
    show ((algebraMap A ↥(chartAlgFin A (↥K) j) a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((ι' (algebraMap A ↥(chartAlgFin A (↥K₀') j₀') a)) : ↥K)
    rw [hι']
    apply Subtype.ext
    show ((algebraMap A ↥K a) : LaurentSeries L) = ((algebraMap A ↥K₀' a : ↥K₀') : LaurentSeries L)
    rw [IsScalarTower.algebraMap_apply A L ↥K, IsScalarTower.algebraMap_apply A L ↥K₀']
    rfl

  have hP2 := ModularCurve.FullLevel.isUnramifiedAt_chartAlgFin_gamma0_mul_comap_of_not_mem_ssJSet_xH
    q hq M' hqM' L ζ hζ hι K hK A hAq hζA j hj ϖ hϖ W₀ hW₀ z ϖz hϖz hz y hy hmax Ω φ hφ hord hz₀ K₀ hK₀ hle₀ j₀ hj₀ ι hιb hfloor
    K₀' hK₀' hle₀' hle' j₀' hj₀' ι₀' hι₀' ι' hι' hιι

  obtain ⟨G, _, _, _, _, _, _, e, he, hIy, hIcyc, heA⟩ :=
    ModularCurve.FullLevel.exists_mulSemiringAction_isInvariant_chartAlgFin_isCyclic_inertia_of_not_mem_ssJSet_xH
      q hq M' hqM' L ζ hζ hι K hK A hAq hζA j hj ϖ hϖ W₀ hW₀ z ϖz hϖz hz y hy hmax Ω φ hφ hord hz₀ K₀ hK₀ hle₀
      K₀' hK₀' hle' j₀' hj₀' ι' hι'

  exact OrdRegL0.L0_isRegularLocalRing_fibre_of_localization A (↥K) j ϖ z ϖz hϖz y hy
    (OrdRegWAT.ringLevel_of_WAT L K A j htj hFD ϖ hϖ y.asIdeal hyϖ K₀ hle₀ j₀ hjj' htj₀ hFD₀ hfloor hιb
      K₀' hle' j₀' hjj'' htj₀' hFD₀' hι' 𝔔₀ h𝔔₀y h𝔔₀ϖ h𝔔₀reg hunr hsep hP2 G e he hIy hIcyc heA)

end S_ModularCurve_FullLevel_isRegularLocalRing_fibre_of_forall_height_one_isUnramifiedAt_off_section_xH_of_isSeparable
end P2MW
export P2MW.S_ModularCurve_FullLevel_isRegularLocalRing_fibre_of_forall_height_one_isUnramifiedAt_off_section_xH_of_isSeparable (solution)
