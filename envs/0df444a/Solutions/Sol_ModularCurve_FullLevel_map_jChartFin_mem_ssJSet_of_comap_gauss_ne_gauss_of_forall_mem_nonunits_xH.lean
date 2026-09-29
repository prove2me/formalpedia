-- Prove2me | solution 1 for ModularCurve.FullLevel.map_jChartFin_mem_ssJSet_of_comap_gauss_ne_gauss_of_forall_mem_nonunits_xH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/2f198278-1a2d-5ae9-8424-75f9e68478f3

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_QAdicPlace
import Theorems.Thm_ModularCurve_FullLevel_forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_not_mem_ssJSet_xH_of_isAlgebraic
import Theorems.Thm_ModularCurve_FullLevel_exists_comap_eq_and_ramificationIdx_eq_one_and_isSeparable_of_over_gauss_gamma0_mul_xH
import Theorems.Thm_ModularCurve_FullLevel_algebraMap_mem_comap_gauss_iff_of_isLevelAutAt
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
import Theorems.Thm_ModularCurve_qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_mem_ssJSet_of_pow_mem_ssJSet
import Theorems.Thm_ModularCurve_FullLevel_exists_qExpand_mem_gauss_xor_mem_comap_gauss_of_dvd_of_not_dvd_of_isLevelAutAt
import Theorems.Thm_ModularCurve_exists_gaussPresentation_qExpand_iff
import Theorems.Thm_ModularCurve_FullLevel_map_jChartFin_mem_ssJSet_of_exists_two_minimalPrimes_span_le_chartAlgFin_of_algEquiv_laurentBaseChange_gamma0_mul
import Theorems.Thm_ModularCurve_laurentBaseChange_qExpFunctionFieldC_gamma0_le_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul
import Theorems.Thm_ModularCurve_FullLevel_exists_subgroup_finite_mem_iff_exists_eq_of_isLevelAutAt
import Theorems.Thm_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand
import Theorems.Thm_ModularCurve_FullLevel_comap_gauss_eq_comap_gauss_iff_redQ_inv_smul_lineInfty_eq_of_isLevelAutAt_of_isAlgebraic
import Theorems.Thm_ModularCurve_FullLevel_dvd_of_redQ_smul_lineInfty_eq
import Theorems.Thm_ModularCurve_FullLevel_exists_ringHom_fieldBar_comap_gauss_iff_of_isAlgebraic
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_apply_eq_of_isLevelAutAt_of_coe_eq_coeffMap
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_mul
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand
import Theorems.Thm_ModularCurve_FullLevel_map_jChartFin_mem_ssJSet_of_exists_two_minimalPrimes_span_le_chartAlgFin_laurentBaseChange_gamma0_mul
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_map_jChartFin_mem_ssJSet_of_comap_gauss_ne_gauss_of_forall_mem_nonunits_xH
p2m_attr_erase "instance" "ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1"
p2m_attr_erase "instance" "isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange ModularCurve.instIsElliptic_tateBase ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_heckeBetaBarRingHom"
p2m_attr_erase "simp" "ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq"
p2m_attr_erase "simp" "TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁"
p2m_attr_erase "simp" "TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.coe_baseChangeRingHom ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ"
p2m_attr_erase "simp" "ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero ModularCurve.LevelN.coe_jGen ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply"
p2m_attr_erase "simp" "ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

namespace IGXR9Pres

p2m_open "ModularCurve~coeffMap_qExpand~coeffEmb_qExpand"

open HahnSeries

section Pres

variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]

noncomputable abbrev toL (L : Type) [Field L] [Algebra A L] (x : PowerSeries A) : LaurentSeries L :=
  ofPowerSeries ℤ L (x.map (algebraMap A L))

noncomputable abbrev toκ (x : PowerSeries A) : LaurentSeries (IsLocalRing.ResidueField A) :=
  ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A))

variable (L) in

def Pres (f : LaurentSeries L) (x y : PowerSeries A) : Prop :=
  y.map (IsLocalRing.residue A) ≠ 0 ∧ f * toL L y = toL L x

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L] in
@[scoped simp] theorem toL_mul (x y : PowerSeries A) : toL L (x * y) = toL L x * toL L y := by simp [toL, map_mul]
omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L] in
@[scoped simp] theorem toL_sub (x y : PowerSeries A) : toL L (x - y) = toL L x - toL L y := by simp [toL, map_sub]
omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L] in
@[scoped simp] theorem toL_one : toL L (1 : PowerSeries A) = 1 := by simp [toL]
omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L] in
@[scoped simp] theorem toL_zero : toL L (0 : PowerSeries A) = 0 := by simp [toL]
omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L] in
@[scoped simp] theorem toL_pow (x : PowerSeries A) (n : ℕ) : toL L (x ^ n) = toL L x ^ n := by simp [toL, map_pow]
omit [IsFractionRing A L] in
@[scoped simp] theorem toκ_mul (x y : PowerSeries A) : toκ (x * y) = toκ x * toκ y := by simp [toκ, map_mul]
omit [IsFractionRing A L] in
@[scoped simp] theorem toκ_sub (x y : PowerSeries A) : toκ (x - y) = toκ x - toκ y := by simp [toκ, map_sub]
omit [IsFractionRing A L] in
@[scoped simp] theorem toκ_pow (x : PowerSeries A) (n : ℕ) : toκ (x ^ n) = toκ x ^ n := by simp [toκ, map_pow]
omit [IsFractionRing A L] in
@[scoped simp] theorem toκ_zero : toκ (0 : PowerSeries A) = 0 := by simp [toκ]
omit [IsFractionRing A L] in
theorem toκ_eq_zero_iff (x : PowerSeries A) : toκ x = 0 ↔ x.map (IsLocalRing.residue A) = 0 := by
  constructor
  · intro e; exact ofPowerSeries_injective (e.trans (map_zero _).symm)
  · intro e; rw [toκ, e, map_zero]

omit [IsDomain A] [IsDiscreteValuationRing A] in
theorem toL_injective : Function.Injective (toL (A := A) L) := fun x y h =>
  PowerSeries.map_injective (algebraMap A L) (IsFractionRing.injective A L) (ofPowerSeries_injective h)

theorem Pres.mul {f g : LaurentSeries L} {x y x' y' : PowerSeries A}
    (hf : Pres L f x y) (hg : Pres L g x' y') : Pres L (f * g) (x * x') (y * y') := by
  refine ⟨by rw [map_mul]; exact mul_ne_zero hf.1 hg.1, ?_⟩
  rw [toL_mul, toL_mul, ← hf.2, ← hg.2]; ring

theorem Pres.pow {f : LaurentSeries L} {x y : PowerSeries A} (hf : Pres L f x y) (n : ℕ) :
    Pres L (f ^ n) (x ^ n) (y ^ n) := by
  induction n with
  | zero => exact ⟨by simp, by simp⟩
  | succ n ih => simpa [pow_succ] using ih.mul hf

theorem Pres.sub {f g : LaurentSeries L} {x y x' y' : PowerSeries A}
    (hf : Pres L f x y) (hg : Pres L g x' y') : Pres L (f - g) (x * y' - x' * y) (y * y') := by
  refine ⟨by rw [map_mul]; exact mul_ne_zero hf.1 hg.1, ?_⟩
  rw [toL_mul, toL_sub, toL_mul, toL_mul, ← hf.2, ← hg.2]; ring

omit [IsFractionRing A L] in
theorem Pres.one : Pres L (1 : LaurentSeries L) (1 : PowerSeries A) 1 :=
  ⟨by simp, by simp⟩

theorem Pres.unique {f : LaurentSeries L} {x y x' y' : PowerSeries A}
    (h : Pres L f x y) (h' : Pres L f x' y') :
    x.map (IsLocalRing.residue A) * y'.map (IsLocalRing.residue A)
      = x'.map (IsLocalRing.residue A) * y.map (IsLocalRing.residue A) := by
  have : toL L (x * y') = toL L (x' * y) := by
    rw [toL_mul, toL_mul, ← h.2, ← h'.2]; ring
  have := toL_injective this
  rw [← map_mul, ← map_mul, this]

theorem Pres.ne_zero {f : LaurentSeries L} {x y : PowerSeries A} (h : Pres L f x y)
    (hx : x.map (IsLocalRing.residue A) ≠ 0) : f ≠ 0 := by
  rintro rfl
  have h2 := h.2
  rw [zero_mul, eq_comm] at h2
  have : x = 0 := toL_injective (L := L) (h2.trans (toL_zero (L := L)).symm)
  exact hx (by simp [this])

theorem Pres.inv {f : LaurentSeries L} {x y : PowerSeries A} (h : Pres L f x y)
    (hx : x.map (IsLocalRing.residue A) ≠ 0) : Pres L f⁻¹ y x := by
  refine ⟨hx, ?_⟩
  have hf := h.ne_zero hx
  rw [← h.2, ← mul_assoc, inv_mul_cancel₀ hf, one_mul]

theorem Pres.map_ne_zero_of_inv {f : LaurentSeries L} {x y x' y' : PowerSeries A}
    (h : Pres L f x y) (hf : f ≠ 0) (h' : Pres L f⁻¹ x' y') :
    x.map (IsLocalRing.residue A) ≠ 0 := by
  have hp := h.mul h'
  rw [mul_inv_cancel₀ hf] at hp
  have hu := hp.unique Pres.one
  simp only [map_mul, map_one, mul_one, one_mul] at hu
  intro hx0
  rw [hx0, zero_mul] at hu
  exact mul_ne_zero h.1 h'.1 hu.symm

theorem Pres.red_eq {f : LaurentSeries L} {x y x' y' : PowerSeries A}
    (h : Pres L f x y) (h' : Pres L f x' y') :
    toκ x / toκ y = toκ x' / toκ y' := by
  have hy : toκ y ≠ 0 := fun e => h.1 ((toκ_eq_zero_iff y).mp e)
  have hy' : toκ y' ≠ 0 := fun e => h'.1 ((toκ_eq_zero_iff y').mp e)
  have e := congrArg (ofPowerSeries ℤ (IsLocalRing.ResidueField A)) (h.unique h')
  rw [map_mul, map_mul] at e
  rw [div_eq_div_iff hy hy']
  exact e

end Pres

end IGXR9Pres
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_map_jChartFin_mem_ssJSet_of_comap_gauss_ne_gauss_of_forall_mem_nonunits_xH.IGXR9Pres"

namespace IGXR9

p2m_open "ModularCurve~coeffMap_qExpand~coeffEmb_qExpand HahnSeries P2MW.S_ModularCurve_FullLevel_map_jChartFin_mem_ssJSet_of_comap_gauss_ne_gauss_of_forall_mem_nonunits_xH.IGXR9Pres"

theorem coeffEmb_qExpand (L : Type) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] (x : LaurentSeries ℚ) :
    coeffEmb L (qExpand ℚ N x) = qExpand L N (coeffEmb L x) := by
  ext k
  rw [coeffEmb_coeff]
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [qExpand_coeff_of_not_dvd N x hk, qExpand_coeff_of_not_dvd N _ hk, map_zero]

theorem qExpand_j_sub_pow_mem_nonunits_gauss
    (q : ℕ) [Fact q.Prime]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    (j xj : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    (hxj : ((xj : LaurentSeries L)) = ModularCurve.qExpand L q (ModularCurve.coeffEmb L ModularCurve.jq))
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    xj - j ^ q ∈ W₀.nonunits := by
  classical
  have hxj' : ((xj : LaurentSeries L)) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ q ModularCurve.jq) := by
    rw [hxj, coeffEmb_qExpand]
  obtain ⟨⟨x₀, y₀, hy₀, hj₀, hr₀⟩, ⟨x₁, y₁, hy₁, hj₁, hr₁⟩⟩ :=
    ModularCurve.exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand q L A hAq
  have Pj : Pres L ((j : ↥K) : LaurentSeries L) x₀ y₀ := ⟨hy₀, by rw [hj]; exact hj₀⟩
  have Pσj : Pres L ((xj : ↥K) : LaurentSeries L) x₁ y₁ := ⟨hy₁, by rw [hxj']; exact hj₁⟩
  have hy₀κ : toκ y₀ ≠ 0 := fun e => hy₀ ((toκ_eq_zero_iff y₀).mp e)
  have hy₁κ : toκ y₁ ≠ 0 := fun e => hy₁ ((toκ_eq_zero_iff y₁).mp e)
  have hx₀ : toκ x₀ = ModularCurve.jqModC _ * toκ y₀ := by rw [← hr₀, div_mul_cancel₀ _ hy₀κ]
  have hx₁ : toκ x₁ = ModularCurve.jqModC _ ^ q * toκ y₁ := by rw [← hr₁, div_mul_cancel₀ _ hy₁κ]

  have Pg : Pres L (((xj - j ^ q : ↥K)) : LaurentSeries L) (x₁ * y₀ ^ q - x₀ ^ q * y₁) (y₁ * y₀ ^ q) := by
    push_cast; exact Pσj.sub (Pj.pow q)
  have hX : (x₁ * y₀ ^ q - x₀ ^ q * y₁).map (IsLocalRing.residue A) = 0 := by
    rw [← toκ_eq_zero_iff, toκ_sub, toκ_mul, toκ_mul, toκ_pow, toκ_pow, hx₀, hx₁]; ring
  rw [ValuationSubring.mem_nonunits_iff_or]
  by_cases h0 : xj - j ^ q = 0
  · exact Or.inl h0
  right
  intro hinv
  obtain ⟨x', y', hy', h'⟩ := (hW₀ _).mp hinv
  have hg0 : (((xj - j ^ q : ↥K)) : LaurentSeries L) ≠ 0 := by
    intro e; apply h0; exact_mod_cast e
  have P' : Pres L ((((xj - j ^ q : ↥K)) : LaurentSeries L))⁻¹ x' y' := by
    refine ⟨hy', ?_⟩
    have e := h'
    push_cast at e ⊢
    exact e
  exact Pg.map_ne_zero_of_inv hg0 P' hX

end IGXR9
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_map_jChartFin_mem_ssJSet_of_comap_gauss_ne_gauss_of_forall_mem_nonunits_xH.IGXR9Pres"

namespace IGXBranch

p2m_open "ModularCurve~coeffMap_qExpand~coeffEmb_qExpand CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel"

universe u

theorem mem_nonunits_iff' {K : Type*} [Field K] (W : ValuationSubring K) (a : K) :
    a ∈ W.nonunits ↔ a = 0 ∨ a⁻¹ ∉ W := by
  rw [ValuationSubring.mem_nonunits_iff]
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [← W.valuation_le_one_iff, map_inv₀, inv_le_one₀ ((Valuation.pos_iff _).mpr ha), not_le]
    simp [ha]

theorem mem_nonunits_iff_map_mem_nonunits {K K' : Type*} [Field K] [Field K'] (φ : K →+* K')
    (W : ValuationSubring K) (W' : ValuationSubring K') (h : ∀ x, x ∈ W ↔ φ x ∈ W') (a : K) :
    a ∈ W.nonunits ↔ φ a ∈ W'.nonunits := by
  rw [mem_nonunits_iff', mem_nonunits_iff', map_eq_zero_iff φ φ.injective, ← map_inv₀, h]

theorem mem_minimalPrimes_span_singleton_of_height_eq_one
    {B : Type u} [CommRing B] (x : B) (hx : x ∈ nonZeroDivisors B)
    (Q : Ideal B) [Q.IsPrime] (hxQ : x ∈ Q) (hQ : Q.height = 1) :
    Q ∈ (Ideal.span {x}).minimalPrimes := by
  have hle : Ideal.span {x} ≤ Q := (Ideal.span_singleton_le_iff_mem _).mpr hxQ
  haveI : Q.FiniteHeight := Ideal.finiteHeight_iff_lt.mpr (Or.inr (by rw [hQ]; exact ENat.one_lt_top))
  apply Ideal.mem_minimalPrimes_of_height_eq hle
  rw [hQ]
  exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors hx

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

theorem coeffEmb_qExpand (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n]
    (x : LaurentSeries ℚ) : coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) :=
  coeffMap_qExpand _ n x

theorem coeffEmb_jq_mem_gamma0 (N : ℕ) [NeZero N] (L : Type) [Field L] [CharZero L] :
    coeffEmb L jq ∈ laurentBaseChange L (qExpFunctionFieldC ℚ (Gamma0 N)) := by
  rw [ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]
  exact ModularCurve.coeffEmb_mem_laurentBaseChange L (ModularCurve.jq_mem_full (N := N))

theorem coeffEmb_jq_ne_zero (L : Type) [Field L] [CharZero L] : coeffEmb L jq ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : LaurentSeries L => f.coeff (-1)) h
  simp only [coeffEmb_coeff, coeff_jq_neg_one, map_one] at h1
  exact one_ne_zero (h1.trans (by simp))

theorem chartAlg_singleton_le {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F]
    {s t : F} (hs : s ∈ chartAlg R F {t}) : chartAlg R F {s} ≤ chartAlg R F {t} := by
  intro x hx
  rw [mem_chartAlg_iff] at hx ⊢

  have hle : Algebra.adjoin R ({s} : Set F) ≤ chartAlg R F {t} :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hs)
  letI alg1 : Algebra ↥(Algebra.adjoin R ({t} : Set F)) ↥(chartAlg R F {t}) :=
    (Subalgebra.inclusion (adjoin_le_chartAlg R F {t})).toRingHom.toAlgebra
  haveI : IsScalarTower ↥(Algebra.adjoin R ({t} : Set F)) ↥(chartAlg R F {t}) F :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral ↥(Algebra.adjoin R ({t} : Set F)) ↥(chartAlg R F {t}) := by
    refine ⟨fun z => ?_⟩
    have hz : IsIntegral ↥(Algebra.adjoin R ({t} : Set F)) (z : F) := z.2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥(Algebra.adjoin R ({t} : Set F)) ↥(chartAlg R F {t}) F)
      Subtype.val_injective).mp hz

  have hx' : IsIntegral ↥(chartAlg R F {t}) x :=
    hx.map_of_comp_eq (Subalgebra.inclusion hle).toRingHom (RingHom.id F) (by ext; rfl)
  exact isIntegral_trans x hx'

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_jChart_qExpand_mem_ssJSet
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
    (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω)
    (hφ : RingHom.ker φ = y.asIdeal)
    (τ : SL(2, ℤ) → (↥K ≃ₐ[L] ↥K))
    (hτ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') γ⁻¹ K (τ γ))
    (hz₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y.asIdeal)

    (γ'' : SL(2, ℤ)) (hγ'' : γ'' ∈ CongruenceSubgroup.Gamma0 M')
    (hz₁'' : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
      (b : ↥K) ∈ (W₀.comap (τ γ'').toAlgHom.toRingHom).nonunits → b ∈ y.asIdeal)
    (g : LaurentSeries L) (x : ↥K)
    (hg : g ∈ ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q * M'))))
    (hx : (x : LaurentSeries L) = ModularCurve.qExpand L q g)
    (hsep : ¬ (x ∈ W₀.comap (τ γ'').toAlgHom.toRingHom ↔ x ∈ W₀)) :
    ∃ xj : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
      ((xj : ↥K) : LaurentSeries L) = ModularCurve.qExpand L q (ModularCurve.coeffEmb L ModularCurve.jq) ∧
      φ xj ∈ ModularCurve.ssJSet q Ω := by
  classical
  have hqp : q.Prime := Fact.out
  haveI : NeZero q := ⟨hqp.ne_zero⟩
  haveI : NeZero (q * M') := ⟨Nat.mul_ne_zero hqp.ne_zero (NeZero.ne M')⟩
  haveI hyP : y.asIdeal.IsPrime := y.isPrime

  obtain ⟨K₀', hK₀'⟩ : ∃ K₀' : IntermediateField L (LaurentSeries L),
      K₀' = laurentBaseChange L (qExpFunctionFieldC ℚ (Gamma0 (q * M'))) := ⟨_, rfl⟩
  letI algAK₀' : Algebra A ↥K₀' := ((algebraMap L ↥K₀').comp (algebraMap A L)).toAlgebra
  haveI towAK₀' := IsScalarTower.of_algebraMap_eq (R := A) (S := L) (A := ↥K₀') (fun _ => rfl)
  have hj₀'mem : coeffEmb L jq ∈ K₀' := by rw [hK₀']; exact coeffEmb_jq_mem_gamma0 (q * M') L
  let j₀' : ↥K₀' := ⟨coeffEmb L jq, hj₀'mem⟩
  have hj₀' : ((j₀' : ↥K₀') : LaurentSeries L) = coeffEmb L jq := rfl
  haveI hj₀'ne : Fact (j₀' ≠ 0) := ⟨fun h => coeffEmb_jq_ne_zero L (congrArg Subtype.val h)⟩
  have hT₀' : ModularGroup.T ∈ Gamma0 (q * M') := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.T]
  haveI hFD₀' := ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
    (Gamma0 (q * M')) hT₀' L K₀' hK₀' j₀' hj₀'
  have htj₀' : Transcendental A j₀' := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₀' A j₀' hj₀'
  haveI : Algebra.IsIntegral ↥(IntermediateField.adjoin L ({j₀'} : Set ↥K₀')) ↥K₀' := by
    haveI := hFD₀'; exact Algebra.IsIntegral.of_finite _ _
  have hsep₀' : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j₀'} : Set ↥K₀')) ↥K₀' :=
    Algebra.IsSeparable.of_integral _ _

  have hβmem : ∀ z : LaurentSeries L, z ∈ K₀' → qExpand L q z ∈ K := by
    intro z hz
    rw [hK₀', mem_laurentBaseChange_iff] at hz
    induction hz using Subfield.closure_induction with
    | mem w hw =>
      rcases hw with ⟨c, rfl⟩ | ⟨g0, hg0, rfl⟩
      · rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero, ← algebraMap_laurentSeries_eq_single]
        exact K.algebraMap_mem c
      · have hg0' : g0 ∈ modularFunctionFieldFull (q * M') := by
          rw [← ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]; exact hg0
        rw [hK]
        exact ModularCurve.qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
          L (q * M') q (q ^ 2 * M') ⟨1, by ring⟩ (ModularCurve.FullLevel.levelH q M') g0 hg0'
    | one => rw [map_one]; exact one_mem K
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | neg a _ ha => rw [map_neg]; exact neg_mem ha
    | inv a _ ha => rw [map_inv₀]; exact inv_mem ha
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let β : ↥K₀' →+* ↥K :=
    { toFun := fun z => ⟨qExpand L q (z : LaurentSeries L), hβmem z z.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hβ : ∀ z : ↥K₀', ((β z : ↥K) : LaurentSeries L) = qExpand L q (z : LaurentSeries L) := fun _ => rfl
  have hβalg : ∀ a : A, β (algebraMap A ↥K₀' a) = algebraMap A ↥K a := by
    intro a
    apply Subtype.ext
    rw [hβ, IsScalarTower.algebraMap_apply A L ↥K]
    show qExpand L q (algebraMap L (LaurentSeries L) (algebraMap A L a)) = algebraMap L (LaurentSeries L) (algebraMap A L a)
    rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

  let βA : ↥K₀' →ₐ[A] ↥K := { β with commutes' := hβalg }
  have hβA : ∀ z, βA z = β z := fun _ => rfl

  have hxjcoe : ((β j₀' : ↥K) : LaurentSeries L) = coeffEmb L (qExpand ℚ q jq) := by
    rw [hβ, hj₀', coeffEmb_qExpand]
  haveI hxjne : Fact (β j₀' ≠ 0) := ⟨fun h => hj₀'ne.out (β.injective (h.trans (map_zero β).symm))⟩
  have hxjA₁ : β j₀' ∈ chartAlgFin A (↥K) j :=
    (ModularCurve.mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand
      q L K A j hj (β j₀') hxjcoe).1

  have hιmem : ∀ b : ↥(chartAlgFin A (↥K₀') j₀'), β (b : ↥K₀') ∈ chartAlgFin A (↥K) j := by
    intro b

    have h1 : β (b : ↥K₀') ∈ chartAlg A (↥K) {β j₀'} := by
      have hadj : ∀ z ∈ Algebra.adjoin A ({j₀'} : Set ↥K₀'), βA z ∈ Algebra.adjoin A ({β j₀'} : Set ↥K) := by
        intro z hz
        have : (Algebra.adjoin A ({j₀'} : Set ↥K₀')).map βA ≤ Algebra.adjoin A ({β j₀'} : Set ↥K) := by
          rw [AlgHom.map_adjoin, Set.image_singleton]
          exact le_of_eq rfl
        exact this ⟨z, hz, rfl⟩
      let ψ : ↥(Algebra.adjoin A ({j₀'} : Set ↥K₀')) →+* ↥(Algebra.adjoin A ({β j₀'} : Set ↥K)) :=
        (βA.toRingHom.comp (Algebra.adjoin A ({j₀'} : Set ↥K₀')).val.toRingHom).codRestrict
          (Algebra.adjoin A ({β j₀'} : Set ↥K)).toSubring (fun z => hadj z z.2)
      rw [mem_chartAlg_iff]
      exact (b.2 : IsIntegral _ (b : ↥K₀')).map_of_comp_eq ψ βA.toRingHom (by ext; rfl)
    exact chartAlg_singleton_le hxjA₁ h1
  let ι : ↥(chartAlgFin A (↥K₀') j₀') →+* ↥(chartAlgFin A (↥K) j) :=
    { toFun := fun b => ⟨β (b : ↥K₀'), hιmem b⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hιb : ∀ b, ((ι b : ↥(chartAlgFin A (↥K) j)) : ↥K) = β (b : ↥K₀') := fun _ => rfl

  obtain ⟨O₀', hO₀', hO₀'A, hO₀'m, hO₀'j, -⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
      (Gamma0 (q * M')) L K₀' hK₀' A j₀' hj₀'
  have hVeq : ∀ z : ↥K₀', z ∈ O₀' ↔ β z ∈ W₀ := by
    intro z
    rw [hO₀', hW₀, hβ]
    exact (ModularCurve.exists_gaussPresentation_qExpand_iff A L q (z : LaurentSeries L)).symm
  have hVnu : ∀ z : ↥K₀', z ∈ O₀'.nonunits ↔ β z ∈ W₀.nonunits :=
    mem_nonunits_iff_map_mem_nonunits β O₀' W₀ hVeq

  have hτxj : τ γ'' (β j₀') = β j₀' :=
    (ModularCurve.FullLevel.forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand
      q hq M' hqM' L ζ hζ hι K hK τ hτ (β j₀')).mpr ⟨coeffEmb L jq, coeffEmb_jq_mem_gamma0 M' L, rfl⟩ γ'' hγ''
  have hτalg : ∀ a : A, τ γ'' (algebraMap A ↥K a) = algebraMap A ↥K a := by
    intro a
    rw [IsScalarTower.algebraMap_apply A L ↥K, AlgEquiv.commutes]
  let τA : ↥K →ₐ[A] ↥K := { (τ γ'').toAlgHom.toRingHom with commutes' := hτalg }
  have hτA : ∀ w, τA w = τ γ'' w := fun _ => rfl
  have hτP : ∀ P : Polynomial A, τ γ'' (β (Polynomial.aeval j₀' P)) = β (Polynomial.aeval j₀' P) := by
    intro P
    rw [← hβA, ← Polynomial.aeval_algHom_apply, hβA, ← hτA, ← Polynomial.aeval_algHom_apply, hτA, hτxj]

  let V' : ValuationSubring ↥K₀' := (W₀.comap (τ γ'').toAlgHom.toRingHom).comap β
  have hV' : ∀ z : ↥K₀', z ∈ V' ↔ τ γ'' (β z) ∈ W₀ := fun _ => Iff.rfl
  have hV'nu : ∀ z : ↥K₀', z ∈ V'.nonunits ↔ β z ∈ (W₀.comap (τ γ'').toAlgHom.toRingHom).nonunits :=
    mem_nonunits_iff_map_mem_nonunits β V' _ (fun _ => Iff.rfl)
  have hV'A : ∀ a : A, algebraMap A ↥K₀' a ∈ V' := by
    intro a
    rw [hV', hβalg, hτalg, ← hβalg, ← hVeq]
    exact hO₀'A a
  have hV'm : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K₀' a ∈ V'.nonunits := by
    intro a ha
    rw [hV'nu, mem_nonunits_iff_map_mem_nonunits (τ γ'').toAlgHom.toRingHom _ W₀ (fun _ => Iff.rfl), hβalg]
    show τ γ'' (algebraMap A ↥K a) ∈ W₀.nonunits
    rw [hτalg, ← hβalg, ← hVnu]
    exact hO₀'m a ha
  have hV'j : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j₀' P ∈ V' ∧ (Polynomial.aeval j₀' P)⁻¹ ∈ V' := by
    intro P hP
    obtain ⟨h1, h2⟩ := hO₀'j P hP
    refine ⟨?_, ?_⟩
    · rw [hV', hτP, ← hVeq]; exact h1
    · rw [hV', map_inv₀, map_inv₀, hτP, ← map_inv₀, ← hVeq]; exact h2
  have hne : O₀' ≠ V' := by
    intro heq
    apply hsep
    have hxg : x = β ⟨g, hK₀' ▸ hg⟩ := Subtype.ext (by rw [hβ]; exact hx)
    rw [hxg]
    show (⟨g, _⟩ : ↥K₀') ∈ V' ↔ β ⟨g, _⟩ ∈ W₀
    rw [← heq, hVeq]

  obtain ⟨-, ⟨𝔓, h𝔓p, h𝔓ht, h𝔓mem, h𝔓ϖ, -⟩, hd⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
      A L (↥K₀') j₀' htj₀' hFD₀' hsep₀' O₀' hO₀'A hO₀'m hO₀'j
  obtain ⟨-, ⟨𝔓', h𝔓'p, h𝔓'ht, h𝔓'mem, h𝔓'ϖ, -⟩, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
      A L (↥K₀') j₀' htj₀' hFD₀' hsep₀' V' hV'A hV'm hV'j
  haveI := h𝔓p
  haveI := h𝔓'p
  obtain ⟨b₀, hb₀V', hb₀O⟩ := hd V' hV'A hV'm hV'j hne
  have h𝔓ne : 𝔓 ≠ 𝔓' := by
    intro h
    exact hb₀O ((h𝔓mem b₀).mp (h ▸ (h𝔓'mem b₀).mpr hb₀V'))

  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal A := hϖ.symm ▸ Ideal.mem_span_singleton_self ϖ
  have hϖne : algebraMap A ↥(chartAlgFin A (↥K₀') j₀') ϖ ≠ 0 := by
    intro h0
    have : (algebraMap A ↥K₀' ϖ : ↥K₀') = 0 := by
      have := congrArg (fun w : ↥(chartAlgFin A (↥K₀') j₀') => (w : ↥K₀')) h0
      simpa using this
    rw [IsScalarTower.algebraMap_apply A L ↥K₀', map_eq_zero] at this
    have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
    exact hirr.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective A L)).mp this)
  have h𝔓min := mem_minimalPrimes_span_singleton_of_height_eq_one _ (mem_nonZeroDivisors_of_ne_zero hϖne)
    𝔓 (h𝔓ϖ ϖ hϖm) h𝔓ht
  have h𝔓'min := mem_minimalPrimes_span_singleton_of_height_eq_one _ (mem_nonZeroDivisors_of_ne_zero hϖne)
    𝔓' (h𝔓'ϖ ϖ hϖm) h𝔓'ht
  let y₀ : Ideal ↥(chartAlgFin A (↥K₀') j₀') := y.asIdeal.comap ι
  haveI hy₀ : y₀.IsPrime := Ideal.comap_isPrime ι y.asIdeal
  have h𝔓le : 𝔓 ≤ y₀ := fun b hb => by
    show ι b ∈ y.asIdeal
    apply hz₀
    rw [hιb, ← hVnu]
    exact (h𝔓mem b).mp hb
  have h𝔓'le : 𝔓' ≤ y₀ := fun b hb => by
    show ι b ∈ y.asIdeal
    apply hz₁''
    rw [hιb, ← hV'nu]
    exact (h𝔓'mem b).mp hb
  have hyϖ : algebraMap A ↥(chartAlgFin A (↥K₀') j₀') ϖ ∈ y₀ := h𝔓le (h𝔓ϖ ϖ hϖm)
  have hker : RingHom.ker (φ.comp ι) = y₀ := by rw [← RingHom.comap_ker, hφ]

  have hK₀'' : K₀' = laurentBaseChange L (qExpFunctionFieldC ℚ (Gamma0 (M' * q))) := by
    rw [Nat.mul_comm]; exact hK₀'
  have key := ModularCurve.FullLevel.map_jChartFin_mem_ssJSet_of_exists_two_minimalPrimes_span_le_chartAlgFin_laurentBaseChange_gamma0_mul
    q M' hqM' L K₀' hK₀'' A hAq j₀' hj₀' ϖ hϖ y₀ hyϖ ⟨𝔓, h𝔓min, 𝔓', h𝔓'min, h𝔓ne, h𝔓le, h𝔓'le⟩ Ω (φ.comp ι) hker
  refine ⟨ι (jChartFin A (↥K₀') j₀'), ?_, key⟩
  rw [hιb, hβ]
  rfl

end IGXBranch
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_map_jChartFin_mem_ssJSet_of_comap_gauss_ne_gauss_of_forall_mem_nonunits_xH.IGXR9Pres"

namespace IGX
p2m_open "ModularCurve~coeffMap_qExpand~coeffEmb_qExpand ModularCurve.FullLevel CongruenceSubgroup"

theorem coe_redQ_apply (q : ℕ) [Fact q.Prime] (δ : SL(2, ℤ)) (i j : Fin 2) :
    ((redQ q δ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) i j = ((δ i j : ℤ) : ZMod q) := by
  simp [redQ, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]

theorem redQ_smul_lineInfty_eq_iff (q : ℕ) [Fact q.Prime] (δ : SL(2, ℤ)) :
    redQ q δ • lineInfty q = lineInfty q ↔ ((δ 1 0 : ℤ) : ZMod q) = 0 := by
  have hsm : (redQ q δ) • (![1, 0] : Fin 2 → ZMod q) = ![((δ 0 0 : ℤ) : ZMod q), ((δ 1 0 : ℤ) : ZMod q)] := by
    show ((redQ q δ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) • (![1, 0] : Fin 2 → ZMod q) = _
    ext i
    rw [Matrix.smul_eq_mulVec]
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, coe_redQ_apply]
  rw [lineInfty, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  simp only [hsm]
  constructor
  · rintro ⟨a, ha⟩
    have := congr_fun ha 1
    simpa using this.symm
  · intro h
    have hdet : ((δ 0 0 : ℤ) : ZMod q) * ((δ 1 1 : ℤ) : ZMod q) = 1 := by
      have hd := Matrix.det_fin_two (δ : Matrix (Fin 2) (Fin 2) ℤ)
      rw [δ.prop] at hd
      have := congrArg (Int.cast : ℤ → ZMod q) hd
      push_cast at this
      rw [h, mul_zero, sub_zero] at this
      exact this.symm
    refine ⟨Units.mkOfMulEqOne _ _ hdet, ?_⟩
    ext i
    fin_cases i <;> simp [h, Units.smul_def]

theorem inv_apply_one_zero (δ : SL(2, ℤ)) :
    ((δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = -((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp

theorem inv_apply_zero_one (δ : SL(2, ℤ)) :
    ((δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = -((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1) := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp

end IGX
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_map_jChartFin_mem_ssJSet_of_comap_gauss_ne_gauss_of_forall_mem_nonunits_xH.IGXR9Pres"

p2m_open "ModularCurve~coeffMap_qExpand~coeffEmb_qExpand" in open  ModularCurve.FullLevel CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel in
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

    (τ : SL(2, ℤ) → (↥K ≃ₐ[L] ↥K))
    (hτ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') γ⁻¹ K (τ γ))

    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (hne : W₀.comap (τ γ).toAlgHom.toRingHom ≠ W₀)
    (hz₁ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), (b : ↥K) ∈ (W₀.comap (τ γ).toAlgHom.toRingHom).nonunits → b ∈ y.asIdeal)
    (hz₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y.asIdeal) :
    φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω := by
  classical
  by_contra hord

  haveI : NeZero (q * M') := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (NeZero.ne M')⟩
  set K₀ : IntermediateField L (LaurentSeries L) := laurentBaseChange L (qExpFunctionFieldC ℚ (Gamma0 M')) with hK₀
  set K₀' : IntermediateField L (LaurentSeries L) := laurentBaseChange L (qExpFunctionFieldC ℚ (Gamma0 (q * M'))) with hK₀'
  have hle₀K : K₀ ≤ K := by
    rw [hK₀, hK]
    exact ModularCurve.laurentBaseChange_qExpFunctionFieldC_gamma0_le_laurentBaseChange_xHFunctionField
      L M' (q ^ 2 * M') ⟨q ^ 2, by ring⟩ (levelH q M')
  have hle' : K₀' ≤ K := by
    rw [hK₀', hK]
    exact ModularCurve.laurentBaseChange_qExpFunctionFieldC_gamma0_le_laurentBaseChange_xHFunctionField
      L (q * M') (q ^ 2 * M') ⟨q, by ring⟩ (levelH q M')
  have hle₀ : K₀ ≤ K₀' := by
    rw [hK₀, hK₀']
    refine IntermediateField.adjoin.mono L _ _ (Set.image_mono ?_)
    refine qExpFunctionFieldC_mono ℚ (fun γ' hγ' => ?_)
    rw [Gamma0_mem] at hγ' ⊢
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ' ⊢
    exact dvd_trans ⟨q, by push_cast; ring⟩ hγ'
  let O₀ : ValuationSubring ↥K₀ := W₀.comap (IntermediateField.inclusion hle₀K).toRingHom
  have hO₀ : ∀ f : ↥K₀, f ∈ O₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) := fun f => (ValuationSubring.mem_comap).trans (hW₀ _)
  let O₀' : ValuationSubring ↥K₀' := W₀.comap (IntermediateField.inclusion hle').toRingHom
  have hO₀' : ∀ f : ↥K₀', f ∈ O₀' ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) := fun f => (ValuationSubring.mem_comap).trans (hW₀ _)
  letI algK₀ : Algebra ↥K₀ ↥K := (IntermediateField.inclusion hle₀K).toRingHom.toAlgebra
  letI algK₀' : Algebra ↥K₀' ↥K := (IntermediateField.inclusion hle').toRingHom.toAlgebra
  set B : ValuationSubring ↥K := W₀.comap (τ γ).toAlgHom.toRingHom with hBdef

  have hBO₀ : ∀ x : ↥K₀, algebraMap ↥K₀ ↥K x ∈ B ↔ x ∈ O₀ :=
    ModularCurve.FullLevel.algebraMap_mem_comap_gauss_iff_of_isLevelAutAt
      q hq M' hqM' L ζ hζ hι K hK K₀ hK₀ hle₀K A hAq hζA W₀ hW₀ O₀ hO₀ τ hτ γ hγ

  have hBO₀' : ∀ x : ↥K₀', algebraMap ↥K₀' ↥K x ∈ B ↔ x ∈ O₀' :=
    ModularCurve.FullLevel.forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_not_mem_ssJSet_xH_of_isAlgebraic
      q hq M' hqM' L ζ hζ hι K hK A hAq hζA j hj ϖ hϖ W₀ hW₀ z ϖz hϖz hz y hy hmax Ω φ hφ hord hz₀
      K₀ hK₀ K₀' hK₀' hle₀ hle' O₀ hO₀ O₀' hO₀' B hBO₀ hz₁

  obtain ⟨⟨σ, hσfix, hBσ⟩, -⟩ :=
    ModularCurve.FullLevel.exists_comap_eq_and_ramificationIdx_eq_one_and_isSeparable_of_over_gauss_gamma0_mul_xH
      q hq M' hqM' L ζ hζ hι K hK K₀ hK₀ hle₀K A hAq hζA W₀ hW₀ O₀ hO₀ K₀' hK₀' hle₀ hle' O₀' hO₀' B hBO₀'

  obtain ⟨Gfull, hGfin, hGmem⟩ :=
    ModularCurve.FullLevel.exists_subgroup_finite_mem_iff_exists_eq_of_isLevelAutAt q hq M' hqM' L ζ hζ hι K hK τ hτ
  haveI : Finite ↥Gfull := hGfin
  set SB : Set (↥K ≃ₐ[L] ↥K) := {σ' | ∃ γ' : SL(2, ℤ), γ' ∈ Gamma0 M' ∧
      (q : ℤ) ∣ (γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1 ∧ σ' = τ γ'} with hSBdef
  set GB : Subgroup (↥K ≃ₐ[L] ↥K) := Subgroup.closure SB with hGBdef
  have hGBle : GB ≤ Gfull := by
    rw [hGBdef, Subgroup.closure_le]
    rintro σ' ⟨γ', hγ', -, rfl⟩
    exact (hGmem _).mpr ⟨γ', hγ', rfl⟩
  haveI : Finite ↥GB := Finite.of_injective (fun g : ↥GB => (⟨g.1, hGBle g.2⟩ : ↥Gfull))
    (fun a b h => Subtype.ext (by simpa using congrArg (fun x : ↥Gfull => (x : ↥K ≃ₐ[L] ↥K)) h))
  haveI : FaithfulSMul ↥GB ↥K := ⟨fun {g h} hgh => by
    apply Subtype.ext; apply AlgEquiv.ext; intro x; exact hgh x⟩
  have hFFB := ModularCurve.FullLevel.forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul
    q hq M' hqM' L ζ hζ hι K hK τ hτ
  have hfixGB : ∀ w : ↥K, (∀ g : ↥GB, g • w = w) → ((w : ↥K) : LaurentSeries L) ∈ K₀' := by
    intro w hw
    rw [hK₀']
    apply (hFFB w).mp
    intro γ' hγ' hdvd
    exact hw ⟨τ γ', Subgroup.subset_closure ⟨γ', hγ', hdvd, rfl⟩⟩
  have hσE : ∀ w : ↥(FixedPoints.subfield ↥GB ↥K), σ (w : ↥K) = w := by
    intro w
    have hw : ((w : ↥K) : LaurentSeries L) ∈ K₀' := hfixGB w (fun g => w.2 g)
    have : (w : ↥K) = algebraMap ↥K₀' ↥K ⟨_, hw⟩ := Subtype.ext rfl
    rw [this]; exact hσfix _
  let σE : ↥K ≃ₐ[↥(FixedPoints.subfield ↥GB ↥K)] ↥K :=
    { σ.toRingEquiv with commutes' := fun w => hσE w }
  obtain ⟨g, hg⟩ := (FixedPoints.toAlgAut_surjective ↥GB ↥K) σE
  have hσg : ∀ x : ↥K, σ x = (g.1 : ↥K ≃ₐ[L] ↥K) x := by
    intro x
    show σE x = _
    rw [← hg]; rfl

  obtain ⟨e, A', hA', ζ', ιK, O, hζ', hιK, hO, hOW⟩ :=
    ModularCurve.FullLevel.exists_ringHom_fieldBar_comap_gauss_iff_of_isAlgebraic
      q hq M' hqM' L ζ hζ hι K hK A hAq hζA W₀ hW₀
  have hιKinj : Function.Injective ιK := ιK.injective
  have hτbar : ∀ γ' : SL(2, ℤ), γ' ∈ Gamma0 M' → ∀ x : ↥K,
      ιK (τ γ' x) = levelAutBar q M' ζ' γ'⁻¹ (ιK x) :=
    fun γ' hγ' x =>
      ModularCurve.FullLevel.levelAutBar_apply_eq_of_isLevelAutAt_of_coe_eq_coeffMap
        q hq M' hqM' L ζ hζ hι K hK e ζ' hζ' ιK hιK γ'⁻¹ (inv_mem hγ') (τ γ') (hτ γ' hγ') x
  have hmul := fun (α β : SL(2, ℤ)) (hα : α ∈ Gamma0 M') (hβ : β ∈ Gamma0 M') =>
    ModularCurve.FullLevel.levelAutBar_mul q M' hqM' ζ' α β hα hβ
  have hτmul : ∀ γ' δ : SL(2, ℤ), γ' ∈ Gamma0 M' → δ ∈ Gamma0 M' → τ (γ' * δ) = τ γ' * τ δ := by
    intro γ' δ hγ' hδ
    apply AlgEquiv.ext; intro x; apply hιKinj
    rw [AlgEquiv.mul_apply, hτbar _ (mul_mem hγ' hδ), hτbar γ' hγ', hτbar δ hδ, mul_inv_rev,
      hmul δ⁻¹ γ'⁻¹ (inv_mem hδ) (inv_mem hγ'), AlgEquiv.trans_apply]
  have hτone : τ 1 = 1 := by
    have h := hτmul 1 1 (one_mem _) (one_mem _)
    rw [mul_one] at h
    exact left_eq_mul.mp h
  have hτinv : ∀ γ' : SL(2, ℤ), γ' ∈ Gamma0 M' → τ γ'⁻¹ = (τ γ')⁻¹ := by
    intro γ' hγ'
    apply eq_inv_of_mul_eq_one_left
    rw [← hτmul _ _ (inv_mem hγ') hγ', inv_mul_cancel, hτone]

  have hGBword : ∀ σ' : ↥K ≃ₐ[L] ↥K, σ' ∈ GB → ∃ β : SL(2, ℤ), β ∈ Gamma0 M' ∧
      (q : ℤ) ∣ (β : Matrix (Fin 2) (Fin 2) ℤ) 0 1 ∧ σ' = τ β := by
    intro σ' hσ'
    refine Subgroup.closure_induction (p := fun σ' _ => ∃ β : SL(2, ℤ), β ∈ Gamma0 M' ∧
      (q : ℤ) ∣ (β : Matrix (Fin 2) (Fin 2) ℤ) 0 1 ∧ σ' = τ β) ?_ ?_ ?_ ?_ hσ'
    · rintro σ' ⟨β, hβ, hdvd, rfl⟩; exact ⟨β, hβ, hdvd, rfl⟩
    · exact ⟨1, one_mem _, by simp, hτone.symm⟩
    · rintro σ₁ σ₂ _ _ ⟨β₁, hβ₁, hd₁, rfl⟩ ⟨β₂, hβ₂, hd₂, rfl⟩
      refine ⟨β₁ * β₂, mul_mem hβ₁ hβ₂, ?_, (hτmul β₁ β₂ hβ₁ hβ₂).symm⟩
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      exact dvd_add (dvd_mul_of_dvd_right hd₂ _) (dvd_mul_of_dvd_left hd₁ _)
    · rintro σ₁ _ ⟨β₁, hβ₁, hd₁, rfl⟩
      refine ⟨β₁⁻¹, inv_mem hβ₁, ?_, (hτinv β₁ hβ₁).symm⟩
      rw [IGX.inv_apply_zero_one]; exact (dvd_neg).mpr hd₁
  obtain ⟨γ'', hγ'', hb'', hgγ''⟩ := hGBword g.1 g.2
  have hBγ'' : B = W₀.comap (τ γ'').toAlgHom.toRingHom := by
    rw [hBσ]; ext x
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap]
    show σ x ∈ W₀ ↔ τ γ'' x ∈ W₀
    rw [hσg, hgγ'']

  have hSL := ModularCurve.FullLevel.comap_gauss_eq_comap_gauss_iff_redQ_inv_smul_lineInfty_eq_of_isLevelAutAt_of_isAlgebraic
      q hq M' hqM' L ζ hζ hι K hK K₀ hK₀ hle₀K A hAq hζA W₀ hW₀ O₀ hO₀ τ hτ
  have hc'' : ¬ (q : ℤ) ∣ ((γ'' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    intro hdvd
    apply hne
    rw [hBγ'']
    apply ((hSL γ'' γ'' hγ'' hγ'').2).mpr
    show redQ q γ''⁻¹ • lineInfty q = lineInfty q
    rw [IGX.redQ_smul_lineInfty_eq_iff, IGX.inv_apply_one_zero, Int.cast_neg, neg_eq_zero]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd

  obtain ⟨g, x, hg, hx, hsep⟩ :=
    ModularCurve.FullLevel.exists_qExpand_mem_gauss_xor_mem_comap_gauss_of_dvd_of_not_dvd_of_isLevelAutAt
      q hq M' hqM' L ζ hζ hι K hK A hAq hζA W₀ hW₀ τ hτ γ'' hγ'' hb'' hc''

  have hj'' : ∃ xj : ↥(chartAlgFin A (↥K) j), ((xj : ↥K) : LaurentSeries L) = qExpand L q (coeffEmb L jq) ∧
      φ xj ∈ ssJSet q Ω := by
    exact IGXBranch.exists_jChart_qExpand_mem_ssJSet q hq M' hqM' L ζ hζ hι K hK A hAq j hj ϖ hϖ W₀ hW₀ y Ω φ hφ τ hτ hz₀
      γ'' hγ'' (fun b hb => hz₁ b (by rw [hBγ'']; exact hb)) g x hg hx hsep

  obtain ⟨xj, hxj, hss⟩ := hj''
  have hfrob : φ xj = φ (jChartFin A (↥K) j) ^ q := by
    have hw : ((xj - jChartFin A (↥K) j ^ q : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ W₀.nonunits := by
      push_cast
      exact IGXR9.qExpand_j_sub_pow_mem_nonunits_gauss q L K A hAq (jChartFin A (↥K) j : ↥K) (xj : ↥K) hj hxj W₀ hW₀
    have hmem : xj - jChartFin A (↥K) j ^ q ∈ y.asIdeal := hz₀ _ hw
    rw [← hφ, RingHom.mem_ker, map_sub, map_pow, sub_eq_zero] at hmem
    exact hmem
  rw [hfrob] at hss
  exact hord (ModularCurve.mem_ssJSet_of_pow_mem_ssJSet q Ω 1 _ (by rw [pow_one]; exact hss))

end S_ModularCurve_FullLevel_map_jChartFin_mem_ssJSet_of_comap_gauss_ne_gauss_of_forall_mem_nonunits_xH
end P2MW
export P2MW.S_ModularCurve_FullLevel_map_jChartFin_mem_ssJSet_of_comap_gauss_ne_gauss_of_forall_mem_nonunits_xH (solution)
