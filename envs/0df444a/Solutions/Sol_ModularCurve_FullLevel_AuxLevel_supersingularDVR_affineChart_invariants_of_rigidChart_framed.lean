-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.supersingularDVR_affineChart_invariants_of_rigidChart_framed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/1432961d-6a5b-583d-aaad-3b916ad45a80

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
import Definitions.Def_ModularCurve_RigidDescentHyps
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_finite_subgroup_forall_mem_iff_exists_isLevelAutAt_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_mul_mul_inv_mem_and_map_fixedField_of_isLevelAutAt_gamma0
import Theorems.Thm_ModularCurve_FullLevel_qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_exists_ringHom
import Theorems.Thm_ModularCurve_qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_FullLevel_qExpand_coeffEmb_jq_mem_and_mem_chartAlgFin_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_FullLevel_qExpand_coeffEmb_mem_chartAlgFin_of_mem_integers_of_cuspRegular_of_not_dvd
import Theorems.Thm_IsGaloisGroup_finitePresentation_and_smooth_invariants_typeZero_of_isUnit_natCard_of_smooth_fibers
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_finite_and_natCard_dvd_of_eq_closure_isLevelAutAt_gamma
import Theorems.Thm_ValuationSubring_maximalIdeal_comap_fixedPoints_eq_span_and_mem_iff_exists_invariant_of_isLocalization
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_quotField_ringHom_invariants_of_rigidChart_framed
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_formallySmooth_invariants_of_rigidChart_framed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_framed
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex AlgebraicCurve.CurveModel.isProper"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe"
p2m_attr_erase "simp" "ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong"
p2m_attr_erase "simp" "NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 51200000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace S3GlueKit

open IsLocalRing

variable {K L : Type*} [Field K] [Field L]

def comapEquiv (e : K ≃+* L) (V : ValuationSubring L) : (V.comap (e : K →+* L)) ≃+* V where
  toFun x := ⟨e x, x.2⟩
  invFun y := ⟨e.symm y, by show e (e.symm y) ∈ V; rw [e.apply_symm_apply]; exact y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

@[scoped simp] theorem coe_comapEquiv (e : K ≃+* L) (V : ValuationSubring L) (x : V.comap (e : K →+* L)) :
    ((comapEquiv e V x : V) : L) = e x := rfl

theorem isDiscreteValuationRing_comap (e : K ≃+* L) (V : ValuationSubring L) [IsDiscreteValuationRing V] :
    IsDiscreteValuationRing (V.comap (e : K →+* L)) :=
  let f := (comapEquiv e V).symm
  { toIsPrincipalIdealRing := IsPrincipalIdealRing.of_surjective f.toRingHom f.surjective
    toIsLocalRing := inferInstance
    not_a_field' := by
      intro h
      apply IsDiscreteValuationRing.not_a_field (R := V)
      rw [eq_bot_iff] at h ⊢
      intro y hy
      have : f y ∈ maximalIdeal _ := by
        rw [mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
        exact fun hu => hy (by simpa using hu.map f.symm.toRingHom)
      have := h this
      rw [Ideal.mem_bot] at this ⊢
      simpa using congrArg f.symm this }

theorem mem_maximalIdeal_comap_iff (e : K ≃+* L) (V : ValuationSubring L) (x : V.comap (e : K →+* L)) :
    x ∈ maximalIdeal (V.comap (e : K →+* L)) ↔ (comapEquiv e V x) ∈ maximalIdeal V := by
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
  exact ⟨fun h => by simpa using h.map (comapEquiv e V).toRingHom,
    fun h => by simpa using h.map (comapEquiv e V).symm.toRingHom⟩

theorem maximalIdeal_comap_eq_span (e : K ≃+* L) (V : ValuationSubring L) (π : V)
    (h : maximalIdeal V = Ideal.span {π}) :
    maximalIdeal (V.comap (e : K →+* L)) = Ideal.span {(comapEquiv e V).symm π} := by
  apply le_antisymm
  · intro x hx
    rw [mem_maximalIdeal_comap_iff, h, Ideal.mem_span_singleton] at hx
    obtain ⟨c, hc⟩ := hx
    rw [Ideal.mem_span_singleton]
    refine ⟨(comapEquiv e V).symm c, ?_⟩
    apply (comapEquiv e V).injective
    rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    exact hc
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_maximalIdeal_comap_iff,
      RingEquiv.apply_symm_apply, h]
    exact Ideal.mem_span_singleton_self π

theorem exists_subring_image {R S : Type*} [Ring R] [Ring S] (s : Subring R) (f : R →+* S) :
    ∃ B : Subring S, ∀ y : S, y ∈ B ↔ ∃ x : R, x ∈ s ∧ y = f x :=
  ⟨s.map f, fun y => by
    rw [Subring.mem_map]
    exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩, fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩⟩⟩

theorem exists_namingBlock {k E : Type*} [Field k] [Field E] [Algebra k E]
    (O : Type*) [CommRing O] [Algebra O E] [Algebra O k] [IsScalarTower O k E]
    (S : Set (E ≃ₐ[k] E)) (Bt : Subalgebra O E) (Wt : ValuationSubring E) :
    ∃ (G : Subgroup (E ≃ₐ[k] E)) (K₀ : IntermediateField k E) (B₀ : Subalgebra O E) (W₀' : ValuationSubring K₀),
      G = Subgroup.closure S ∧ K₀ = IntermediateField.fixedField G ∧
      (∀ f : E, f ∈ B₀ ↔ f ∈ Bt ∧ ∀ τ : E ≃ₐ[k] E, τ ∈ G → τ f = f) ∧
      (∀ f : K₀, f ∈ W₀' ↔ ((f : E)) ∈ Wt) := by
  refine ⟨Subgroup.closure S, IntermediateField.fixedField (Subgroup.closure S),
    { carrier := {f : E | f ∈ Bt ∧ ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.closure S → τ f = f}
      mul_mem' := ?_, one_mem' := ?_, add_mem' := ?_, zero_mem' := ?_, algebraMap_mem' := ?_ },
    Wt.comap (algebraMap _ E), rfl, rfl, fun f => Iff.rfl, fun f => Iff.rfl⟩
  · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨Bt.mul_mem ha hb, fun τ hτ => by rw [map_mul, ha' τ hτ, hb' τ hτ]⟩
  · exact ⟨Bt.one_mem, fun τ _ => map_one τ⟩
  · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨Bt.add_mem ha hb, fun τ hτ => by rw [map_add, ha' τ hτ, hb' τ hτ]⟩
  · exact ⟨Bt.zero_mem, fun τ _ => map_zero τ⟩
  · intro a
    exact ⟨Bt.algebraMap_mem a, fun τ _ => by rw [IsScalarTower.algebraMap_apply O k E]; exact τ.commutes _⟩

theorem exists_comap_valuationSubring {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (V : ValuationSubring L) :
    ∃ W : ValuationSubring K, W = V.comap (e : K →+* L) ∧ ∀ f : K, f ∈ W ↔ e f ∈ V :=
  ⟨_, rfl, fun f => Iff.rfl⟩

theorem exists_algebra_of_ringHom {R S : Type*} [CommRing R] [CommRing S] (ψ : R →+* S) :
    ∃ alg : Algebra R S, ∀ a : R, @algebraMap R S _ _ alg a = ψ a :=
  ⟨ψ.toAlgebra, fun a => rfl⟩

theorem coe_comapEquiv_symm {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (V : ValuationSubring L) (y : V) :
    (((comapEquiv e V).symm y : V.comap (e : K →+* L)) : K) = e.symm y := rfl

section algEquiv
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem algEquiv_symm_toRingEquiv_algebraMap (φ : A ≃ₐ[R] B) (x : R) :
    φ.symm.toRingEquiv (algebraMap R B x) = algebraMap R A x := φ.symm.commutes x

theorem algEquiv_symm_toRingEquiv_symm_algebraMap (φ : A ≃ₐ[R] B) (x : R) :
    φ.symm.toRingEquiv.symm (algebraMap R A x) = algebraMap R B x := φ.commutes x

theorem algEquiv_symm_toRingEquiv_apply_apply (φ : A ≃ₐ[R] B) (x : A) :
    φ.symm.toRingEquiv (φ x) = x := φ.symm_apply_apply x

theorem algEquiv_symm_toRingEquiv_symm_apply (φ : A ≃ₐ[R] B) (x : A) :
    φ.symm.toRingEquiv.symm x = φ x := rfl

end algEquiv

theorem exists_mem_and_maximalIdeal_eq_span {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    (V : ValuationSubring L) (W : ValuationSubring K) (hW : W = V.comap (e : K →+* L))
    (π : L) (hπV : π ∈ V) (hmax : IsLocalRing.maximalIdeal V = Ideal.span {(⟨π, hπV⟩ : V)})
    (π' : K) (hπ' : e π' = π) :
    ∃ h : π' ∈ W, IsLocalRing.maximalIdeal W = Ideal.span {(⟨π', h⟩ : W)} := by
  subst hW
  have h : π' ∈ V.comap (e : K →+* L) := by show e π' ∈ V; rw [hπ']; exact hπV
  refine ⟨h, ?_⟩
  rw [maximalIdeal_comap_eq_span e V ⟨π, hπV⟩ hmax]
  congr 2
  apply Subtype.ext
  show e.symm π = π'
  rw [← hπ', e.symm_apply_apply]

end S3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_framed.S3GlueKit"

namespace C3Kit2

open IsLocalRing

variable {k E : Type*} [Field k] [Field E] [Algebra k E]

theorem mem_fixedSubfield_of_mem (G : Subgroup (E ≃ₐ[k] E)) (K₀ : IntermediateField k E)
    (hK₀ : K₀ = IntermediateField.fixedField G) (x : E) (hx : x ∈ K₀) : x ∈ FixedPoints.subfield ↥G E := by
  rw [hK₀, IntermediateField.mem_fixedField_iff] at hx
  show x ∈ MulAction.fixedPoints ↥G E
  rw [MulAction.mem_fixedPoints]
  intro g
  exact hx g g.2

theorem mem_of_mem_fixedSubfield (G : Subgroup (E ≃ₐ[k] E)) (K₀ : IntermediateField k E)
    (hK₀ : K₀ = IntermediateField.fixedField G) (x : E) (hx : x ∈ FixedPoints.subfield ↥G E) : x ∈ K₀ := by
  rw [hK₀, IntermediateField.mem_fixedField_iff]
  change x ∈ MulAction.fixedPoints ↥G E at hx
  rw [MulAction.mem_fixedPoints] at hx
  intro g hg
  exact hx ⟨g, hg⟩

def fixedEquiv (G : Subgroup (E ≃ₐ[k] E)) (K₀ : IntermediateField k E) (hK₀ : K₀ = IntermediateField.fixedField G) :
    ↥K₀ ≃+* ↥(FixedPoints.subfield ↥G E) where
  toFun x := ⟨(x : E), mem_fixedSubfield_of_mem G K₀ hK₀ x x.2⟩
  invFun y := ⟨(y : E), mem_of_mem_fixedSubfield G K₀ hK₀ y y.2⟩
  left_inv x := Subtype.ext rfl
  right_inv y := Subtype.ext rfl
  map_mul' x y := Subtype.ext rfl
  map_add' x y := Subtype.ext rfl

@[scoped simp] theorem coe_fixedEquiv (G : Subgroup (E ≃ₐ[k] E)) (K₀ : IntermediateField k E)
    (hK₀ : K₀ = IntermediateField.fixedField G) (x : ↥K₀) : ((fixedEquiv G K₀ hK₀ x : ↥(FixedPoints.subfield ↥G E)) : E) = (x : E) := rfl

theorem descDVR {K : Type} [Field K] {k : Type} [Field k] [Algebra k K]
    (G : Subgroup (K ≃ₐ[k] K)) [Finite ↥G]
    (W : ValuationSubring K) [IsDiscreteValuationRing ↥W]
    (π : K) (hπG : ∀ g : ↥G, g • π = π) (hπW : π ∈ W)
    (hπ : maximalIdeal ↥W = Ideal.span {(⟨π, hπW⟩ : ↥W)})
    (hfaith : ∀ (g : ↥G) (hg : ∀ x : K, g • x ∈ W ↔ x ∈ W), g ≠ 1 → ∃ x : ↥W,
      (⟨g • (x : K), (hg x).mpr x.2⟩ - x : ↥W) ∉ maximalIdeal ↥W)
    (B : Subring K) (hBG : ∀ (g : ↥G) (b : K), b ∈ B → g • b ∈ B) (hBW : ∀ f : K, f ∈ B → f ∈ W)
    (hloc : ∀ f : K, f ∈ W ↔ ∃ g h : K, g ∈ B ∧ h ∈ B ∧
      (∀ hh : h ∈ W, (⟨h, hh⟩ : ↥W) ∉ maximalIdeal ↥W) ∧ f * h = g)
    (K₀ : IntermediateField k K) (hK₀ : K₀ = IntermediateField.fixedField G)
    (W₀ : ValuationSubring ↥K₀) (hW₀ : ∀ f : ↥K₀, f ∈ W₀ ↔ ((f : K)) ∈ W)
    (hπK₀ : π ∈ K₀) :
    IsDiscreteValuationRing ↥W₀ ∧
    (∃ hπ0 : (⟨π, hπK₀⟩ : ↥K₀) ∈ W₀, maximalIdeal ↥W₀ = Ideal.span {(⟨_, hπ0⟩ : ↥W₀)}) ∧
    (∀ f : K, (∀ g : ↥G, g • f = f) →
      (f ∈ W ↔ ∃ g h : K, g ∈ B ∧ h ∈ B ∧ (∀ σ : ↥G, σ • g = g) ∧ (∀ σ : ↥G, σ • h = h) ∧
        (∀ hh : h ∈ W, (⟨h, hh⟩ : ↥W) ∉ maximalIdeal ↥W) ∧ f * h = g)) := by
  obtain ⟨h1, ⟨hπ0, h2⟩, h3⟩ :=
    ValuationSubring.maximalIdeal_comap_fixedPoints_eq_span_and_mem_iff_exists_invariant_of_isLocalization
      K (↥G) W π hπG hπW hπ hfaith B hBG hBW hloc
  haveI := h1
  let e := fixedEquiv G K₀ hK₀
  have hWeq : W₀ = (W.comap (FixedPoints.subfield ↥G K).subtype).comap (e : ↥K₀ →+* ↥(FixedPoints.subfield ↥G K)) := by
    ext f; rw [hW₀]; rfl
  refine ⟨?_, ?_, h3⟩
  · rw [hWeq]; exact S3GlueKit.isDiscreteValuationRing_comap e _
  · have hmem : (⟨π, hπK₀⟩ : ↥K₀) ∈ W₀ := (hW₀ _).mpr hπW
    refine ⟨hmem, ?_⟩

    have key := S3GlueKit.maximalIdeal_comap_eq_span e (W.comap (FixedPoints.subfield ↥G K).subtype) ⟨_, hπ0⟩ h2
    have hgen : ((S3GlueKit.comapEquiv e (W.comap (FixedPoints.subfield ↥G K).subtype)).symm ⟨_, hπ0⟩ :
        ↥((W.comap (FixedPoints.subfield ↥G K).subtype).comap (e : ↥K₀ →+* ↥(FixedPoints.subfield ↥G K)))) =
        ⟨⟨π, hπK₀⟩, by rw [← hWeq]; exact hmem⟩ := by
      apply Subtype.ext; apply Subtype.ext; rfl
    rw [hgen] at key
    subst hWeq
    exact key

theorem hloc_reshape {K : Type*} [Field K] {R : Type*} [CommRing R] [Algebra R K]
    (Bt : Subalgebra R K) (W : ValuationSubring K) (hBW : ∀ f : K, f ∈ Bt → f ∈ W)
    (hR3e : ∀ f : K, f ∈ W ↔ ∃ g h : ↥Bt, (⟨(h : K), hBW _ h.2⟩ : ↥W) ∉ maximalIdeal ↥W ∧ f * (h : K) = (g : K)) :
    ∀ f : K, f ∈ W ↔ ∃ g h : K, g ∈ Bt.toSubring ∧ h ∈ Bt.toSubring ∧
      (∀ hh : h ∈ W, (⟨h, hh⟩ : ↥W) ∉ maximalIdeal ↥W) ∧ f * h = g := by
  intro f
  rw [hR3e]
  constructor
  · rintro ⟨g, h, hh, hf⟩
    exact ⟨g, h, g.2, h.2, fun _ => hh, hf⟩
  · rintro ⟨g, h, hg, hh, hu, hf⟩
    exact ⟨⟨g, hg⟩, ⟨h, hh⟩, hu _, hf⟩

end C3Kit2
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_framed.S3GlueKit P2MW.S_ModularCurve_FullLevel_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_framed.C3Kit2"

namespace C3Kit3

open MvPolynomial DrinfeldCurve

theorem x_ne_zero (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [IsAlgClosed k] : DrinfeldCurve.x q k ≠ 0 := by
  classical
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hP1 : (Polynomial.X ^ q - Polynomial.X : Polynomial k).natDegree = q := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
      simp only [Polynomial.natDegree_X_pow, Polynomial.natDegree_X] ; omega
  have hP : (Polynomial.X ^ q - Polynomial.X + 1 : Polynomial k).natDegree = q := by
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;> rw [hP1]
    rw [Polynomial.natDegree_one]; omega
  have hP0 : (Polynomial.X ^ q - Polynomial.X + 1 : Polynomial k) ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hP; omega
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root (Polynomial.X ^ q - Polynomial.X + 1 : Polynomial k)
    (by rw [Polynomial.degree_eq_natDegree hP0, hP]; exact_mod_cast (show q ≠ 0 by omega))
  have ha' : a ^ q - a + 1 = 0 := by
    have := ha.eq_zero
    simpa [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] using this
  have ha0 : a ≠ 0 := by rintro rfl; simp [zero_pow (show q ≠ 0 by omega)] at ha'

  let φ : MvPolynomial (Fin 2) k →ₐ[k] k := MvPolynomial.aeval ![a, 1]
  have hφ : ∀ f ∈ drinfeldIdeal q k, φ f = 0 := by
    intro f hf
    rw [drinfeldIdeal, Ideal.mem_span_singleton] at hf
    obtain ⟨g, rfl⟩ := hf
    rw [map_mul]
    have : φ (drinfeldPoly q k - 1) = 0 := by
      simp only [drinfeldPoly, φ, map_sub, map_mul, map_pow, map_one, MvPolynomial.aeval_X,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_pow, mul_one]
      linear_combination (-1 : k) * ha'
    rw [this, zero_mul]
  let ψ : CoordRing q k →ₐ[k] k := Ideal.Quotient.liftₐ (drinfeldIdeal q k) φ hφ
  have hψx : ψ (DrinfeldCurve.x q k) = a := by
    show Ideal.Quotient.liftₐ (drinfeldIdeal q k) φ hφ (Ideal.Quotient.mkₐ k (drinfeldIdeal q k) (X 0)) = a
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    simp [φ]
  intro hx
  apply ha0
  rw [← hψx, hx, map_zero]

theorem hAction_x_ne (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [IsAlgClosed k] [Algebra (GaloisField q 2) k]
    (p : ↥(hSubgroup q))
    (hp1 : (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1 = 1)
    (hp2 : scalarOf q k (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2 ≠ 1) :
    hAction q k p (DrinfeldCurve.x q k) ≠ DrinfeldCurve.x q k := by
  set s := scalarOf q k (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2 with hs
  have hact : hAction q k p (DrinfeldCurve.x q k) = s • DrinfeldCurve.x q k := by
    show hAction q k p (mk q k (X 0)) = s • mk q k (X 0)
    rw [hAction_mk, hp1]
    have : ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) = 1 := rfl
    rw [this, substPoly_one, AlgHom.id_apply, scalePoly_X, map_mul, ← hs]
    rw [show mk q k (C s) = algebraMap k (CoordRing q k) s from (mk q k).commutes s, Algebra.smul_def]
  intro h
  rw [hact] at h
  have h2 : (s - 1) • DrinfeldCurve.x q k = 0 := by rw [sub_smul, one_smul, h, sub_self]
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hp2
  exact x_ne_zero q k ((inv_smul_smul₀ hs1 (DrinfeldCurve.x q k)).symm.trans (by rw [h2, smul_zero]))

end C3Kit3
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_framed.S3GlueKit P2MW.S_ModularCurve_FullLevel_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_framed.C3Kit2"

namespace C3Kit

section Action

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable {R : Type*} [CommRing R] [Algebra R K]

def subalgAction (G : Subgroup (K ≃ₐ[k] K)) (B : Subalgebra R K)
    (h : ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∀ f : K, f ∈ B → τ f ∈ B) : MulSemiringAction ↥G ↥B where
  smul τ b := ⟨(τ : K ≃ₐ[k] K) (b : K), h τ τ.2 b b.2⟩
  one_smul b := Subtype.ext rfl
  mul_smul σ τ b := Subtype.ext rfl
  smul_zero τ := Subtype.ext (map_zero _)
  smul_add τ a b := Subtype.ext (map_add _ _ _)
  smul_one τ := Subtype.ext (map_one _)
  smul_mul τ a b := Subtype.ext (map_mul _ _ _)

theorem subalgAction_smul_coe (G : Subgroup (K ≃ₐ[k] K)) (B : Subalgebra R K)
    (h : ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∀ f : K, f ∈ B → τ f ∈ B) (τ : ↥G) (b : ↥B) :
    letI := subalgAction G B h
    (((τ • b) : ↥B) : K) = (τ : K ≃ₐ[k] K) (b : K) := rfl

def inclAlgebra (B₀ B : Subalgebra R K) (hle : B₀ ≤ B) : Algebra ↥B₀ ↥B :=
  (Subalgebra.inclusion hle).toRingHom.toAlgebra

theorem inclAlgebra_algebraMap_coe (B₀ B : Subalgebra R K) (hle : B₀ ≤ B) (x : ↥B₀) :
    letI := inclAlgebra B₀ B hle
    ((algebraMap ↥B₀ ↥B x : ↥B) : K) = (x : K) := rfl

theorem inclAlgebra_isScalarTower (B₀ B : Subalgebra R K) (hle : B₀ ≤ B) :
    letI := inclAlgebra B₀ B hle
    IsScalarTower R ↥B₀ ↥B :=
  letI := inclAlgebra B₀ B hle
  IsScalarTower.of_algebraMap_eq (fun r => Subtype.ext rfl)

theorem inclAlgebra_faithfulSMul (B₀ B : Subalgebra R K) (hle : B₀ ≤ B) :
    letI := inclAlgebra B₀ B hle
    FaithfulSMul ↥B₀ ↥B :=
  letI := inclAlgebra B₀ B hle
  (faithfulSMul_iff_algebraMap_injective ↥B₀ ↥B).mpr (Subalgebra.inclusion_injective hle)

theorem isGaloisGroup (G : Subgroup (K ≃ₐ[k] K)) (B B₀ : Subalgebra R K)
    (h : ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∀ f : K, f ∈ B → τ f ∈ B)
    (hB₀ : ∀ f : K, f ∈ B₀ ↔ f ∈ B ∧ ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ f = f)
    (hfrac : ∀ f : K, ∃ g h' : ↥B, (h' : K) ≠ 0 ∧ f * (h' : K) = (g : K)) :
    letI := subalgAction G B h
    letI := inclAlgebra B₀ B (fun f hf => ((hB₀ f).mp hf).1)
    IsGaloisGroup ↥G ↥B₀ ↥B := by
  letI := subalgAction G B h
  letI := inclAlgebra B₀ B (fun f hf => ((hB₀ f).mp hf).1)
  refine ⟨⟨fun {σ τ} hστ => ?_⟩, ⟨fun τ b₀ b => ?_⟩, ⟨fun b hb => ?_⟩⟩
  ·
    apply Subtype.ext
    apply AlgEquiv.ext
    intro f
    obtain ⟨g, h', hh0, hfg⟩ := hfrac f
    have eg : (σ : K ≃ₐ[k] K) (g : K) = (τ : K ≃ₐ[k] K) (g : K) := congrArg Subtype.val (hστ g)
    have eh : (σ : K ≃ₐ[k] K) (h' : K) = (τ : K ≃ₐ[k] K) (h' : K) := congrArg Subtype.val (hστ h')
    have hσh : (σ : K ≃ₐ[k] K) (h' : K) ≠ 0 := (map_ne_zero_iff _ (σ : K ≃ₐ[k] K).injective).mpr hh0
    have e1 : (σ : K ≃ₐ[k] K) f * (σ : K ≃ₐ[k] K) (h' : K) = (σ : K ≃ₐ[k] K) (g : K) := by rw [← map_mul, hfg]
    have e2 : (τ : K ≃ₐ[k] K) f * (τ : K ≃ₐ[k] K) (h' : K) = (τ : K ≃ₐ[k] K) (g : K) := by rw [← map_mul, hfg]
    rw [← mul_left_inj' hσh, e1, eg, eh, ← e2]
  ·
    apply Subtype.ext
    change (τ : K ≃ₐ[k] K) ((b₀ : K) * (b : K)) = (b₀ : K) * (τ : K ≃ₐ[k] K) (b : K)
    rw [map_mul, ((hB₀ b₀).mp b₀.2).2 τ τ.2]
  ·
    refine ⟨⟨(b : K), (hB₀ b).mpr ⟨b.2, fun τ hτ => ?_⟩⟩, Subtype.ext rfl⟩
    exact congrArg Subtype.val (hb ⟨τ, hτ⟩)

theorem smulCommClass (G : Subgroup (K ≃ₐ[k] K)) (B : Subalgebra R K)
    (h : ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∀ f : K, f ∈ B → τ f ∈ B)
    [Algebra R k] [IsScalarTower R k K] :
    letI := subalgAction G B h
    SMulCommClass ↥G R ↥B := by
  letI := subalgAction G B h
  refine ⟨fun τ r b => Subtype.ext ?_⟩
  change (τ : K ≃ₐ[k] K) ((r • b : ↥B) : K) = ((r • (τ • b) : ↥B) : K)
  rw [Subalgebra.coe_smul, Subalgebra.coe_smul, Algebra.smul_def, Algebra.smul_def, map_mul,
    IsScalarTower.algebraMap_apply R k K, AlgEquiv.commutes]
  rfl

end Action
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_framed.S3GlueKit P2MW.S_ModularCurve_FullLevel_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_framed.C3Kit2"

end C3Kit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_framed.S3GlueKit P2MW.S_ModularCurve_FullLevel_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_framed.C3Kit2"

theorem C3aux_exists_emb (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (m : ℕ) [NeZero m]
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ m) :
    ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / m) := by
  haveI hQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h := AlgebraicClosure.isAlgebraic ℚ
    convert h <;> first | exact Subsingleton.elim _ _ | with_reducible_and_instances rfl | rfl
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

namespace C3Kit4

theorem exists_invariant_fraction {k K : Type*} [Field k] [Field K] [Algebra k K] {R : Type*} [CommRing R] [Algebra R K]
    (G : Subgroup (K ≃ₐ[k] K)) [Finite ↥G] (B B₀ : Subalgebra R K)
    (h : ∀ τ : K ≃ₐ[k] K, τ ∈ G → ∀ f : K, f ∈ B → τ f ∈ B)
    (hB₀ : ∀ f : K, f ∈ B₀ ↔ f ∈ B ∧ ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ f = f)
    (hfrac : ∀ f : K, ∃ g h' : ↥B, (h' : K) ≠ 0 ∧ f * (h' : K) = (g : K))
    (f : K) (hf : ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ f = f) :
    ∃ g h' : ↥B₀, (h' : K) ≠ 0 ∧ f * (h' : K) = (g : K) := by
  classical
  haveI : Fintype ↥G := Fintype.ofFinite _
  obtain ⟨g, h', hh0, hfg⟩ := hfrac f

  let N : K := ∏ σ : ↥G, (σ : K ≃ₐ[k] K) (h' : K)
  have hNB : N ∈ B := Subalgebra.prod_mem B (fun σ _ => h σ σ.2 _ h'.2)
  have hN0 : N ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro σ _
    exact (map_ne_zero_iff _ (σ : K ≃ₐ[k] K).injective).mpr hh0
  have hNinv : ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ N = N := by
    intro τ hτ
    simp only [N, map_prod]
    simp_rw [← AlgEquiv.mul_apply]
    exact Fintype.prod_equiv (Equiv.mulLeft ⟨τ, hτ⟩) _ _ (fun σ => rfl)

  let P : K := ∏ σ ∈ (Finset.univ : Finset ↥G).erase 1, (σ : K ≃ₐ[k] K) (h' : K)
  have hPB : P ∈ B := Subalgebra.prod_mem B (fun σ _ => h σ σ.2 _ h'.2)
  have hNP : N = (h' : K) * P := by
    simp only [N, P]
    rw [← Finset.mul_prod_erase (Finset.univ : Finset ↥G) _ (Finset.mem_univ (1 : ↥G))]
    rfl
  have hfN : f * N = (g : K) * P := by rw [hNP, ← mul_assoc, hfg]
  have hfNB : f * N ∈ B := by rw [hfN]; exact B.mul_mem g.2 hPB
  have hfNinv : ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ (f * N) = f * N := by
    intro τ hτ; rw [map_mul, hf τ hτ, hNinv τ hτ]
  exact ⟨⟨f * N, (hB₀ _).mpr ⟨hfNB, hfNinv⟩⟩, ⟨N, (hB₀ _).mpr ⟨hNB, hNinv⟩⟩, hN0, rfl⟩

end C3Kit4
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_framed.S3GlueKit P2MW.S_ModularCurve_FullLevel_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_framed.C3Kit2"

namespace C3GlueKit
open IsLocalRing

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {O : Type*} [CommRing O] [Algebra O K]

theorem prime_and_loc_of_invariants
    (G : Subgroup (K ≃ₐ[k] K)) (Bt B₀ : Subalgebra O K) (Wt : ValuationSubring K)
    (hBW : ∀ f : K, f ∈ Bt → f ∈ Wt)
    (hB₀ : ∀ f : K, f ∈ B₀ ↔ f ∈ Bt ∧ ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ f = f)
    (π : O) (hπm : (⟨algebraMap O K π, hBW _ (Bt.algebraMap_mem π)⟩ : ↥Wt) ∈ maximalIdeal ↥Wt)
    (hπne : algebraMap O K π ≠ 0)
    (hGO : ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ (algebraMap O K π) = algebraMap O K π)
    (P : (K ≃ₐ[k] K) → Prop) (hPG : ∀ τ, P τ → τ ∈ G)
    (hR5c : ∀ b : ↥Bt, (∀ τ : K ≃ₐ[k] K, P τ → ∀ hb : τ (b : K) ∈ Bt,
        (⟨τ (b : K), hBW _ hb⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) → algebraMap O ↥Bt π ∣ b)
    (K₀ : IntermediateField k K) (hK₀B₀ : ∀ f : K, f ∈ B₀ → f ∈ K₀)
    (hK₀G : ∀ f : K, f ∈ K₀ → ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ f = f)
    (W₀ : ValuationSubring ↥K₀) (hW₀ : ∀ f : ↥K₀, f ∈ W₀ ↔ ((f : K)) ∈ Wt)
    (hloc : ∀ f : K, (∀ g : ↥G, g • f = f) →
      (f ∈ Wt ↔ ∃ g h : K, g ∈ Bt.toSubring ∧ h ∈ Bt.toSubring ∧ (∀ σ : ↥G, σ • g = g) ∧ (∀ σ : ↥G, σ • h = h) ∧
        (∀ hh : h ∈ Wt, (⟨h, hh⟩ : ↥Wt) ∉ maximalIdeal ↥Wt) ∧ f * h = g)) :
    (∀ b : ↥B₀, ((⟨(b : K), hBW _ ((hB₀ _).mp b.2).1⟩ : ↥Wt) ∈ maximalIdeal ↥Wt ↔ algebraMap O ↥B₀ π ∣ b)) ∧
    Prime (algebraMap O ↥B₀ π) ∧
    (∀ f : ↥K₀, f ∈ W₀ ↔ ∃ g h : ↥B₀, ¬ (algebraMap O ↥B₀ π ∣ h) ∧ (f : K) * (h : K) = (g : K)) := by
  have hcoeπ : ((algebraMap O ↥B₀ π : ↥B₀) : K) = algebraMap O K π := Subalgebra.coe_algebraMap B₀ π
  have KEY : ∀ b : ↥B₀, ((⟨(b : K), hBW _ ((hB₀ _).mp b.2).1⟩ : ↥Wt) ∈ maximalIdeal ↥Wt ↔ algebraMap O ↥B₀ π ∣ b) := by
    intro b
    obtain ⟨hbBt, hbfix⟩ := (hB₀ _).mp b.2
    constructor
    · intro hm
      have hprem : ∀ τ : K ≃ₐ[k] K, P τ → ∀ hb : τ ((⟨(b : K), hbBt⟩ : ↥Bt) : K) ∈ Bt,
          (⟨τ ((⟨(b : K), hbBt⟩ : ↥Bt) : K), hBW _ hb⟩ : ↥Wt) ∈ maximalIdeal ↥Wt := by
        intro τ hP hb
        have e : τ (b : K) = (b : K) := hbfix τ (hPG τ hP)
        have : (⟨τ ((⟨(b : K), hbBt⟩ : ↥Bt) : K), hBW _ hb⟩ : ↥Wt) = ⟨(b : K), hBW _ hbBt⟩ := Subtype.ext e
        rw [this]; exact hm
      obtain ⟨c, hc⟩ := hR5c ⟨(b : K), hbBt⟩ hprem
      have hcK : (b : K) = algebraMap O K π * (c : K) := by
        have := congrArg (fun z : ↥Bt => (z : K)) hc
        simpa [Subalgebra.coe_algebraMap] using this
      have hcfix : ∀ τ : K ≃ₐ[k] K, τ ∈ G → τ (c : K) = (c : K) := by
        intro τ hτ
        have h1 := hbfix τ hτ
        rw [hcK, map_mul, hGO τ hτ] at h1
        exact mul_left_cancel₀ hπne h1
      have hcB₀ : (c : K) ∈ B₀ := (hB₀ _).mpr ⟨c.2, hcfix⟩
      refine ⟨⟨(c : K), hcB₀⟩, Subtype.ext ?_⟩
      rw [Subalgebra.coe_mul, hcoeπ]; exact hcK
    · rintro ⟨c, hc⟩
      have hcK : (b : K) = algebraMap O K π * (c : K) := by
        have := congrArg (fun z : ↥B₀ => (z : K)) hc
        beta_reduce at this
        rw [Subalgebra.coe_mul, hcoeπ] at this; exact this
      have hcW : (c : K) ∈ Wt := hBW _ ((hB₀ _).mp c.2).1
      have : (⟨(b : K), hBW _ hbBt⟩ : ↥Wt) = ⟨algebraMap O K π, hBW _ (Bt.algebraMap_mem π)⟩ * ⟨(c : K), hcW⟩ :=
        Subtype.ext hcK
      rw [this]
      exact Ideal.mul_mem_right _ _ hπm
  refine ⟨KEY, ?_, ?_⟩
  ·
    have hmprime : (maximalIdeal ↥Wt).IsPrime := Ideal.IsMaximal.isPrime inferInstance
    refine ⟨?_, ?_, ?_⟩
    · intro h0
      apply hπne
      have := congrArg (fun z : ↥B₀ => (z : K)) h0
      beta_reduce at this
      rw [hcoeπ] at this; simpa using this
    · intro hu
      have hu' : IsUnit ((⟨algebraMap O K π, hBW _ (Bt.algebraMap_mem π)⟩ : ↥Wt)) := by
        obtain ⟨u, hu⟩ := hu
        have hval : ((u : ↥B₀) : K) = algebraMap O K π := by rw [hu, hcoeπ]
        have hinv : ((u⁻¹ : (↥B₀)ˣ) : ↥B₀) * (u : ↥B₀) = 1 := u.inv_mul
        refine isUnit_iff_exists_inv'.mpr ⟨⟨((u⁻¹ : (↥B₀)ˣ) : ↥B₀), hBW _ ((hB₀ _).mp ((u⁻¹ : (↥B₀)ˣ) : ↥B₀).2).1⟩, Subtype.ext ?_⟩
        have := congrArg (fun z : ↥B₀ => (z : K)) hinv
        beta_reduce at this
        rw [Subalgebra.coe_mul, hval, Subalgebra.coe_one] at this
        exact this
      exact (mem_maximalIdeal _ |>.mp hπm) hu'
    · intro a b hab
      rw [← KEY] at hab ⊢; rw [← KEY]
      have : (⟨((a * b : ↥B₀) : K), hBW _ ((hB₀ _).mp (a * b).2).1⟩ : ↥Wt) =
          ⟨(a : K), hBW _ ((hB₀ _).mp a.2).1⟩ * ⟨(b : K), hBW _ ((hB₀ _).mp b.2).1⟩ := Subtype.ext (Subalgebra.coe_mul B₀ a b)
      rw [this] at hab
      exact hmprime.mem_or_mem hab
  ·
    intro f
    rw [hW₀, hloc (f : K) (fun g => hK₀G _ f.2 g g.2)]
    constructor
    · rintro ⟨g, h, hg, hh, hgfix, hhfix, hunit, hfh⟩
      have hgB₀ : g ∈ B₀ := (hB₀ _).mpr ⟨Subalgebra.mem_toSubring.mp hg, fun τ hτ => hgfix ⟨τ, hτ⟩⟩
      have hhB₀ : h ∈ B₀ := (hB₀ _).mpr ⟨Subalgebra.mem_toSubring.mp hh, fun τ hτ => hhfix ⟨τ, hτ⟩⟩
      refine ⟨⟨g, hgB₀⟩, ⟨h, hhB₀⟩, fun hd => ?_, hfh⟩
      have hm := (KEY ⟨h, hhB₀⟩).mpr hd
      exact hunit _ hm
    · rintro ⟨g, h, hnd, hfh⟩
      refine ⟨(g : K), (h : K), Subalgebra.mem_toSubring.mpr ((hB₀ _).mp g.2).1, Subalgebra.mem_toSubring.mpr ((hB₀ _).mp h.2).1, fun σ => ((hB₀ _).mp g.2).2 σ σ.2,
        fun σ => ((hB₀ _).mp h.2).2 σ σ.2, fun hh hm => hnd ((KEY h).mp ?_), hfh⟩
      have : (⟨(h : K), hh⟩ : ↥Wt) = ⟨(h : K), hBW _ ((hB₀ _).mp h.2).1⟩ := rfl
      rw [← this]; exact hm

end C3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_framed.S3GlueKit P2MW.S_ModularCurve_FullLevel_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_framed.C3Kit2"

namespace C3GlueKit
section kitW
open IsLocalRing

theorem mem_iff_map_mem_of_pow_eq_one {k K : Type*} [Field k] [Field K] [Algebra k K]
    {S : Type*} [SetLike S K] (B : S) (W : ValuationSubring K)
    (hBW : ∀ f : K, f ∈ B → f ∈ W)
    (hloc : ∀ f : K, f ∈ W ↔ ∃ g h : K, g ∈ B ∧ h ∈ B ∧ (∀ hh : h ∈ W, (⟨h, hh⟩ : ↥W) ∉ maximalIdeal ↥W) ∧ f * h = g)
    (μ : K ≃ₐ[k] K) (n : ℕ) (hn : 0 < n) (hμn : μ ^ n = 1)
    (hμB : ∀ f : K, f ∈ B → μ f ∈ B)
    (hμP : ∀ (f : K) (hf : f ∈ B), (⟨f, hBW f hf⟩ : ↥W) ∈ maximalIdeal ↥W → (⟨μ f, hBW _ (hμB f hf)⟩ : ↥W) ∈ maximalIdeal ↥W)
    (f : K) : f ∈ W ↔ μ f ∈ W := by

  have hμmB : ∀ (m : ℕ) (f : K), f ∈ B → (μ ^ m) f ∈ B := by
    intro m; induction m with
    | zero => intro f hf; simpa using hf
    | succ m ih => intro f hf; rw [pow_succ, AlgEquiv.mul_apply]; exact ih _ (hμB f hf)
  have hμmP : ∀ (m : ℕ) (f : K) (hf : f ∈ B), (⟨f, hBW f hf⟩ : ↥W) ∈ maximalIdeal ↥W →
      (⟨(μ ^ m) f, hBW _ (hμmB m f hf)⟩ : ↥W) ∈ maximalIdeal ↥W := by
    intro m; induction m with
    | zero => intro f hf h; simpa using h
    | succ m ih =>
      intro f hf h
      have h1 := ih _ (hμB f hf) (hμP f hf h)
      have e : (μ ^ (m + 1)) f = (μ ^ m) (μ f) := by rw [pow_succ, AlgEquiv.mul_apply]
      have : (⟨(μ ^ (m + 1)) f, hBW _ (hμmB (m + 1) f hf)⟩ : ↥W) = ⟨(μ ^ m) (μ f), hBW _ (hμmB m _ (hμB f hf))⟩ := Subtype.ext e
      rw [this]; exact h1

  have hμP' : ∀ (h : K) (hh : h ∈ B), (⟨μ h, hBW _ (hμB h hh)⟩ : ↥W) ∈ maximalIdeal ↥W → (⟨h, hBW h hh⟩ : ↥W) ∈ maximalIdeal ↥W := by
    intro h hh hm
    have h1 := hμmP (n - 1) (μ h) (hμB h hh) hm
    have e : (μ ^ (n - 1)) (μ h) = h := by
      rw [← AlgEquiv.mul_apply, ← pow_succ, Nat.sub_add_cancel hn, hμn, AlgEquiv.one_apply]
    have : (⟨(μ ^ (n - 1)) (μ h), hBW _ (hμmB (n - 1) _ (hμB h hh))⟩ : ↥W) = ⟨h, hBW h hh⟩ := Subtype.ext e
    rw [← this]; exact h1

  have fwd : ∀ f : K, f ∈ W → μ f ∈ W := by
    intro f hf
    obtain ⟨g, h, hg, hh, hunit, hfh⟩ := (hloc f).mp hf
    refine (hloc (μ f)).mpr ⟨μ g, μ h, hμB g hg, hμB h hh, fun hh' hm => hunit (hBW h hh) (hμP' h hh ?_), by rw [← map_mul, hfh]⟩
    have : (⟨μ h, hh'⟩ : ↥W) = ⟨μ h, hBW _ (hμB h hh)⟩ := rfl
    rw [← this]; exact hm
  refine ⟨fwd f, fun hμf => ?_⟩
  have h1 : (μ ^ (n - 1)) (μ f) ∈ W := by
    have : ∀ (m : ℕ) (x : K), x ∈ W → (μ ^ m) x ∈ W := by
      intro m; induction m with
      | zero => intro x hx; simpa using hx
      | succ m ih => intro x hx; rw [pow_succ, AlgEquiv.mul_apply]; exact ih _ (fwd x hx)
    exact this _ _ hμf
  rwa [← AlgEquiv.mul_apply, ← pow_succ, Nat.sub_add_cancel hn, hμn, AlgEquiv.one_apply] at h1

theorem exists_prime_pullback {k K : Type*} [Field k] [Field K] [Algebra k K] {O : Type*} [CommRing O] [Algebra O K]
    (Bt : Subalgebra O K) (W : ValuationSubring K) (hBW : ∀ f : K, f ∈ Bt → f ∈ W)
    (τ : K ≃ₐ[k] K) (hτB : ∀ f : K, f ∈ Bt → τ f ∈ Bt) :
    ∃ Q : Ideal ↥Bt, Q.IsPrime ∧
      ∀ b : ↥Bt, b ∈ Q ↔ (⟨τ (b : K), hBW _ (hτB _ b.2)⟩ : ↥W) ∈ maximalIdeal ↥W := by
  let φ : ↥Bt →+* ↥W :=
    { toFun := fun b => ⟨τ (b : K), hBW _ (hτB _ b.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  refine ⟨(maximalIdeal ↥W).comap φ, Ideal.comap_isPrime φ (maximalIdeal ↥W), fun b => ?_⟩
  rw [Ideal.mem_comap]; exact Iff.rfl

end kitW
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_framed.S3GlueKit P2MW.S_ModularCurve_FullLevel_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_framed.C3Kit2"
end C3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_framed.S3GlueKit P2MW.S_ModularCurve_FullLevel_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_framed.C3Kit2"

namespace C3GlueKit
section kitK4
open IsLocalRing

theorem mem_maximalIdeal_of_restrict {k E : Type*} [Field k] [Field E] [Algebra k E]
    (K₀ : IntermediateField k E) (Wt : ValuationSubring E) (W₀ : ValuationSubring ↥K₀)
    (hW₀ : ∀ f : ↥K₀, f ∈ W₀ ↔ ((f : E)) ∈ Wt)
    (x : ↥W₀) (hx : (⟨((x : ↥K₀) : E), (hW₀ _).mp x.2⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) :
    x ∈ maximalIdeal ↥W₀ := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  intro hu
  apply hx
  obtain ⟨u, hu⟩ := hu
  have hinv : ((u⁻¹ : (↥W₀)ˣ) : ↥W₀) * (u : ↥W₀) = 1 := u.inv_mul
  refine isUnit_iff_exists_inv'.mpr ⟨⟨(((u⁻¹ : (↥W₀)ˣ) : ↥W₀) : ↥K₀), (hW₀ _).mp ((u⁻¹ : (↥W₀)ˣ) : ↥W₀).2⟩, Subtype.ext ?_⟩
  have h1 := congrArg (fun z : ↥W₀ => (((z : ↥K₀)) : E)) hinv
  beta_reduce at h1
  show (((((u⁻¹ : (↥W₀)ˣ) : ↥W₀) : ↥K₀) : E)) * ((x : ↥K₀) : E) = 1
  rw [← hu]
  have h2 : (((((u⁻¹ : (↥W₀)ˣ) : ↥W₀) * (u : ↥W₀) : ↥W₀) : ↥K₀) : E) =
      (((((u⁻¹ : (↥W₀)ˣ) : ↥W₀) : ↥K₀) : E)) * ((((u : ↥W₀)) : ↥K₀) : E) := rfl
  rw [← h2, h1]; rfl

end kitK4
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_framed.S3GlueKit P2MW.S_ModularCurve_FullLevel_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_framed.C3Kit2"
end C3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_framed.S3GlueKit P2MW.S_ModularCurve_FullLevel_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_framed.C3Kit2"

set_option maxHeartbeats 0 in

theorem solution
    (q : ℕ)
    [Fact q.Prime]
    (M' : ℕ)
    [NeZero M']
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
    (ℓ' : ℕ)
    [Fact ℓ'.Prime]
    (ξ : ↥k₀)
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
    (hjK : ModularCurve.jqNModC ↥k₀ (q * ℓ') ∈ Kℓ)
    (a₀ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (ends : Finset (Subring ↥Kℓ))
    (ℱ : ModularCurve.FullLevel.RigidDescentHyps q M' A W hle R₀ s k₀ π₀ hπ ℓ ζ₀ ϖt Kb Ab hAb ϖb ℓ' ξ Kℓ jℓ ϖt' y Bt Wt hBW n γ₀ τ₀ m ζc hjK a₀ ends)
    (G : Subgroup (↥Kℓ ≃ₐ[↥k₀] ↥Kℓ))
    (hG : G = Subgroup.closure {τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ Kℓ τ})
    (K₀ : IntermediateField ↥k₀ ↥Kℓ)
    (hK₀ : K₀ = IntermediateField.fixedField G)
    (B₀ : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)
    (hB₀ : ∀ f : ↥Kℓ, f ∈ B₀ ↔ f ∈ Bt ∧ ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → τ f = f)
    (W₀' : ValuationSubring ↥K₀)
    (hW₀' : ∀ f : ↥K₀, f ∈ W₀' ↔ ((f : ↥Kℓ)) ∈ Wt)
    :

      (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥K₀ x ∈ W₀') ∧
      IsDiscreteValuationRing ↥W₀' ∧
      (∃ hπW : algebraMap ↥k₀ ↥K₀ π₀ ∈ W₀', maximalIdeal ↥W₀' = Ideal.span {(⟨_, hπW⟩ : ↥W₀')}) ∧

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
          ∀ (hgK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g) ∈ Kℓ), ∃ hF : (⟨ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g), hgK⟩ : ↥Kℓ) ∈ K₀,
            (⟨_, hF⟩ : ↥K₀) ∈ W₀' ∧
            ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
              residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
              ∃ hm : (⟨_, hF⟩ : ↥K₀) - algebraMap ↥k₀ ↥K₀ c ∈ W₀', (⟨_, hm⟩ : ↥W₀') ∈ maximalIdeal ↥W₀') ∧

      (∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ), ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ Kℓ τ →
        ∀ (f : ↥Kℓ) (hf : f ∈ K₀) (hf' : τ f ∈ K₀),
          (⟨f, hf⟩ : ↥K₀) ∈ W₀' ↔ (⟨_, hf'⟩ : ↥K₀) ∈ W₀') ∧

      (

        (∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ a : ↥B₀) : ↥Kℓ) = algebraMap ↥k₀ ↥Kℓ (a : ↥k₀)) ∧

        (∀ f : ↥Kℓ, f ∈ B₀ → f ∈ K₀) ∧
        (∀ f : ↥Kℓ, f ∈ K₀ → ∃ g h : ↥B₀, (h : ↥Kℓ) ≠ 0 ∧ f * (h : ↥Kℓ) = (g : ↥Kℓ)) ∧

        Algebra.FormallySmooth ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ ∧ Algebra.FinitePresentation ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ ∧
        Ring.KrullDimLE 1 (↥B₀ ⧸ Ideal.span {algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ ⟨π₀, hπ⟩}) ∧

        (∀ f : ↥Kℓ, f ∈ B₀ → ∃ hf : f ∈ K₀, (⟨f, hf⟩ : ↥K₀) ∈ W₀') ∧
        Prime (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ ⟨π₀, hπ⟩) ∧
        (∀ f : ↥K₀, f ∈ W₀' ↔ ∃ g h : ↥B₀, ¬ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ ⟨π₀, hπ⟩ ∣ h) ∧ (f : ↥Kℓ) * (h : ↥Kℓ) = (g : ↥Kℓ)) ∧

        (∀ (hjK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ jq) ∈ Kℓ), (⟨ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ jq), hjK⟩ : ↥Kℓ) ∈ B₀) ∧
        (∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ), ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ Kℓ τ → ∀ f : ↥Kℓ, f ∈ B₀ → τ f ∈ B₀) ∧

        (∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥A)),
          ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
          ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
            (ρ : ↥B₀ →+* ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
            Nat.card Cs = 2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
            RingHom.ker ρ = Ideal.span {algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ ⟨π₀, hπ⟩} ∧
            (∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), ρ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ a) =
              algebraMap (ResidueField ↥A) ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) (IsLocalRing.residue ↥A ⟨((a : ↥k₀) : (AlgebraicClosure ℚ)), a.2⟩)) ∧
            (∀ z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs), ∃ g h : ↥B₀, ρ h ≠ 0 ∧ z * ρ h = ρ g) ∧
            (∀ z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs), z ∈ Set.range ρ ↔
              (z : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ∈ Set.range (algebraMap (DrinfeldCurve.CoordRing q (ResidueField ↥A)) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) ∧
            (∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ), ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ Kℓ τ →
              ∀ (hmem : (redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q)
                (f : ↥B₀) (hf' : τ (f : ↥Kℓ) ∈ B₀),
                ((ρ ⟨_, hf'⟩ : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                  DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((ρ f : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))))) := by
  have hℱ := ℱ
  obtain ⟨hq, hqM', hA, hW, hR₀, hdvr, hunif, hhens, hres, hκ, hℓ, hℓ3, hℓq, hℓM', hζ₀, hϖtA, hϖt, hKb, hϖb, hϖb0, hℓ'3, hℓ'q, hℓ'M, htame, hξ, hKℓ, hjℓ, hϖt', hy, hϖy, hss, hover, hOrbit, hS1, hn1, hnq, hγ₀Γ, hγ₀Γ0, hτ₀, hτ₀W, hm1, hm, hζc, hζcprim, hjC, ha₀y, hR7, hR9, hR10, hn⟩ := hℱ
  classical
  haveI hmne : NeZero (q * ℓ') := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero⟩

  have hObt1 := C3aux_exists_emb k₀ (q * ℓ') ξ hξ
  obtain ⟨ι, hι'⟩ := hObt1
  have hι : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ')) :=
    ⟨ι, by rw [hι']; simp only [Nat.cast_mul]⟩
  have hObt2 := ModularCurve.FullLevel.AuxLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M ↥k₀ ξ hξ hι Kℓ hKℓ
  obtain ⟨huniq, hmul, hone⟩ := hObt2
  obtain ⟨Gfull, hGfin, hGmem⟩ :=
    ModularCurve.FullLevel.AuxLevel.exists_finite_subgroup_forall_mem_iff_exists_isLevelAutAt_of_exists_ringHom
      q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M ↥k₀ ξ hξ hι Kℓ hKℓ
  have hex := ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
      q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M ↥k₀ ξ hξ hι Kℓ hKℓ

  have hGle : G ≤ Gfull := by
    rw [hG, Subgroup.closure_le]
    rintro τ ⟨γ, -, hγ0, hτ⟩
    exact (hGmem τ).mpr ⟨γ, hγ0, hτ⟩
  haveI hGfinite : Finite ↥G := by
    haveI := hGfin
    exact Finite.of_injective (Subgroup.inclusion hGle) (Subgroup.inclusion_injective hGle)
  have hGatt : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G →
      ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ Kℓ τ := by
    intro τ hτ
    rw [hG] at hτ
    refine Subgroup.closure_induction (p := fun τ _ => ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧
        γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ Kℓ τ) ?_ ?_ ?_ ?_ hτ
    · intro τ h; exact h
    · exact ⟨1, Subgroup.one_mem _, Subgroup.one_mem _, by rw [inv_one]; exact hone 1 (Subgroup.one_mem _) (Subgroup.one_mem _)⟩
    · rintro τ σ - - ⟨γ, hγq, hγ0, hτ⟩ ⟨δ, hδq, hδ0, hσ⟩
      refine ⟨γ * δ, Subgroup.mul_mem _ hγq hδq, Subgroup.mul_mem _ hγ0 hδ0, ?_⟩
      rw [mul_inv_rev]
      exact hmul γ⁻¹ δ⁻¹ (Subgroup.inv_mem _ hγ0) (Subgroup.inv_mem _ hδ0) τ σ hτ hσ
    · rintro τ - ⟨γ, hγq, hγ0, hτ⟩
      have hObt3 := hex γ⁻¹ (Subgroup.inv_mem _ hγ0)
      obtain ⟨σ, hσ⟩ := hObt3
      rw [inv_inv] at hσ

      have h1 : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') (γ * γ⁻¹) Kℓ (τ * σ) := hmul γ⁻¹ γ (Subgroup.inv_mem _ hγ0) hγ0 τ σ hτ hσ
      rw [mul_inv_cancel] at h1
      have h2 : τ * σ = 1 := huniq 1 (Subgroup.one_mem _) _ _ h1 (hone 1 (Subgroup.one_mem _) (Subgroup.one_mem _))
      have h3 : τ⁻¹ = σ := inv_eq_of_mul_eq_one_right h2
      refine ⟨γ⁻¹, Subgroup.inv_mem _ hγq, Subgroup.inv_mem _ hγ0, ?_⟩
      rw [inv_inv, h3]; exact hσ

  obtain ⟨hR1a, hR1b, hR2a, hR2b, hR2c, hR3a, hR3b, hR3c, hR3d, hR3e, hR46, hR5a, hR5b, hR5c⟩ := hS1
  have hGBt : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → ∀ f : ↥Kℓ, f ∈ Bt → τ f ∈ Bt := by
    intro τ hτ f hf
    have hObt4 := hGatt τ hτ
    obtain ⟨γ, -, hγ0, hτ'⟩ := hObt4
    exact hR5a γ hγ0 τ hτ' f hf

  have hB₀le : B₀ ≤ Bt := fun f hf => ((hB₀ f).mp hf).1
  letI instAct : MulSemiringAction ↥G ↥Bt := C3Kit.subalgAction G Bt hGBt
  letI instAlg : Algebra ↥B₀ ↥Bt := C3Kit.inclAlgebra B₀ Bt hB₀le
  haveI instIST : IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ ↥Bt := C3Kit.inclAlgebra_isScalarTower B₀ Bt hB₀le
  haveI instFS : FaithfulSMul ↥B₀ ↥Bt := C3Kit.inclAlgebra_faithfulSMul B₀ Bt hB₀le
  haveI instGal : IsGaloisGroup ↥G ↥B₀ ↥Bt := C3Kit.isGaloisGroup G Bt B₀ hGBt hB₀ hR1b
  haveI instSCC : SMulCommClass ↥G ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt := C3Kit.smulCommClass G Bt hGBt
  haveI : Algebra.FinitePresentation ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt := hR2b
  haveI hdvr0 : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := hdvr

  have hGunit : IsUnit ((Nat.card ↥G : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := by
    have hObt5 := ModularCurve.FullLevel.AuxLevel.finite_and_natCard_dvd_of_eq_closure_isLevelAutAt_gamma q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M ↥k₀ ξ hξ hι Kℓ hKℓ G hG
    obtain ⟨-, hGdvd⟩ := hObt5
    exact isUnit_of_dvd_unit (Nat.cast_dvd_cast hGdvd) htame

  have hC1 := IsGaloisGroup.finitePresentation_and_smooth_invariants_typeZero_of_isUnit_natCard_of_smooth_fibers
    ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ ↥Bt ↥G hGunit
  obtain ⟨hB₀ft, hB₀fp, hBtfin, hB₀normal, hB₀flat, hB₀fib, hB₀smooth⟩ := hC1

  have hπW : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ Wt := hBW _ (Bt.algebraMap_mem ⟨π₀, hπ⟩)
  have hπeq : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ = algebraMap ↥k₀ ↥Kℓ π₀ :=
    IsScalarTower.algebraMap_apply ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ ⟨π₀, hπ⟩
  have hπG : ∀ g : ↥G, g • algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ = algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ := by
    intro g
    rw [hπeq]
    exact (g : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ).commutes π₀
  have hπK₀ : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ K₀ := by
    rw [hπeq]; exact K₀.algebraMap_mem π₀
  have hBG' : ∀ (g : ↥G) (b : ↥Kℓ), b ∈ Bt.toSubring → g • b ∈ Bt.toSubring := fun g b hb => hGBt g g.2 b hb
  have hloc' := C3Kit2.hloc_reshape Bt Wt hBW hR3e
  haveI hWtdvr : IsDiscreteValuationRing ↥Wt := hR3c

  have hqp : q.Prime := Fact.out
  have hqmem : ((q : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hqA : ((q : ℕ) : ↥A) ∈ maximalIdeal ↥A := by
      have hq' : (((q : ℕ) : ↥A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := by norm_cast
      rw [← ValuationSubring.coe_mem_nonunits_iff, hq']; exact hA
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hqA
    apply hqA
    obtain ⟨v, hv⟩ := hu
    refine isUnit_iff_exists_inv.mpr ⟨⟨(((v⁻¹ : (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))ˣ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : ↥k₀), ((v⁻¹ : (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))ˣ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))).2⟩, Subtype.ext ?_⟩
    have e := congrArg (fun z : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) => (((z : ↥k₀)) : AlgebraicClosure ℚ)) v.mul_inv
    rw [hv] at e
    push_cast at e ⊢
    simpa using e
  haveI hchar : CharP (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) q := by
    have h0 : ((q : ℕ) : ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) = 0 := by
      rw [← map_natCast (IsLocalRing.residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))), IsLocalRing.residue_eq_zero_iff]; exact hqmem
    exact (CharP.charP_iff_prime_eq_zero hqp).mpr h0
  haveI hresI : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := hres
  letI instZ : Algebra (ZMod q) (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := ZMod.algebra (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) q
  letI instGF : Algebra (GaloisField q 2) (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) :=
    (IsAlgClosed.lift : GaloisField q 2 →ₐ[ZMod q] ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))).toRingHom.toAlgebra

  have hfaith : ∀ (g : ↥G) (hg : ∀ x : ↥Kℓ, g • x ∈ Wt ↔ x ∈ Wt), g ≠ 1 → ∃ x : ↥Wt,
      (⟨g • (x : ↥Kℓ), (hg x).mpr x.2⟩ - x : ↥Wt) ∉ maximalIdeal ↥Wt := by
    intro g hg hne
    have hObt6 := hGatt g g.2
    obtain ⟨γ, hγq, hγ0, hτ⟩ := hObt6
    have hObt7 := hR46 instGF
    obtain ⟨ρ, hρsurj, hρker, -, hρeq⟩ := hObt7
    have hdec : ∀ f : ↥Kℓ, f ∈ Wt ↔ (g : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) f ∈ Wt := fun f => (hg f).symm
    have hObt8 := hρeq γ hγ0 (g : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) hτ hdec
    obtain ⟨c, hmem, hcomm, hc, -⟩ := hObt8
    have hne' : ¬ ∀ x : ↥Kℓ, (g : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) x = x := by
      intro hall; apply hne
      apply Subtype.ext; apply AlgEquiv.ext; intro x
      rw [hall x]; rfl
    have hc1 : c ≠ 1 := hc hγq hne'

    have hp1 : ((⟨(ModularCurve.FullLevel.redQ q γ, c), hmem⟩ : ↥(DrinfeldCurve.hSubgroup q)) :
        Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1 = 1 := by
      show ModularCurve.FullLevel.redQ q γ = 1
      show Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))) γ) = 1
      rw [CongruenceSubgroup.Gamma_mem'.mp hγq, map_one]
    have hp2 : DrinfeldCurve.scalarOf q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
        ((⟨(ModularCurve.FullLevel.redQ q γ, c), hmem⟩ : ↥(DrinfeldCurve.hSubgroup q)) :
          Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2 ≠ 1 := by
      show algebraMap (GaloisField q 2) (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (c : GaloisField q 2) ≠ 1
      intro h1
      apply hc1
      apply Units.ext
      exact (algebraMap (GaloisField q 2) (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))).injective (h1.trans (map_one _).symm)
    have hmove := C3Kit3.hAction_x_ne q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨(ModularCurve.FullLevel.redQ q γ, c), hmem⟩ hp1 hp2

    have hObt9 := hρsurj (DrinfeldCurve.x q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    obtain ⟨b, hb⟩ := hObt9
    have hbτ : (g : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) (b : ↥Kℓ) ∈ Bt := hGBt g g.2 b b.2
    refine ⟨⟨(b : ↥Kℓ), hBW _ b.2⟩, ?_⟩
    intro hmax
    apply hmove

    have hdiff : (ρ (⟨(g : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) (b : ↥Kℓ), hbτ⟩ - b) = 0) := by
      rw [hρker]
      exact hmax
    rw [map_sub, hcomm b hbτ, hb, sub_eq_zero] at hdiff
    exact hdiff
  have hObt10 := C3Kit2.descDVR G Wt (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩) hπG hπW hR3b hfaith
    Bt.toSubring hBG' hBW hloc' K₀ hK₀ W₀' hW₀' hπK₀
  obtain ⟨hW₀dvr, ⟨hπ0, hW₀max⟩, hW₀loc⟩ := hObt10

  have hπelt : algebraMap ↥k₀ ↥K₀ π₀ = (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hπK₀⟩ : ↥K₀) := Subtype.ext hπeq.symm
  have hB₀K₀ : ∀ f : ↥Kℓ, f ∈ B₀ → f ∈ K₀ := by
    intro f hf
    rw [hK₀, IntermediateField.mem_fixedField_iff]
    exact ((hB₀ f).mp hf).2

  have hπne : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field (R := ↥Wt)
    rw [hR3b, Ideal.span_singleton_eq_bot]
    exact Subtype.ext h0
  have hGO : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → τ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩) = algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ :=
    fun τ _ => by rw [hπeq]; exact τ.commutes π₀
  have hPG : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, (∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ Kℓ τ) → τ ∈ G :=
    fun τ h => by rw [hG]; exact Subgroup.subset_closure h
  have hR5c' : ∀ b : ↥Bt, (∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, (∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ Kℓ τ) →
      ∀ hb : τ (b : ↥Kℓ) ∈ Bt, (⟨τ (b : ↥Kℓ), hBW _ hb⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) →
      algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ⟨π₀, hπ⟩ ∣ b :=
    fun b h => hR5c b (fun γ hγq hγ0 τ hτ hb => h τ ⟨γ, hγq, hγ0, hτ⟩ hb)
  have hK₀G : ∀ f : ↥Kℓ, f ∈ K₀ → ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → τ f = f := by
    intro f hf; rw [hK₀, IntermediateField.mem_fixedField_iff] at hf; exact hf
  have hKEY := C3GlueKit.prime_and_loc_of_invariants G Bt B₀ Wt hBW hB₀ ⟨π₀, hπ⟩
    (by rw [hR3b]; exact Ideal.mem_span_singleton_self _) hπne hGO _ hPG hR5c' K₀ hB₀K₀ hK₀G W₀' hW₀' hW₀loc
  obtain ⟨KEY, hM2b, hM2c⟩ := hKEY
  refine ⟨?_, hW₀dvr, ?_, ?_, ?_, ?_, hB₀K₀, ?_, ?_, hB₀fp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x
    rw [hW₀']
    change (x : AlgebraicClosure ℚ) ∈ A ↔ algebraMap ↥k₀ ↥Kℓ x ∈ Wt
    rw [hR3a]
    exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
  ·
    rw [hπelt]; exact ⟨hπ0, hW₀max⟩
  ·
    intro g hg hgi hcusp hres hgK
    have hgC := ModularCurve.FullLevel.qExpand_coeffEmb_mem_chartAlgFin_of_mem_integers_of_cuspRegular_of_not_dvd q M' hqM' A hA R₀ hR₀ k₀ ℓ' Kℓ hKℓ jℓ hjℓ g hg hgi hcusp hgK
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    haveI : NeZero ℓ' := ⟨(Fact.out : ℓ'.Prime).ne_zero⟩
    have hx0 := ModularCurve.qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull ↥k₀ M' 1 (q ^ 2 * M')
      ⟨q ^ 2, by ring⟩ (ModularCurve.FullLevel.levelH q M') g hg
    rw [ModularCurve.qExpand_one_apply] at hx0
    have hfix : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → τ (⟨_, hgK⟩ : ↥Kℓ) = ⟨_, hgK⟩ := by
      intro τ hτ
      have hObt11 := hGatt τ hτ
      obtain ⟨γ, hγq, hγ0, hatt⟩ := hObt11
      exact (ModularCurve.FullLevel.qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_exists_ringHom q M'
        ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqM') ℓ' ↥k₀ ξ hξ hι Kℓ hKℓ).2 _ hx0 ⟨_, hgK⟩ rfl γ hγq hγ0 τ hatt
    have hF : (⟨_, hgK⟩ : ↥Kℓ) ∈ K₀ := by
      rw [hK₀, IntermediateField.mem_fixedField_iff]; exact hfix
    refine ⟨hF, ?_, ?_⟩
    · rw [hW₀']; exact hBW _ (hR1a hgC)
    · intro c hc hev
      have hy := hover g hg hgi hcusp hres hgK hgC c hc hev
      have hObt12 := (hR3d _).mp hy
      obtain ⟨hbW, hbm⟩ := hObt12
      have hAval : (((⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨c, hc⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) : ↥Kℓ) =
          (⟨_, hgK⟩ : ↥Kℓ) - algebraMap ↥k₀ ↥Kℓ c := by
        rw [Subalgebra.coe_sub, Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ]; rfl
      have hBval : ((((⟨_, hF⟩ : ↥K₀) - algebraMap ↥k₀ ↥K₀ c : ↥K₀)) : ↥Kℓ) = (⟨_, hgK⟩ : ↥Kℓ) - algebraMap ↥k₀ ↥Kℓ c := rfl
      have hm : ((⟨_, hF⟩ : ↥K₀) - algebraMap ↥k₀ ↥K₀ c) ∈ W₀' := by
        rw [hW₀', hBval, ← hAval]; exact hbW
      refine ⟨hm, C3GlueKit.mem_maximalIdeal_of_restrict K₀ Wt W₀' hW₀' ⟨_, hm⟩ ?_⟩
      have he : (⟨((((⟨_, hm⟩ : ↥W₀') : ↥K₀)) : ↥Kℓ), (hW₀' _).mp hm⟩ : ↥Wt) = ⟨_, hbW⟩ :=
        Subtype.ext (by rw [hAval]; exact hBval)
      rw [he]; exact hbm
  ·
    intro γ hγ τ hτ f hf hf'
    rw [hW₀', hW₀']
    show f ∈ Wt ↔ τ f ∈ Wt
    have hτB : ∀ x : ↥Kℓ, x ∈ Bt → τ x ∈ Bt := hR5a γ hγ τ hτ
    have hObt13 := C3GlueKit.exists_prime_pullback Bt Wt hBW τ hτB
    obtain ⟨Q, hQprime, hQmem⟩ := hObt13
    have hπQ : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ⟨π₀, hπ⟩ ∈ Q := by
      rw [hQmem]
      have e : τ ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ⟨π₀, hπ⟩ : ↥Bt) : ↥Kℓ) = algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ := by
        rw [Subalgebra.coe_algebraMap, hπeq]; exact τ.commutes π₀
      have e2 : (⟨τ ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ⟨π₀, hπ⟩ : ↥Bt) : ↥Kℓ), hBW _ (hτB _ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ⟨π₀, hπ⟩).2)⟩ : ↥Wt) =
          ⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hBW _ (Bt.algebraMap_mem ⟨π₀, hπ⟩)⟩ := Subtype.ext e
      rw [e2, hR3b]; exact Ideal.mem_span_singleton_self _
    have hObt14 := hR5b Q hQprime hπQ
    obtain ⟨γσ, hγσq, hγσ0, σ, hσatt, hσmove⟩ := hObt14
    have hσG : σ ∈ G := hPG σ ⟨γσ, hγσq, hγσ0, hσatt⟩
    have hσB : ∀ x : ↥Kℓ, x ∈ Bt → σ x ∈ Bt := hGBt σ hσG
    have hμB : ∀ x : ↥Kℓ, x ∈ Bt.toSubring → (τ * σ) x ∈ Bt.toSubring :=
      fun x hx => hτB _ (hσB _ hx)
    have hμP : ∀ (x : ↥Kℓ) (hx : x ∈ Bt.toSubring), (⟨x, hBW x hx⟩ : ↥Wt) ∈ maximalIdeal ↥Wt →
        (⟨(τ * σ) x, hBW _ (hμB x hx)⟩ : ↥Wt) ∈ maximalIdeal ↥Wt := by
      intro x hx hm
      have hObt15 := hσmove ⟨x, hx⟩ hm
      obtain ⟨hσx, hQ⟩ := hObt15
      have h2 := (hQmem ⟨σ x, hσx⟩).mp (hQ hσx)
      have e3 : (⟨(τ * σ) x, hBW _ (hμB x hx)⟩ : ↥Wt) = ⟨τ ((⟨σ x, hσx⟩ : ↥Bt) : ↥Kℓ), hBW _ (hτB _ hσx)⟩ := Subtype.ext rfl
      rw [e3]; exact h2

    have hμatt := hmul γ⁻¹ γσ⁻¹ (Subgroup.inv_mem _ hγ) (Subgroup.inv_mem _ hγσ0) τ σ hτ hσatt
    rw [← mul_inv_rev] at hμatt
    have hμmem : τ * σ ∈ Gfull := (hGmem (τ * σ)).mpr ⟨γ * γσ, Subgroup.mul_mem _ hγ hγσ0, hμatt⟩
    haveI := hGfin
    have hfin : IsOfFinOrder (⟨τ * σ, hμmem⟩ : ↥Gfull) := isOfFinOrder_of_finite _
    have hn0 : 0 < orderOf (⟨τ * σ, hμmem⟩ : ↥Gfull) := hfin.orderOf_pos
    have hμn : (τ * σ) ^ orderOf (⟨τ * σ, hμmem⟩ : ↥Gfull) = 1 := by
      have := pow_orderOf_eq_one (⟨τ * σ, hμmem⟩ : ↥Gfull)
      exact congrArg Subtype.val this
    have key := C3GlueKit.mem_iff_map_mem_of_pow_eq_one (k := ↥k₀) Bt.toSubring Wt (fun x hx => hBW x hx) hloc' (τ * σ) _ hn0 hμn hμB hμP f
    rw [key, AlgEquiv.mul_apply, hK₀G f hf σ hσG]
  ·
    intro a
    show algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a = algebraMap ↥k₀ ↥Kℓ (a : ↥k₀)
    exact IsScalarTower.algebraMap_apply ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ a
  ·
    intro f hf
    have hinv : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → τ f = f := by
      rw [hK₀, IntermediateField.mem_fixedField_iff] at hf
      exact fun τ hτ => hf τ hτ
    exact C3Kit4.exists_invariant_fraction G Bt B₀ hGBt hB₀ hR1b f hinv
  ·
    exact ModularCurve.FullLevel.AuxLevel.formallySmooth_invariants_of_rigidChart_framed q M' A W hle R₀ s k₀ π₀ hπ ℓ ζ₀ ϖt Kb Ab hAb ϖb ℓ' ξ Kℓ jℓ ϖt' y Bt Wt hBW n γ₀ τ₀ m ζc hjK a₀ ends ℱ G hG K₀ hK₀ B₀ hB₀ W₀' hW₀'
  ·
    have hmapBt : (Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))}).map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt) =
        Ideal.span {algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ⟨π₀, hπ⟩} := by
      rw [Ideal.map_span, Set.image_singleton]
    have hmapB₀ : (Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))}).map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀) =
        Ideal.span {algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥B₀ ⟨π₀, hπ⟩} := by
      rw [Ideal.map_span, Set.image_singleton]
    have h3 := (hB₀fib (Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})).2.2 1
    rw [hmapBt, hmapB₀] at h3
    exact h3 hR2c
  ·
    intro f hf
    exact ⟨hB₀K₀ f hf, (hW₀' _).mpr (hBW f (hB₀le hf))⟩
  ·
    exact hM2b
  ·
    exact hM2c
  ·
    intro hjK
    have hjsh := ModularCurve.FullLevel.qExpand_coeffEmb_jq_mem_and_mem_chartAlgFin_laurentBaseChange_xHFunctionField q M' ℓ' ↥k₀ Kℓ hKℓ ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))
    obtain ⟨hj, hj0, hjK', hjC⟩ := hjsh
    have hjℓeq : jℓ = ⟨coeffEmb ↥k₀ jq, hj⟩ := Subtype.ext hjℓ
    have hjBt : (⟨_, hjK⟩ : ↥Kℓ) ∈ Bt := by
      apply hR1a
      rw [hjℓeq]; exact hjC
    refine (hB₀ _).mpr ⟨hjBt, fun τ hτ => ?_⟩
    have hObt16 := hGatt τ hτ
    obtain ⟨γ, hγq, hγ0, hatt⟩ := hObt16
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    haveI : NeZero ℓ' := ⟨(Fact.out : ℓ'.Prime).ne_zero⟩
    have hx0 := ModularCurve.qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull ↥k₀ M' 1 (q ^ 2 * M')
      ⟨q ^ 2, by ring⟩ (ModularCurve.FullLevel.levelH q M') jq (modularFunctionField_le_full M' (jq_mem M'))
    rw [ModularCurve.qExpand_one_apply] at hx0
    exact (ModularCurve.FullLevel.qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_exists_ringHom q M'
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqM') ℓ' ↥k₀ ξ hξ hι Kℓ hKℓ).2 _ hx0 ⟨_, hjK⟩ rfl γ hγq hγ0 τ hatt
  ·
    intro γ hγ τ hτ f hf
    have hObt17 := (hB₀ f).mp hf
    obtain ⟨hfB, hfix⟩ := hObt17
    have hN := ModularCurve.FullLevel.AuxLevel.mul_mul_inv_mem_and_map_fixedField_of_isLevelAutAt_gamma0 q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M
      ↥k₀ ξ hξ hι Kℓ hKℓ G hG K₀ hK₀ γ hγ τ hτ
    obtain ⟨-, hconj, -, -⟩ := hN
    refine (hB₀ _).mpr ⟨hR5a γ hγ τ hτ f hfB, fun σ hσ => ?_⟩
    have h1 := hfix (τ⁻¹ * σ * τ) (hconj σ hσ)
    have h2 : σ (τ f) = τ ((τ⁻¹ * σ * τ) f) := by
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply τ τ⁻¹, mul_inv_cancel, AlgEquiv.one_apply]
    rw [h2, h1]
  ·
    exact ModularCurve.FullLevel.AuxLevel.exists_quotField_ringHom_invariants_of_rigidChart_framed q M' A W hle R₀ s k₀ π₀ hπ ℓ ζ₀ ϖt Kb Ab hAb ϖb ℓ' ξ Kℓ jℓ ϖt' y Bt Wt hBW n γ₀ τ₀ m ζc hjK a₀ ends ℱ G hG K₀ hK₀ B₀ hB₀ W₀' hW₀'

end S_ModularCurve_FullLevel_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_framed
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_supersingularDVR_affineChart_invariants_of_rigidChart_framed (solution)
