-- Prove2me | solution 1 for ModularCurve.FullLevel.qExpand_coeffEmb_mem_chartAlgFin_of_mem_integers_of_cuspRegular_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/85d41fec-8269-56b0-a2e2-a05ab708111c

import Mathlib
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
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_ModularCurve_coeffEmb_mem_chartAlgFin_of_forall_coeff_of_isIntegral_adjoin_jq
import Theorems.Thm_ModularCurve_FullLevel_qExpand_coeffEmb_jq_mem_and_mem_chartAlgFin_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_exists_ne_zero_forall_algebraMap_mul_coeff_mem_of_cuspRegular
import Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_qExpand_coeffEmb_mem_chartAlgFin_of_mem_integers_of_cuspRegular_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure"
p2m_attr_erase "instance" "mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qExpandAlgHomC_apply ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.val_heckeDiagMatrix"
p2m_attr_erase "simp" "ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero"
p2m_attr_erase "simp" "TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 51200000

p2m_open "AlgebraicCurve ModularCurve~coeffEmb_injective P2MW.S_ModularCurve_FullLevel_qExpand_coeffEmb_mem_chartAlgFin_of_mem_integers_of_cuspRegular_of_not_dvd.ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel"
open scoped MatrixGroups Polynomial

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace ModularCurve
p2m_export "ModularCurve" "FullLevel.levelH xHFunctionField modularFunctionFieldBar qExpand qExpand_single algebraMap_apply_eq_single jq jq_ne_zero jq_mem modularFunctionFieldFull modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_id coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jq_mem_full instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable modularFunctionFieldC coeffEmb_mem_chartAlgFin_of_forall_coeff_of_isIntegral_adjoin_jq FullLevel.qExpand_coeffEmb_jq_mem_and_mem_chartAlgFin_laurentBaseChange_xHFunctionField qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull exists_ne_zero_forall_algebraMap_mul_coeff_mem_of_cuspRegular transcendental_coeffEmb_jq finiteDimensional_adjoin_coeffEmb_jq_of_neZero hasPrincipalDivisors_modularFunctionFieldBar_unconditional"
namespace ChartMPrimeAux
p2m_open "ModularCurve~coeffEmb_injective"

theorem isIntegral_transfer
    {R₁ R₂ S U' U : Type*} [CommRing R₁] [CommRing R₂] [CommRing S] [CommRing U'] [CommRing U]
    [Algebra R₁ S] [Algebra R₂ U']
    (C : Subalgebra R₁ S) (D : Subalgebra R₂ U')
    (ψ : S →+* U) (τ : U' →+* U) (hτ : Function.Injective τ)
    (hCD : ∀ c : S, c ∈ C → ∃ d ∈ D, τ d = ψ c)
    {x : S} (hx : IsIntegral ↥C x) {x' : U'} (hx' : τ x' = ψ x) : IsIntegral ↥D x' := by
  classical
  choose d hdmem hd using hCD
  let φ : ↥C →+* ↥D :=
    { toFun := fun c => ⟨d c.1 c.2, hdmem c.1 c.2⟩
      map_one' := Subtype.ext (hτ (by simp [hd]))
      map_mul' := fun a b => Subtype.ext (hτ (by simp [hd]))
      map_zero' := Subtype.ext (hτ (by simp [hd]))
      map_add' := fun a b => Subtype.ext (hτ (by simp [hd])) }
  letI : Algebra ↥D U := (τ.comp (algebraMap ↥D U')).toAlgebra
  have h1 : IsIntegral ↥D (ψ x) := by
    refine hx.map_of_comp_eq φ ψ ?_
    ext c
    change τ (d c.1 c.2) = ψ c
    exact hd c.1 c.2
  let f : U' →ₐ[↥D] U := { τ with commutes' := fun _ => rfl }
  rw [← hx'] at h1
  exact (isIntegral_algHom_iff f hτ).mp h1

theorem forall_exists_of_generator
    {R₁ R₂ S U' U : Type*} [CommRing R₁] [CommRing R₂] [CommRing S] [CommRing U'] [CommRing U]
    [Algebra R₁ S] [Algebra R₂ U']
    (s : S) (D : Subalgebra R₂ U') (ψ : S →+* U) (τ : U' →+* U)
    (hs : ∃ d ∈ D, τ d = ψ s)
    (hsc : ∀ r : R₁, ∃ d ∈ D, τ d = ψ (algebraMap R₁ S r)) :
    ∀ c : S, c ∈ Algebra.adjoin R₁ ({s} : Set S) → ∃ d ∈ D, τ d = ψ c := by
  intro c hc
  refine Algebra.adjoin_induction (p := fun c _ => ∃ d ∈ D, τ d = ψ c) ?_ ?_ ?_ ?_ hc
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hs
  · exact hsc
  · rintro x y - - ⟨d₁, hd₁, h₁⟩ ⟨d₂, hd₂, h₂⟩
    exact ⟨d₁ + d₂, Subalgebra.add_mem _ hd₁ hd₂, by rw [map_add, map_add, h₁, h₂]⟩
  · rintro x y - - ⟨d₁, hd₁, h₁⟩ ⟨d₂, hd₂, h₂⟩
    exact ⟨d₁ * d₂, Subalgebra.mul_mem _ hd₁ hd₂, by rw [map_mul, map_mul, h₁, h₂]⟩

theorem isIntegral_adjoin_of_isIntegral_adjoin_of_isIntegral
    {R F : Type*} [CommRing R] [CommRing F] [Algebra R F] (j y x : F)
    (hy : IsIntegral ↥(Algebra.adjoin R ({j} : Set F)) y)
    (hx : IsIntegral ↥(Algebra.adjoin R ({y} : Set F)) x) :
    IsIntegral ↥(Algebra.adjoin R ({j} : Set F)) x := by
  classical
  set T : Subalgebra R F := Algebra.adjoin R ({j} : Set F) with hT

  let B : Subalgebra R F :=
    { carrier := {z | IsIntegral ↥T z}
      mul_mem' := fun ha hb => ha.mul hb
      one_mem' := isIntegral_one
      add_mem' := fun ha hb => ha.add hb
      zero_mem' := isIntegral_zero
      algebraMap_mem' := fun a => by
        have : IsIntegral ↥T (algebraMap ↥T F (algebraMap R ↥T a)) := isIntegral_algebraMap
        simpa [← IsScalarTower.algebraMap_apply] using this }
  have hTB : T ≤ B := fun z hz => (isIntegral_algebraMap (x := (⟨z, hz⟩ : ↥T)))
  have hyB : Algebra.adjoin R ({y} : Set F) ≤ B := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hy)

  have hxB : IsIntegral ↥B x := by
    refine isIntegral_transfer (Algebra.adjoin R ({y} : Set F)) B
      (RingHom.id F) (RingHom.id F) (fun _ _ h => h) ?_ hx rfl
    intro c hc
    exact ⟨c, hyB hc, rfl⟩

  letI : Algebra ↥T ↥B := (Subalgebra.inclusion hTB).toRingHom.toAlgebra
  haveI : IsScalarTower ↥T ↥B F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral ↥T ↥B := by
    refine ⟨fun b => ?_⟩
    let f : ↥B →ₐ[↥T] F := { (algebraMap ↥B F) with commutes' := fun _ => rfl }
    exact (isIntegral_algHom_iff f Subtype.val_injective).mp b.2
  exact isIntegral_trans (R := ↥T) (A := ↥B) x hxB

section RatLoc

variable (q : ℕ) [hq : Fact q.Prime]

theorem mem_ratLocalizedAt_iff_not_dvd (r : ℚ) : r ∈ GaloisRep.ratLocalizedAt q ↔ ¬ q ∣ r.den := by
  change r.den.Coprime q ↔ _
  rw [Nat.coprime_comm, hq.out.coprime_iff_not_dvd]

theorem mem_ratLocalizedAt_iff_padicValRat (r : ℚ) :
    r ∈ GaloisRep.ratLocalizedAt q ↔ 0 ≤ padicValRat q r := by
  rw [mem_ratLocalizedAt_iff_not_dvd, padicValRat_def]
  by_cases hd : q ∣ r.den
  ·
    have hnum : ¬ (q : ℤ) ∣ r.num := by
      intro h
      have h1 : q ∣ r.num.natAbs := Int.natCast_dvd.mp (by simpa using h)
      have := Nat.dvd_gcd h1 hd
      rw [r.reduced.gcd_eq_one] at this
      exact hq.out.one_lt.ne' (Nat.dvd_one.mp this)
    have h2 : 1 ≤ padicValNat q r.den := one_le_padicValNat_of_dvd r.den_nz hd
    rw [padicValInt.eq_zero_of_not_dvd hnum]
    refine iff_of_false (fun h => h hd) ?_
    intro h0
    have h3 : (1 : ℤ) ≤ (padicValNat q r.den : ℤ) := by exact_mod_cast h2
    simp only [Nat.cast_zero, zero_sub] at h0
    omega
  · rw [padicValNat.eq_zero_of_not_dvd hd]
    simp [hd]

theorem padicValRat_natCast_self : padicValRat q (q : ℚ) = 1 := padicValRat.self hq.out.one_lt

variable {L : Type*} [Field L] (A : ValuationSubring L)

omit hq in

theorem natCast_mem_maximalIdeal (hA : A.LiesOverPrime q) :
    (⟨(q : L), natCast_mem A q⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A :=
  (ValuationSubring.coe_mem_nonunits_iff).mp hA

theorem inv_natCast_notMem [CharZero L] (hA : A.LiesOverPrime q) : ((q : L))⁻¹ ∉ A := by
  intro h
  have hlt := (ValuationSubring.mem_nonunits_iff _).mp hA
  have hle := (A.valuation_le_one_iff _).mpr h
  have hq0 : (q : L) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  rw [map_inv₀, inv_le_one₀ ((Valuation.pos_iff _).mpr hq0)] at hle
  exact absurd hlt (not_lt.mpr hle)

theorem inv_natCast_mem_of_not_dvd (hA : A.LiesOverPrime q) (n : ℕ) (hn : ¬ q ∣ n) : ((n : L))⁻¹ ∈ A := by
  by_contra h

  have hnA : (⟨(n : L), natCast_mem A n⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨u, hu⟩ := hu
    apply h
    have h1 : (((u⁻¹ : (↥A)ˣ) : ↥A) : L) * (n : L) = 1 := by
      have := congrArg (fun z : ↥A => (z : L)) u.inv_mul
      simpa [hu] using this
    have : (((u⁻¹ : (↥A)ˣ) : ↥A) : L) = ((n : L))⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [← this]
    exact ((u⁻¹ : (↥A)ˣ) : ↥A).2
  have hqA := natCast_mem_maximalIdeal q A hA

  have hcop : Nat.Coprime q n := (hq.out.coprime_iff_not_dvd).mpr hn
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have h1 : (1 : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    have : (1 : ↥A) = (a : ↥A) * ⟨(q : L), natCast_mem A q⟩ + (b : ↥A) * ⟨(n : L), natCast_mem A n⟩ := by
      apply Subtype.ext
      simp only [OneMemClass.coe_one, AddMemClass.coe_add, MulMemClass.coe_mul]
      have := congrArg (fun z : ℤ => (z : L)) hab
      push_cast at this
      rw [← this]
      congr 1
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hqA) (Ideal.mul_mem_left _ _ hnA)
  exact (IsLocalRing.maximalIdeal.isMaximal ↥A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem ratCast_mem_of_mem_ratLocalizedAt (hA : A.LiesOverPrime q) (r : ℚ) (hr : r ∈ GaloisRep.ratLocalizedAt q) :
    ((r : L)) ∈ A := by
  rw [mem_ratLocalizedAt_iff_not_dvd] at hr
  rw [Rat.cast_def, div_eq_mul_inv]
  exact mul_mem (intCast_mem A r.num) (inv_natCast_mem_of_not_dvd q A hA r.den hr)

theorem mem_ratLocalizedAt_of_ratCast_mem [CharZero L] (hA : A.LiesOverPrime q) (r : ℚ) (hr : ((r : L)) ∈ A) :
    r ∈ GaloisRep.ratLocalizedAt q := by
  rw [mem_ratLocalizedAt_iff_not_dvd]
  intro hd
  rcases eq_or_ne r 0 with rfl | hr0
  · simp at hd
    exact hq.out.one_lt.ne' hd

  have hnum : ¬ q ∣ r.num.natAbs := by
    intro h1
    have := Nat.dvd_gcd h1 hd
    rw [r.reduced.gcd_eq_one] at this
    exact hq.out.one_lt.ne' (Nat.dvd_one.mp this)
  have hnuminv : ((r.num.natAbs : L))⁻¹ ∈ A := inv_natCast_mem_of_not_dvd q A hA _ hnum
  have hnum0 : r.num ≠ 0 := Rat.num_ne_zero.mpr hr0

  have hden : ((r.den : L))⁻¹ = (r : L) * ((r.num : L))⁻¹ := by
    have h1 : (r : L) = r.num / r.den := Rat.cast_def r
    have hden0 : (r.den : L) ≠ 0 := by exact_mod_cast r.den_nz
    have hnum0' : (r.num : L) ≠ 0 := by exact_mod_cast hnum0
    rw [h1]; field_simp
  have hnuminv' : ((r.num : L))⁻¹ ∈ A := by
    rcases Int.natAbs_eq r.num with h | h
    · rw [h, Int.cast_natCast]; exact hnuminv
    · rw [h, Int.cast_neg, Int.cast_natCast, inv_neg]; exact neg_mem hnuminv
  have hdeninv : ((r.den : L))⁻¹ ∈ A := by
    rw [hden]; exact mul_mem hr hnuminv'

  obtain ⟨d, hdd⟩ := hd
  have hqinv : ((q : L))⁻¹ = (d : L) * ((r.den : L))⁻¹ := by
    have hq0 : (q : L) ≠ 0 := by exact_mod_cast hq.out.ne_zero
    have hd0 : (d : L) ≠ 0 := by
      intro h0
      have : (d : ℕ) = 0 := by exact_mod_cast h0
      apply r.den_nz; rw [hdd, this, mul_zero]
    rw [hdd]; push_cast; field_simp
  exact inv_natCast_notMem q A hA (hqinv ▸ mul_mem (natCast_mem A d) hdeninv)

theorem isUnit_of_padicValRat_eq_zero [CharZero L] (hA : A.LiesOverPrime q) (r : ℚ) (hr : padicValRat q r = 0) (hr0 : r ≠ 0)
    (h : ((r : L)) ∈ A) : IsUnit (⟨(r : L), h⟩ : ↥A) := by
  have hinv : (((r⁻¹ : ℚ) : L)) ∈ A := by
    apply ratCast_mem_of_mem_ratLocalizedAt q A hA
    rw [mem_ratLocalizedAt_iff_padicValRat, padicValRat.inv, hr, neg_zero]
  refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
  simp only [MulMemClass.coe_mul, OneMemClass.coe_one, Rat.cast_inv]
  exact mul_inv_cancel₀ (by exact_mod_cast hr0)

end RatLoc

section StepA

variable (q : ℕ) [hq : Fact q.Prime] (M' : ℕ) [NeZero M']

theorem padicValRat_pow_mul (t : ℕ) (a : ℚ) (ha : a ≠ 0) :
    padicValRat q ((q : ℚ) ^ t * a) = t + padicValRat q a := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  rw [padicValRat.mul (pow_ne_zero _ hq0) ha, padicValRat.pow _, padicValRat_natCast_self, mul_one]

theorem algebraMap_natCast_mem_maximalIdeal
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hmem : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (q : AlgebraicClosure ℚ) ∈ R₀.integers) :
    (⟨_, hmem⟩ : ↥R₀.integers) ∈ IsLocalRing.maximalIdeal ↥R₀.integers := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨u, hu⟩ := hu
  have hq0 : (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (q : AlgebraicClosure ℚ)) ≠ 0 :=
    (map_ne_zero _).mpr (by exact_mod_cast hq.out.ne_zero)
  have h1 : (((u⁻¹ : (↥R₀.integers)ˣ) : ↥R₀.integers) : ↥(modularFunctionFieldBar M')) *
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (q : AlgebraicClosure ℚ) = 1 := by
    have := congrArg (fun z : ↥R₀.integers => (z : ↥(modularFunctionFieldBar M'))) u.inv_mul
    simpa [hu] using this
  have h2 : (((u⁻¹ : (↥R₀.integers)ˣ) : ↥R₀.integers) : ↥(modularFunctionFieldBar M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') ((q : AlgebraicClosure ℚ))⁻¹ := by
    rw [map_inv₀]
    exact eq_inv_of_mul_eq_one_left h1
  have h3 : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') ((q : AlgebraicClosure ℚ))⁻¹ ∈ R₀.integers := by
    rw [← h2]; exact ((u⁻¹ : (↥R₀.integers)ˣ) : ↥R₀.integers).2
  exact inv_natCast_notMem q A hA ((R₀.algebraMap_mem_iff _).mp h3)

theorem coeff_mem_ratLocalizedAt
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
    (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
      ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
    (hcusp : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))) :
    ∀ n : ℤ, g.coeff n ∈ GaloisRep.ratLocalizedAt q := by
  classical

  obtain ⟨c, hc0, hc⟩ :=
    ModularCurve.exists_ne_zero_forall_algebraMap_mul_coeff_mem_of_cuspRegular q M' A hA g hg hcusp
  have hc' : ∀ n, c * g.coeff n ∈ GaloisRep.ratLocalizedAt q := fun n =>
    mem_ratLocalizedAt_of_ratCast_mem q A hA _ (by simpa only [eq_ratCast] using hc n)

  have ht : ∃ t : ℕ, ∀ n, (q : ℚ) ^ t * g.coeff n ∈ GaloisRep.ratLocalizedAt q := by
    refine ⟨(padicValRat q c).toNat, fun n => ?_⟩
    rcases eq_or_ne (g.coeff n) 0 with h0 | h0
    · rw [h0, mul_zero]; exact zero_mem _
    rw [mem_ratLocalizedAt_iff_padicValRat, padicValRat_pow_mul q _ _ h0]
    have h1 := (mem_ratLocalizedAt_iff_padicValRat q _).mp (hc' n)
    rw [padicValRat.mul hc0 h0] at h1
    have h2 : padicValRat q c ≤ ((padicValRat q c).toNat : ℤ) := Int.self_le_toNat _
    omega
  obtain ⟨t, ht⟩ := ht

  set G : ↥(modularFunctionFieldBar M') :=
    ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ with hGdef
  have hQmem : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (q : AlgebraicClosure ℚ) ∈ R₀.integers :=
    (R₀.algebraMap_mem_iff _).mpr (natCast_mem A q)
  have hQmax := algebraMap_natCast_mem_maximalIdeal q M' A hA R₀ hQmem

  suffices H : ∀ s : ℕ, (∀ n, (q : ℚ) ^ s * g.coeff n ∈ GaloisRep.ratLocalizedAt q) →
      ∀ n, g.coeff n ∈ GaloisRep.ratLocalizedAt q from H t ht
  intro s
  induction s with
  | zero => intro h n; simpa using h n
  | succ s ih =>
    intro h
    apply ih
    by_contra hcon
    simp only [not_forall] at hcon
    obtain ⟨n₀, hn₀⟩ := hcon
    have ha0 : g.coeff n₀ ≠ 0 := by
      intro h0; apply hn₀; rw [h0, mul_zero]; exact zero_mem _

    have hv1 : padicValRat q ((q : ℚ) ^ (s + 1) * g.coeff n₀) = 0 := by
      have h1 := (mem_ratLocalizedAt_iff_padicValRat q _).mp (h n₀)
      have h2 : ¬ 0 ≤ padicValRat q ((q : ℚ) ^ s * g.coeff n₀) := fun h' =>
        hn₀ ((mem_ratLocalizedAt_iff_padicValRat q _).mpr h')
      rw [padicValRat_pow_mul q _ _ ha0] at h1 h2 ⊢
      push_cast at h1 ⊢
      omega
    have hu0 : (q : ℚ) ^ (s + 1) * g.coeff n₀ ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hq.out.ne_zero)) ha0

    have hmemA : ∀ n, (((q : ℚ) ^ (s + 1) * g.coeff n : ℚ) : AlgebraicClosure ℚ) ∈ A := fun n =>
      ratCast_mem_of_mem_ratLocalizedAt q A hA _ (h n)
    let y : LaurentSeries ↥A :=
      { coeff := fun n => ⟨(((q : ℚ) ^ (s + 1) * g.coeff n : ℚ) : AlgebraicClosure ℚ), hmemA n⟩
        isPWO_support' := g.isPWO_support'.mono (by
          intro n hn
          rw [Function.mem_support] at hn ⊢
          contrapose! hn
          exact Subtype.ext (by simp [hn])) }
    have hy_coeff : ∀ n, ((y.coeff n : ↥A) : AlgebraicClosure ℚ) =
        (((q : ℚ) ^ (s + 1) * g.coeff n : ℚ) : AlgebraicClosure ℚ) := fun n => rfl

    set C' : ↥(modularFunctionFieldBar M') :=
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') ((q : AlgebraicClosure ℚ) ^ (s + 1)) with hC'def
    have heq : coeffMap A.subtype y = ((C' * G : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) := by
      ext n
      rw [coeffMap_coeff]
      change ((y.coeff n : ↥A) : AlgebraicClosure ℚ) = _
      rw [hy_coeff]
      have : ((C' * G : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) =
          algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((q : AlgebraicClosure ℚ) ^ (s + 1)) *
            coeffEmb (AlgebraicClosure ℚ) g := rfl
      rw [this, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul, coeffEmb_coeff, eq_ratCast]
      push_cast
      ring
    have hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M' := heq ▸ (C' * G).2
    obtain ⟨hint, hres⟩ := hR₀ y hy
    have helt : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) = C' * G := Subtype.ext heq

    have hunit : IsUnit (y.coeff n₀) :=
      isUnit_of_padicValRat_eq_zero q A hA _ hv1 hu0 (hmemA n₀)
    have hres_ne : (R₀.residue ⟨_, hint⟩ : modularFunctionFieldC (ResidueField A) M') ≠ 0 := by
      intro h0
      have h1 : coeffMap (IsLocalRing.residue ↥A) y = 0 := by rw [← hres, h0]; rfl
      have h2 : IsLocalRing.residue ↥A (y.coeff n₀) = 0 := by
        have := congrArg (fun z => HahnSeries.coeff z n₀) h1
        simpa [coeffMap_coeff] using this
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h2
      exact h2 hunit

    have hC'mem : C' ∈ R₀.integers := by
      rw [hC'def, map_pow]; exact pow_mem hQmem _
    have hmax : (⟨_, hint⟩ : ↥R₀.integers) ∈ IsLocalRing.maximalIdeal ↥R₀.integers := by
      have : (⟨_, hint⟩ : ↥R₀.integers) = ⟨C', hC'mem⟩ * ⟨G, hgi⟩ := Subtype.ext helt
      rw [this]
      refine Ideal.mul_mem_right _ _ ?_
      have : (⟨C', hC'mem⟩ : ↥R₀.integers) = ⟨_, hQmem⟩ ^ (s + 1) := by
        apply Subtype.ext
        simp [hC'def, map_pow]
      rw [this]
      exact Ideal.pow_mem_of_mem _ hQmax _ (Nat.succ_pos s)
    have hres0 : R₀.residue ⟨_, hint⟩ = 0 := by
      rw [← RingHom.mem_ker, R₀.ker_residue]; exact hmax
    exact hres_ne hres0

end StepA

section StepB

variable (M' : ℕ) [NeZero M']

theorem coeffEmb_injective (L : Type*) [Field L] [CharZero L] : Function.Injective (coeffEmb L) := by
  intro x y h
  ext k
  have := congrArg (fun z => HahnSeries.coeff z k) h
  simp only [coeffEmb_coeff] at this
  exact (algebraMap ℚ L).injective this

theorem isIntegral_adjoin_jq_of_cuspRegular
    (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
    (hcusp : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))) :
    IsIntegral ↥(Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) g := by
  classical
  set J : ↥(modularFunctionFieldBar M') := ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ with hJdef
  set G : ↥(modularFunctionFieldBar M') :=
    ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ with hGdef

  have htJ : Transcendental (AlgebraicClosure ℚ) J := ModularCurve.transcendental_coeffEmb_jq (AlgebraicClosure ℚ) M'
  haveI : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({J} : Set ↥(modularFunctionFieldBar M')))
      ↥(modularFunctionFieldBar M') :=
    ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_of_neZero M'
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional M'
  have hB1 : IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ) ({J} : Set ↥(modularFunctionFieldBar M'))) G :=
    AlgebraicCurve.isIntegral_adjoin_of_forall_ord_nonneg J htJ G hcusp

  set τ : LaurentSeries ℚ →+* LaurentSeries (AlgebraicClosure ℚ) := coeffEmb (AlgebraicClosure ℚ) with hτ
  set J' : LaurentSeries (AlgebraicClosure ℚ) := coeffEmb (AlgebraicClosure ℚ) jq with hJ'
  set T' : Subalgebra (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
    Algebra.adjoin (AlgebraicClosure ℚ) ({J'} : Set (LaurentSeries (AlgebraicClosure ℚ))) with hT'
  have hB2 : IsIntegral ↥T' (τ g) := by
    refine isIntegral_transfer (Algebra.adjoin (AlgebraicClosure ℚ) ({J} : Set ↥(modularFunctionFieldBar M'))) T'
      (algebraMap ↥(modularFunctionFieldBar M') (LaurentSeries (AlgebraicClosure ℚ))) (RingHom.id _)
      (fun _ _ h => h) ?_ hB1 rfl
    refine forall_exists_of_generator J T' _ _ ⟨J', Algebra.subset_adjoin rfl, rfl⟩ ?_
    intro r
    exact ⟨algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) r, Subalgebra.algebraMap_mem _ _, rfl⟩

  set Rj : Subalgebra ℚ (LaurentSeries ℚ) := Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)) with hRj
  letI algRj : Algebra ↥Rj (LaurentSeries (AlgebraicClosure ℚ)) := (τ.comp (algebraMap ↥Rj (LaurentSeries ℚ))).toAlgebra
  have hcomm : (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp
      (algebraMap ℚ (AlgebraicClosure ℚ)) = τ.comp (algebraMap ℚ (LaurentSeries ℚ)) := Subsingleton.elim _ _
  have hτRj : ∀ r : ↥Rj, (τ.comp (algebraMap ↥Rj (LaurentSeries ℚ))) r ∈ T' := by
    intro r
    obtain ⟨p, hp⟩ : ∃ p : ℚ[X], Polynomial.aeval jq p = (r : LaurentSeries ℚ) := by
      have hr : (r : LaurentSeries ℚ) ∈ Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)) := r.2
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hr
      exact hr
    change τ (r : LaurentSeries ℚ) ∈ T'
    rw [← hp, Polynomial.map_aeval_eq_aeval_map hcomm]
    exact Polynomial.aeval_mem_adjoin_singleton _ _
  letI algRjT : Algebra ↥Rj ↥T' := (RingHom.codRestrict (τ.comp (algebraMap ↥Rj (LaurentSeries ℚ))) T' hτRj).toAlgebra
  haveI : IsScalarTower ↥Rj ↥T' (LaurentSeries (AlgebraicClosure ℚ)) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral ↥Rj ↥T' := ⟨fun x => by
    have hval : ∀ z : LaurentSeries (AlgebraicClosure ℚ), z ∈ T' → IsIntegral ↥Rj z := by
      intro z hz
      refine Algebra.adjoin_induction (p := fun z _ => IsIntegral ↥Rj z) ?_ ?_
        (fun _ _ _ _ h1 h2 => h1.add h2) (fun _ _ _ _ h1 h2 => h1.mul h2) hz
      · intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact isIntegral_algebraMap (x := (⟨jq, Algebra.subset_adjoin rfl⟩ : ↥Rj))
      · intro c
        have hc : IsIntegral ℚ c := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) c).isIntegral
        refine hc.map_of_comp_eq (algebraMap ℚ ↥Rj) (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) ?_
        exact Subsingleton.elim _ _
    let f : ↥T' →ₐ[↥Rj] LaurentSeries (AlgebraicClosure ℚ) :=
      { (algebraMap ↥T' (LaurentSeries (AlgebraicClosure ℚ))) with commutes' := fun _ => rfl }
    exact (isIntegral_algHom_iff f Subtype.val_injective).mp (hval x.1 x.2)⟩
  have hB3 : IsIntegral ↥Rj (τ g) := isIntegral_trans (R := ↥Rj) (A := ↥T') (τ g) hB2

  let τₐ : LaurentSeries ℚ →ₐ[↥Rj] LaurentSeries (AlgebraicClosure ℚ) := { τ with commutes' := fun _ => rfl }
  exact (isIntegral_algHom_iff τₐ (coeffEmb_injective (AlgebraicClosure ℚ))).mp hB3

end StepB

theorem coeffEmb_rat_apply (x : LaurentSeries ℚ) : coeffEmb ℚ x = x := by
  rw [coeffEmb, coeffMap_congr (Subsingleton.elim (algebraMap ℚ ℚ) (RingHom.id ℚ)), coeffMap_id]

theorem natCast_mem_maximalIdeal_ratLocalizedAt (q : ℕ) [hq : Fact q.Prime]
    [IsLocalRing ↥(GaloisRep.ratLocalizedAt q)] :
    ((q : ↥(GaloisRep.ratLocalizedAt q))) ∈ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt q) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  have hmem : (((u⁻¹ : (↥(GaloisRep.ratLocalizedAt q))ˣ) : ↥(GaloisRep.ratLocalizedAt q)) : ℚ) ∈
      GaloisRep.ratLocalizedAt q := ((u⁻¹ : (↥(GaloisRep.ratLocalizedAt q))ˣ) : ↥(GaloisRep.ratLocalizedAt q)).2
  have hval : (((u⁻¹ : (↥(GaloisRep.ratLocalizedAt q))ˣ) : ↥(GaloisRep.ratLocalizedAt q)) : ℚ) = ((q : ℚ))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    have := congrArg (fun z : ↥(GaloisRep.ratLocalizedAt q) => (z : ℚ)) u.inv_mul
    simpa [hu] using this
  rw [hval, mem_ratLocalizedAt_iff_padicValRat, padicValRat.inv, padicValRat_natCast_self] at hmem
  norm_num at hmem

end ModularCurve.ChartMPrimeAux

open ModularCurve.ChartMPrimeAux in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (ℓ' : ℕ) [Fact ℓ'.Prime]
    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hKℓ : Kℓ = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M')))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ]
    (jℓ : ↥Kℓ) (hjℓ : ((jℓ : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (jℓ ≠ 0)]
    (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
    (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
    (hcusp : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
          ↥(modularFunctionFieldBar M')))
    (hgK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g) ∈ Kℓ) :
    (⟨_, hgK⟩ : ↥Kℓ) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ := by
  classical

  have hcoef : ∀ n : ℤ, g.coeff n ∈ GaloisRep.ratLocalizedAt q :=
    coeff_mem_ratLocalizedAt q M' A hA R₀ hR₀ g hg hgi hcusp
  have hgj : IsIntegral ↥(Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) g :=
    isIntegral_adjoin_jq_of_cuspRegular M' g hg hcusp

  haveI : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt q) :=
    GaloisRep.isDiscreteValuationRing_ratLocalizedAt q Fact.out
  haveI : IsFractionRing ↥(GaloisRep.ratLocalizedAt q) ℚ := GaloisRep.isFractionRing_ratLocalizedAt q

  letI algQK₀ : Algebra ℚ ↥(modularFunctionFieldFull M') := SubalgebraClass.toAlgebra (modularFunctionFieldFull M')
  haveI hIST := IsScalarTower.of_algebraMap_eq (R := ↥(GaloisRep.ratLocalizedAt q)) (S := ℚ)
    (A := ↥(modularFunctionFieldFull M')) (fun _ => rfl)
  let j₀ : ↥(modularFunctionFieldFull M') := ⟨jq, jq_mem_full M'⟩
  haveI : Fact (j₀ ≠ 0) := ⟨fun h => jq_ne_zero (congrArg Subtype.val h)⟩
  have hj₀ : ((j₀ : LaurentSeries ℚ)) = coeffEmb ℚ jq := (coeffEmb_rat_apply jq).symm
  have hAq : ((q : ↥(GaloisRep.ratLocalizedAt q))) ∈ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt q) :=
    natCast_mem_maximalIdeal_ratLocalizedAt q
  have hgA : ∀ n : ℤ, ∃ a : ↥(GaloisRep.ratLocalizedAt q),
      algebraMap ↥(GaloisRep.ratLocalizedAt q) ℚ a = algebraMap ℚ ℚ (g.coeff n) :=
    fun n => ⟨⟨g.coeff n, hcoef n⟩, rfl⟩
  have hgK₀ : coeffEmb ℚ g ∈ modularFunctionFieldFull M' := by rw [coeffEmb_rat_apply]; exact hg
  have hW : (⟨coeffEmb ℚ g, hgK₀⟩ : ↥(modularFunctionFieldFull M')) ∈
      AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt q) (↥(modularFunctionFieldFull M')) j₀ :=
    ModularCurve.coeffEmb_mem_chartAlgFin_of_forall_coeff_of_isIntegral_adjoin_jq q M' hqM' ℚ (modularFunctionFieldFull M')
      ↥(GaloisRep.ratLocalizedAt q) hAq j₀ hj₀ g hg hgA hgj hgK₀
  have hW' : IsIntegral ↥(Algebra.adjoin ↥(GaloisRep.ratLocalizedAt q) ({j₀} : Set ↥(modularFunctionFieldFull M')))
      (⟨coeffEmb ℚ g, hgK₀⟩ : ↥(modularFunctionFieldFull M')) :=
    (mem_chartAlg_iff _ _).mp hW

  let φ : LaurentSeries ℚ →+* LaurentSeries ↥k₀ := (qExpand ↥k₀ ℓ').comp (coeffEmb ↥k₀)
  have hφ_apply : ∀ y, φ y = qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ y) := fun _ => rfl
  have hdvd : M' * ℓ' ∣ (q * ℓ') ^ 2 * M' := ⟨q ^ 2 * ℓ', by ring⟩
  have hφK : ∀ y : ↥(modularFunctionFieldFull M'),
      (φ.comp (algebraMap ↥(modularFunctionFieldFull M') (LaurentSeries ℚ))) y ∈ Kℓ := fun y => by
    rw [hKℓ]
    exact ModularCurve.qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
      ↥k₀ M' ℓ' ((q * ℓ') ^ 2 * M') hdvd (ModularCurve.FullLevel.levelH (q * ℓ') M') y y.2
  let ψ : ↥(modularFunctionFieldFull M') →+* ↥Kℓ :=
    RingHom.codRestrict (φ.comp (algebraMap ↥(modularFunctionFieldFull M') (LaurentSeries ℚ))) Kℓ hφK
  have hψ_apply : ∀ y : ↥(modularFunctionFieldFull M'), ((ψ y : ↥Kℓ) : LaurentSeries ↥k₀) = φ (y : LaurentSeries ℚ) :=
    fun _ => rfl

  have hιmem : ∀ r : ↥(GaloisRep.ratLocalizedAt q),
      (((r : ℚ)) : ↥k₀) ∈ A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) := fun r => by
    rw [ValuationSubring.mem_comap, map_ratCast]
    exact ratCast_mem_of_mem_ratLocalizedAt q A hA _ r.2
  let ι : ↥(GaloisRep.ratLocalizedAt q) →+* ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) :=
    RingHom.codRestrict ((Rat.castHom ↥k₀).comp (GaloisRep.ratLocalizedAt q).subtype)
      (A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) hιmem
  have hι_apply : ∀ r : ↥(GaloisRep.ratLocalizedAt q),
      ((ι r : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : ↥k₀) = ((r : ℚ) : ↥k₀) := fun _ => rfl
  let jK : ↥Kℓ := ψ j₀
  have hT : IsIntegral ↥(Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({jK} : Set ↥Kℓ))
      (⟨_, hgK⟩ : ↥Kℓ) := by
    refine isIntegral_transfer
      (Algebra.adjoin ↥(GaloisRep.ratLocalizedAt q) ({j₀} : Set ↥(modularFunctionFieldFull M')))
      (Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({jK} : Set ↥Kℓ))
      ψ (RingHom.id ↥Kℓ) (fun _ _ h => h) ?_ hW' ?_
    · refine forall_exists_of_generator j₀ _ ψ (RingHom.id _) ⟨jK, Algebra.subset_adjoin rfl, rfl⟩ ?_
      intro r
      refine ⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ (ι r), Subalgebra.algebraMap_mem _ _, ?_⟩
      have h1 : ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ (ι r) : ↥Kℓ) : LaurentSeries ↥k₀) =
          HahnSeries.single 0 (((r : ℚ)) : ↥k₀) := by
        rw [IsScalarTower.algebraMap_apply ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ,
          ← algebraMap_laurentSeries_eq_single]
        rfl
      have h2 : ((ψ (algebraMap ↥(GaloisRep.ratLocalizedAt q) ↥(modularFunctionFieldFull M') r) : ↥Kℓ) :
          LaurentSeries ↥k₀) = HahnSeries.single 0 (((r : ℚ)) : ↥k₀) := by
        rw [hψ_apply]
        have : (((algebraMap ↥(GaloisRep.ratLocalizedAt q) ↥(modularFunctionFieldFull M') r) :
            ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ) = algebraMap ℚ (LaurentSeries ℚ) (r : ℚ) := rfl
        rw [this, algebraMap_apply_eq_single, hφ_apply, coeffEmb, coeffMap_single, qExpand_single,
          mul_zero, eq_ratCast]
      exact Subtype.ext (h1.trans h2.symm)
    · apply Subtype.ext
      change qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g) = φ (coeffEmb ℚ g)
      rw [coeffEmb_rat_apply, hφ_apply]

  obtain ⟨hj, hj0, hjK, hmem⟩ :=
    ModularCurve.FullLevel.qExpand_coeffEmb_jq_mem_and_mem_chartAlgFin_laurentBaseChange_xHFunctionField
      q M' ℓ' ↥k₀ Kℓ hKℓ ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))
  have hjeq : (⟨_, hj⟩ : ↥Kℓ) = jℓ := Subtype.ext hjℓ.symm
  have hjKeq : (⟨_, hjK⟩ : ↥Kℓ) = jK := Subtype.ext rfl
  change (⟨_, hjK⟩ : ↥Kℓ) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlg
    ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ {(⟨_, hj⟩ : ↥Kℓ)} at hmem
  rw [hjeq, hjKeq] at hmem
  have hjKint : IsIntegral ↥(Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({jℓ} : Set ↥Kℓ)) jK :=
    (mem_chartAlg_iff _ _).mp hmem

  exact (mem_chartAlg_iff _ _).mpr (isIntegral_adjoin_of_isIntegral_adjoin_of_isIntegral jℓ jK _ hjKint hT)

end S_ModularCurve_FullLevel_qExpand_coeffEmb_mem_chartAlgFin_of_mem_integers_of_cuspRegular_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_qExpand_coeffEmb_mem_chartAlgFin_of_mem_integers_of_cuspRegular_of_not_dvd (solution)
