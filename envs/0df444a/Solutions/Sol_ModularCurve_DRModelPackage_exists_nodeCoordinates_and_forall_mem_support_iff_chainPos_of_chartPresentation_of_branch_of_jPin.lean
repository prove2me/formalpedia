-- Prove2me | solution 1 for ModularCurve.DRModelPackage.exists_nodeCoordinates_and_forall_mem_support_iff_chainPos_of_chartPresentation_of_branch_of_jPin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/a0a5bc58-d1d9-5a59-b25b-d1841f8a84c2

import Mathlib
import Theorems.Thm_ModularCurve_DRModelPackage_mem_nodeIntegers_of_stalk_of_specializes_of_exists_sub_mem
import Theorems.Thm_ModularCurve_DRModelPackage_nodeResidue_eq_zero_iff_and_ord_eq_of_specializes_of_mem_maximalIdeal
import Theorems.Thm_ModularCurve_DRModelPackage_evalAt_eq_stalkClosedPointTo_of_schemeHomOver
import Theorems.Thm_ModularCurve_exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq
import Theorems.Thm_ModularCurve_DRModelPackage_ord_placeOfPoint_stalkMap_eq_one_of_span_eq_maximalIdeal
import Theorems.Thm_ModularCurve_DRModelPackage_nodeResidue_eq_zero_iff_and_ord_eq_of_specializes_of_mem_maximalIdeal_swap
import Theorems.Thm_ModularCurve_DRModelPackage_map_maximalIdeal_stalkMap_baseChangeMap_eq_of_inertia_grain
import Theorems.Thm_ModularCurve_DRModelPackage_compl_jNeLocus_inter_range_comp_eq_singleton
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModelCharts
import Theorems.Thm_ModularCurve_DRModel_exists_ne_and_notMem_chartFin_pFibre
import Theorems.Thm_ModularCurve_ssJSet_nonempty
import Theorems.Thm_ModularCurve_ssJSet_finite
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_DRModelPackage_exists_residueField_point_baseChangeMap_eq_of_isAlgClosed_residueField
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ModularCurve_inertiaField_comap_isDVR_and_residue_surjective_and_place_fixed
import Theorems.Thm_ModularCurve_DRModelPackage_exists_germ_jq_sub_pow_and_stalkSpecializes_mem_maximalIdeal_of_swap
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelLegTwoInput
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_exists_nodeCoordinates_and_forall_mem_support_iff_chainPos_of_chartPresentation_of_branch_of_jPin
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure"
p2m_attr_erase "instance" "continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ValuationSubring.instIsAlgClosedResidueField AlgebraicCurve.GaussReduction.isLocalHom_constToGauss"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong"
p2m_attr_erase "simp" "NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord RegularLocalRingQuotientAscent.dualNumberFst_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one"
p2m_attr_erase "simp" "TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply"
p2m_attr_erase "simp" "ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_integers"
p2m_attr_erase "simp" "AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve~nodeEquiv AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

p2m_open "IsLocalRing ModularCurve.PlaceSpecialization~jFun"

namespace FinJ

theorem mem_chartFinOpenBC_iff (p : ℕ) [Fact p.Prime] [NeZero p] (k : Type) [Field k]
    (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))) :
    y ∈ TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k ↔
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base y ∈ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) := by
  change (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base y ∈ TwoChartIntegralModel.chartFinOpen ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ↔ _
  rw [← TwoChartIntegralModel.TwoChartsAux.U_eq]

theorem compInf_fst_mem_chartFinOpenBC_of_two_cusps (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (hcusps : ∃ y₁ y₂ : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))), y₁ ≠ y₂ ∧
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base y₁ ∉ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) ∧ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base y₂ ∉ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
    (c : ↥(pullback (𝔛.compInf k) (𝔛.compZero k))) :
    (𝔛.compInf k).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base c) ∈
      TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  obtain ⟨xI, hxI⟩ := (ModularCurve.DRModelPackage.compl_jNeLocus_inter_range_comp_eq_singleton p 𝔛 k (𝔛.compInf k) (Or.inl rfl)).2
  obtain ⟨xZ, hxZ⟩ := (ModularCurve.DRModelPackage.compl_jNeLocus_inter_range_comp_eq_singleton p 𝔛 k (𝔛.compZero k) (Or.inr rfl)).2

  have hL : ∀ y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))), y ∉ TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k →
      y = (𝔛.compInf k).base xI.1 ∨ y = (𝔛.compZero k).base xZ.1 := by
    intro y hy
    rcases 𝔛.comp_jointly_surjective k y with h | h
    · left
      have : y ∈ ((TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).Opens) :
          Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k))ᶜ ∩
          Set.range (𝔛.compInf k).base := ⟨hy, h⟩
      rw [hxI] at this
      exact this
    · right
      have : y ∈ ((TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).Opens) :
          Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k))ᶜ ∩
          Set.range (𝔛.compZero k).base := ⟨hy, h⟩
      rw [hxZ] at this
      exact this

  have hne : (𝔛.compInf k).base xI.1 ≠ (𝔛.compZero k).base xZ.1 := by
    obtain ⟨y₁, y₂, h12, h1, h2⟩ := hcusps
    rw [← mem_chartFinOpenBC_iff] at h1 h2
    rcases hL y₁ h1 with rfl | rfl <;> rcases hL y₂ h2 with rfl | rfl
    · exact absurd rfl h12
    · exact h12
    · exact fun e => h12 e.symm
    · exact absurd rfl h12

  by_contra hy
  have h1 : (𝔛.compInf k).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base c) = (𝔛.compInf k).base xI.1 := by
    have : (𝔛.compInf k).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base c) ∈
        ((TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).Opens) :
          Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k))ᶜ ∩
          Set.range (𝔛.compInf k).base := ⟨hy, ⟨_, rfl⟩⟩
    rw [hxI] at this
    exact this
  have h2 : (𝔛.compInf k).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base c) = (𝔛.compZero k).base xZ.1 := by
    have hcond : (𝔛.compInf k).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base c) =
        (𝔛.compZero k).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base c) := by
      rw [← TopCat.comp_app, ← TopCat.comp_app, ← Scheme.Hom.comp_base, ← Scheme.Hom.comp_base, pullback.condition]
    have : (𝔛.compInf k).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base c) ∈
        ((TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).Opens) :
          Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k))ᶜ ∩
          Set.range (𝔛.compZero k).base := ⟨hy, ⟨_, hcond.symm⟩⟩
    rw [hxZ] at this
    exact this
  exact hne (h1.symm.trans h2)

end FinJ

theorem finj_block
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (toκ : O →+* k)
    (𝔛reg : DRResolvedModelPackage p 𝔛 O k toκ)

    (hcusps : ∃ y₁ y₂ : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))), y₁ ≠ y₂ ∧
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base y₁ ∉
        ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) ∧
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base y₂ ∉
        ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
    (n : 𝔛reg.node) :
    ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv n)) ∈
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
        ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h := FinJ.compInf_fst_mem_chartFinOpenBC_of_two_cusps p 𝔛 k hcusps (𝔛reg.nodeEquiv n)
  rw [FinJ.mem_chartFinOpenBC_iff] at h

  change (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base
      (((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ)).base (𝔛reg.nodeEquiv n)) ∈
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)
  have hcomp : (pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ) ≫
      pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
      pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) := by
    simp only [Category.assoc, DRModel.baseChangeMap, pullback.lift_fst, Category.comp_id]
  have key := congrArg (fun g => g.base (𝔛reg.nodeEquiv n)) hcomp
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at key
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h ⊢
  convert h using 2

namespace ChartOkNT
p2m_open "AlgebraicCurve IsLocalRing ModularCurve~nodeEquiv ModularCurve.NodeLocalized ModularCurve.PlaceSpecialization~jFun ModularCurve.PlaceSpecialization.ProlongationTuple"
open Classical

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

local notation "Qb" => AlgebraicClosure ℚ

theorem not_strict_of_reduceFst_mem (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (V : Place Qb ↥(modularFunctionFieldBar (1 * q))) {w : Place k ↥(modularFunctionFieldC k 1)} (hw : w ∈ W) (hV : P.reduceFst V = w) :
    ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V := by
  have hq1 : ¬ q ∣ 1 := fun h => (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h)
  have hφ : ∀ v : Place k ↥(modularFunctionFieldC k 1), frobOnPlacesGeomLevel k 1 data hKr v = arithFrobC q k 1 • v :=
    fun v => (ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr v).symm
  have hfix2 : ∀ v ∈ W, arithFrobC q k 1 • (arithFrobC q k 1 • v) = v := fun v hv =>
    ModularCurve.arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces q 1 hq1 k v ((hW v).mp hv)
  constructor
  · rintro ⟨-, h2⟩
    apply h2
    rw [hφ, hφ, hV]
    exact hfix2 w hw
  · rintro ⟨h1, h2⟩
    apply h2
    rw [hφ] at h1
    rw [hφ, hφ]
    have h3 : arithFrobC q k 1 • P.reduceSnd V = w := h1.symm.trans hV
    have hinj : Function.Injective fun v : Place k ↥(modularFunctionFieldC k 1) => arithFrobC q k 1 • v := MulAction.injective _
    have h4 : P.reduceSnd V = arithFrobC q k 1 • w := hinj (by simp only; rw [h3, hfix2 w hw])
    rw [h3, h4]

theorem divf_eq_neg_over (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    {d₁ d₂ : ℕ} (Q₁ : Fin d₁ → Place Qb ↥(modularFunctionFieldBar (1 * q))) (Q₂ : Fin d₂ → Place Qb ↥(modularFunctionFieldBar (1 * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (E D : Divisor Qb ↥(modularFunctionFieldBar (1 * q))) {w : Place k ↥(modularFunctionFieldC k 1)} (hw : w ∈ W)
    (hEw : ∀ V : Place Qb ↥(modularFunctionFieldBar (1 * q)), P.reduceFst V = w → E V = 0)
    (V : Place Qb ↥(modularFunctionFieldBar (1 * q))) (hV : P.reduceFst V = w) :
    (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - D) V = -(D V) := by
  have hns := not_strict_of_reduceFst_mem P hW V hw hV
  have h1 : (∑ i, Finsupp.single (Q₁ i) (1 : ℤ)) V = 0 := by
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    rintro rfl; exact hns.1 (hQ₁ i)
  have h2 : (∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) V = 0 := by
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finsupp.single_apply, if_neg]
    rintro rfl; exact hns.2 (hQ₂ j)
  rw [Finsupp.sub_apply, Finsupp.sub_apply, Finsupp.add_apply, h1, h2, hEw V hV]
  ring

theorem sum_second_diff (a : ℕ → ℤ) (n : ℕ) :
    ∑ d ∈ Finset.Ico 1 (n + 1), (a (d - 1) - 2 * a d + a (d + 1)) = a 0 - a 1 - a n + a (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ih]
      simp only [Nat.add_sub_cancel]
      ring

end ChartOkNT

namespace ChartBlockAlg

set_option autoImplicit false

theorem valuation_comp_eq_pow {L : Type*} [Field L] (A : ValuationSubring L)
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* L) (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)
    (π : O) (n : ℕ) (w : O) (hw : IsUnit w) :
    A.valuation (ιK (algebraMap O K (π ^ n * w))) = A.valuation (ιK (algebraMap O K π)) ^ n := by
  have hunit : A.valuation (ιK (algebraMap O K w)) = 1 := by
    obtain ⟨wi, hwi⟩ := hw.exists_right_inv
    apply (A.valuation_eq_one_iff ⟨_, hιA w⟩).mp
    refine ⟨⟨⟨_, hιA w⟩, ⟨_, hιA wi⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
    · show ιK (algebraMap O K w) * ιK (algebraMap O K wi) = 1
      rw [← map_mul, ← map_mul, hwi, map_one, map_one]
    · show ιK (algebraMap O K wi) * ιK (algebraMap O K w) = 1
      rw [← map_mul, ← map_mul, mul_comm, hwi, map_one, map_one]
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, hunit, mul_one]

theorem pow_injective_of_lt_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {x : Γ} (h0 : 0 < x) (h1 : x < 1) :
    Function.Injective (fun n : ℕ => x ^ n) := by
  intro m n hmn
  simp only at hmn
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd hmn (ne_of_gt (pow_lt_pow_right_of_lt_one₀ h0 h1 hlt))
  · exact absurd hmn (ne_of_lt (pow_lt_pow_right_of_lt_one₀ h0 h1 hlt))

theorem exists_eq_pow_mul_unit {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) (hπ : IsLocalRing.maximalIdeal O = Ideal.span {π}) (a : O) (ha : a ≠ 0) :
    ∃ (n : ℕ) (w : O), IsUnit w ∧ a = π ^ n * w ∧ IsDiscreteValuationRing.addVal O a = n := by
  have hirr : Irreducible π := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]; exact hπ
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hirr
  exact ⟨n, u, u.isUnit, by rw [hu]; ring, IsDiscreteValuationRing.addVal_def a u hirr n hu⟩

end ChartBlockAlg

namespace ChartBlockAlg

set_option autoImplicit false

theorem addVal_eq_sub_of_mul_eq {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) (hπ : IsLocalRing.maximalIdeal O = Ideal.span {π}) (N d : ℕ) (a b c₀ : O) (hc₀ : IsUnit c₀)
    (hprod : a * b = π ^ N * c₀) (ha : IsDiscreteValuationRing.addVal O a = d) :
    d ≤ N ∧ IsDiscreteValuationRing.addVal O b = ((N - d : ℕ) : ℕ∞) := by
  have hirr : Irreducible π := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]; exact hπ
  have hπ0 : π ≠ 0 := hirr.ne_zero
  have hb0 : b ≠ 0 := by
    intro h0
    have : a * b = 0 := by rw [h0, mul_zero]
    rw [hprod] at this
    exact (mul_ne_zero (pow_ne_zero _ hπ0) hc₀.ne_zero) this
  obtain ⟨m, wV, hwV, hvm, haddm⟩ := exists_eq_pow_mul_unit π hπ b hb0
  have hN : IsDiscreteValuationRing.addVal O (π ^ N * c₀) = (N : ℕ∞) := by
    obtain ⟨wu, hwu⟩ := hc₀
    exact IsDiscreteValuationRing.addVal_def _ wu hirr N (by rw [← hwu]; ring)
  have hsum : ((d + m : ℕ) : ℕ∞) = (N : ℕ∞) := by
    rw [← hN, ← hprod, IsDiscreteValuationRing.addVal_mul, ha, haddm]; norm_cast
  have hsum' : d + m = N := by exact_mod_cast hsum
  refine ⟨by omega, ?_⟩
  rw [haddm]
  congr 1
  omega

end ChartBlockAlg

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
open Classical in

theorem chart_block
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime p)
    (𝔛 : DRModelPackage p)

    [hneη : Nonempty (Scheme.Opens.toScheme
      ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
        ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hMη : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((𝔛.Mη.ffEquiv.symm
          (𝔛.Mη.C.germToFunctionField
            ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
            (((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))).app
                ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
              (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of
                  ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))))
          : ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    (ePl : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ≃ Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p))
    (hePl_fun : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
        (f : ↥(modularFunctionFieldBar (1 * p))) (f' : ↥(modularFunctionFieldBar p)),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = (f' : LaurentSeries (AlgebraicClosure ℚ)) →
        (f ∈ V.toValuationSubring ↔ f' ∈ (ePl V).toValuationSubring) ∧ V.evalAt f = (ePl V).evalAt f')

    {k : Type} [Field k] [CharP k p] [PerfectField k] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ)
    (R : ProlongationTuple P) [DecidableEq k] (hqN : ¬ p ∣ 1)
    (hR : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k 1)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces p 1 k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (e : Place k (modularFunctionFieldC k 1) → ℕ) (he : ∀ w ∈ W, 1 ≤ e w)
    (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)
    (hιK : ∀ o : O, ιK (algebraMap O K o) =
      algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)
        ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) :
          ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))))

    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)
    (toκ : O →+* k)
    (htoκ : ∀ o : O, toκ o = red ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)
      ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) :
        ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), (eO o).2⟩)

    (𝔛reg : DRResolvedModelPackage p 𝔛 O k toκ)
    (σN : ↥W ≃ 𝔛reg.node) (hσN : ∀ w : ↥W, 𝔛reg.width (σN w) = e (w : Place k (modularFunctionFieldC k 1)))
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W) (swap : Bool)

    (hswap : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V = V) →
      ∀ s : Spec (CommRingCat.of O) ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))),
        s ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) = 𝟙 _ →
        Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ s ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
          ((𝔛.Mη.pointEquivPlace).symm (ePl V)).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ →
        (P.IsStrictFst V →
          s.base (IsLocalRing.closedPoint O) ∈ Set.range ((if swap then 𝔛.compZero k else 𝔛.compInf k) ≫ DRModel.baseChangeMap toκ).base ∧
          s.base (IsLocalRing.closedPoint O) ∉ Set.range ((if swap then 𝔛.compInf k else 𝔛.compZero k) ≫ DRModel.baseChangeMap toκ).base) ∧
        (P.IsStrictSnd V →
          s.base (IsLocalRing.closedPoint O) ∈ Set.range ((if swap then 𝔛.compInf k else 𝔛.compZero k) ≫ DRModel.baseChangeMap toκ).base ∧
          s.base (IsLocalRing.closedPoint O) ∉ Set.range ((if swap then 𝔛.compZero k else 𝔛.compInf k) ≫ DRModel.baseChangeMap toκ).base))

    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
          ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤
          ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))) trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K a)))

    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((φ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField
          ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
            ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) :
            ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    (hnodePt : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (hw : P.reduceFst V ∈ W),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V = V) →
      ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
      ∀ s : Spec (CommRingCat.of O) ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))),
        s ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) = 𝟙 _ →
        Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ s ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
          ((𝔛.Mη.pointEquivPlace).symm (ePl V)).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ →
        s.base (IsLocalRing.closedPoint O) =
          (pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨P.reduceFst V, hw⟩)))

    (hxj : ∃ ĵ : O, red ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩ = w.evalAt (jGeomGen k 1) ∧
      ∃ t ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
          ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))),
        φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField t) =
          ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p -
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ)))

    (hspInf : ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)) ⤳ ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))))
    (hspZero : ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)) ⤳ ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))))

    (u v w₀ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))))
    (hw₀ : IsUnit w₀)
    (huv : u * v = ((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))) ^ (𝔛reg.width (σN ⟨w, hw⟩)) * w₀)
    (hmax : Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))), u, v} = IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))))

    (h𝔭inf : Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))), u} =
      Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hspInf).hom (IsLocalRing.maximalIdeal _))
    (h𝔭zero : Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))), v} =
      Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hspZero).hom (IsLocalRing.maximalIdeal _))

    (hchartV : ∀ (t : Spec (CommRingCat.of O) ⟶ 𝔛reg.Y), t ≫ 𝔛reg.toBase = 𝟙 _ →
      ∀ (htx : (t ≫ 𝔛reg.toDR).base (IsLocalRing.closedPoint O) = ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))),
      ∀ d : ℕ,
        IsDiscreteValuationRing.addVal O
          ((Scheme.stalkClosedPointTo (t ≫ 𝔛reg.toDR))
            (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes (specializes_of_eq htx)).hom v)) = d →
        ∀ c : X0MqComponents 𝔛reg.width,
          t.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp c).support ↔
            c = DRResolvedModelPackage.chainPos 𝔛reg.width (σN ⟨w, hw⟩) d)

    (hfin : ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))) ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) :
    ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))), P.reduceFst V = w →
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V = V) →
        ∀ (t : Spec (CommRingCat.of O) ⟶ 𝔛reg.Y), t ≫ 𝔛reg.toBase = 𝟙 _ →
          Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
              (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫
            t ≫ 𝔛reg.toDR ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
            ((𝔛.Mη.pointEquivPlace).symm (ePl V)).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ →
          ∀ d : ℕ, A.valuation (V.evalAt (φ (algebraMap _ ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) (if swap then u else v)))) = A.valuation (((p : ℕ) : AlgebraicClosure ℚ)) ^ d →
            ∀ c : X0MqComponents 𝔛reg.width,
              t.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp c).support ↔
                c = DRResolvedModelPackage.chainPos 𝔛reg.width (σN ⟨w, hw⟩)
                  (if swap then 𝔛reg.width (σN ⟨w, hw⟩) - d else d) := by
  intro V hVw hfix t ht hcomp d hval c
  classical

  have hns : ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V := ChartOkNT.not_strict_of_reduceFst_mem P hW V hw hVw

  have hsec : (t ≫ 𝔛reg.toDR) ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) = 𝟙 _ := by
    rw [Category.assoc, 𝔛reg.toDR_over]; exact ht
  have hcomp' : Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
        (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫
        (t ≫ 𝔛reg.toDR) ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
      ((𝔛.Mη.pointEquivPlace).symm (ePl V)).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ := by
    simpa only [Category.assoc] using hcomp
  have hwW : P.reduceFst V ∈ W := hVw ▸ hw
  have htx : (t ≫ 𝔛reg.toDR).base (IsLocalRing.closedPoint O) = ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))) := by
    have h := hnodePt V hwW hfix hns.1 hns.2 (t ≫ 𝔛reg.toDR) hsec hcomp'
    rw [h]
    congr

  have hιKeq : ιK.comp (algebraMap O K) = (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
      (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)) := by
    ext o; exact hιK o
  have ht' : Spec.map (CommRingCat.ofHom (ιK.comp (algebraMap O K))) ≫ (t ≫ 𝔛reg.toDR) ≫
        pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
      (𝔛.Mη.pointEquivPlace.symm (ePl V)).1 ≫ 𝔛.eη ≫
        pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) := by
    rw [hιKeq]; exact hcomp'

  set sv : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((t ≫ 𝔛reg.toDR).base (IsLocalRing.closedPoint O)) :=
    ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkCongr (.of_eq htx)).inv.hom (if swap then u else v) with hsv
  have hsv' : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkCongr (.of_eq htx)).hom.hom sv = (if swap then u else v) := by
    rw [hsv]
    exact CategoryTheory.Iso.inv_hom_id_apply _ _
  obtain ⟨hmem, hev⟩ := ModularCurve.DRModelPackage.evalAt_eq_stalkClosedPointTo_of_schemeHomOver p hp 𝔛 hMη O hϖO K ιK
    ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))) φ hφO hφj P R ePl hePl_fun V ⟨t ≫ 𝔛reg.toDR, hsec⟩ ht' htx hfin sv
  rw [hsv'] at hev

  set o : O := Scheme.stalkClosedPointTo (t ≫ 𝔛reg.toDR) sv with ho
  have hpO : ιK (algebraMap O K ((p : ℕ) : O)) = ((p : ℕ) : AlgebraicClosure ℚ) := by simp
  have hvp0 : 0 < A.valuation ((p : ℕ) : AlgebraicClosure ℚ) :=
    (Valuation.pos_iff _).mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hvp1 : A.valuation ((p : ℕ) : AlgebraicClosure ℚ) < 1 := by
    have hpA : ((p : ℕ) : AlgebraicClosure ℚ) ∈ A := by
      have : ((p : ℕ) : AlgebraicClosure ℚ) = (((p : ℕ) : A) : AlgebraicClosure ℚ) := by simp
      rw [this]; exact Subtype.mem _
    have hmem : (⟨((p : ℕ) : AlgebraicClosure ℚ), hpA⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
      ValuationSubring.coe_mem_nonunits_iff.mp hA
    exact (A.valuation_lt_one_iff _).mp hmem
  have ho0 : o ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at hev
    rw [hev, map_zero] at hval
    exact (pow_ne_zero d hvp0.ne') hval.symm
  obtain ⟨n, wU, hwU, hon, haddv⟩ := ChartBlockAlg.exists_eq_pow_mul_unit ((p : ℕ) : O) hϖO o ho0
  have hnd : n = d := by
    apply ChartBlockAlg.pow_injective_of_lt_one hvp0 hvp1
    simp only
    rw [← hval, hev, hon, ChartBlockAlg.valuation_comp_eq_pow A ιK hιA _ n wU hwU, hpO]

  have hread : ∀ z, Scheme.stalkClosedPointTo (t ≫ 𝔛reg.toDR)
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes (specializes_of_eq htx)).hom z)
      = Scheme.stalkClosedPointTo (t ≫ 𝔛reg.toDR) (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkCongr (.of_eq htx)).inv.hom z) := by
    intro z; rfl
  cases swap with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hsv ⊢
    apply hchartV t ht htx d _ c
    rw [hread v, ← hsv]
    rw [hnd] at haddv
    exact haddv
  | true =>
    simp only [↓reduceIte] at hsv ⊢

    let ψ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))) →+* O :=
      (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes (specializes_of_eq htx)) ≫ Scheme.stalkClosedPointTo (t ≫ 𝔛reg.toDR)).hom
    have hψ : ∀ z, ψ z = Scheme.stalkClosedPointTo (t ≫ 𝔛reg.toDR)
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes (specializes_of_eq htx)).hom z) := fun z => rfl
    have hprod : ψ u * ψ v = ((p : ℕ) : O) ^ (𝔛reg.width (σN ⟨w, hw⟩)) * ψ w₀ := by
      rw [← map_mul, huv, map_mul, map_pow, map_natCast]
    have hψu : IsDiscreteValuationRing.addVal O (ψ u) = d := by
      rw [hψ u, hread u, ← hsv]
      rw [hnd] at haddv
      exact haddv
    obtain ⟨-, hb⟩ := ChartBlockAlg.addVal_eq_sub_of_mul_eq ((p : ℕ) : O) hϖO _ d (ψ u) (ψ v) (ψ w₀) (hw₀.map ψ) hprod hψu
    apply hchartV t ht htx (𝔛reg.width (σN ⟨w, hw⟩) - d) _ c
    show IsDiscreteValuationRing.addVal O (ψ v) = _
    exact hb

namespace HratBridge

theorem surjective_residue_comp_of_section
    {O : Type} [CommRing O] [IsLocalRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O))
    (t : Spec (CommRingCat.of (ResidueField O)) ⟶ X)
    (ht : t ≫ q = Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))
    (x : X) (hxt : t.base (closedPoint (ResidueField O)) = x) :
    Function.Surjective ((IsLocalRing.residue (X.presheaf.stalk x)).comp
      ((X.presheaf.germ ⊤ x trivial).hom.comp
        (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom))) := by
  subst hxt
  set x := t.base (closedPoint (ResidueField O)) with hxdef

  let τ := Scheme.stalkClosedPointTo t
  haveI : IsLocalHom τ.hom := inferInstance

  let c : CommRingCat.of O ⟶ X.presheaf.stalk x := (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ q.appTop ≫ X.presheaf.germ ⊤ x trivial
  have hc : ∀ o : O, c.hom o = (X.presheaf.germ ⊤ x trivial).hom (q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)) :=
    fun o => rfl

  have hSpec_c : Spec.map c = X.fromSpecStalk x ≫ q := by
    have hq : q = X.toSpecΓ ≫ Spec.map q.appTop ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of O)).inv := by
      rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    conv_rhs => rw [hq]
    rw [← Category.assoc, Scheme.fromSpecStalk_toSpecΓ]
    simp only [c, Spec.map_comp, Category.assoc]

  have hcτ : c ≫ τ = CommRingCat.ofHom (IsLocalRing.residue O) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hSpec_c, ← Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, ht]

  intro ζ
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective ζ
  obtain ⟨o, ho⟩ := Ideal.Quotient.mk_surjective (τ.hom a)
  refine ⟨o, ?_⟩
  change IsLocalRing.residue _ (c.hom o) = IsLocalRing.residue _ a
  have hτ : τ.hom (c.hom o) = τ.hom a := by
    change (c ≫ τ).hom o = _
    rw [hcτ]; exact ho

  apply (Ideal.Quotient.eq).mpr
  rw [IsLocalRing.mem_maximalIdeal]
  intro hu
  have h0 : τ.hom (c.hom o - a) = 0 := by rw [map_sub, hτ, sub_self]
  exact (hu.map τ.hom).ne_zero h0

theorem baseChangeMap_snd (p : ℕ) [Fact p.Prime] {O κ : Type} [CommRing O] [CommRing κ] (r : O →+* κ) :
    DRModel.baseChangeMap (p := p) r ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
      pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) ≫ Spec.map (CommRingCat.ofHom r) := by
  simp only [DRModel.baseChangeMap, pullback.map, pullback.lift_snd]

end HratBridge

theorem hrat_bridge
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (toκ : O →+* k)
    (n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)))
    (s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (IsLocalRing.ResidueField O))))))
    (hs : s ≫ pullback.snd _ _ = 𝟙 _)
    (hx : ((DRModel.baseChangeMap toκ).base ((𝔛.compInf k).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))) = (DRModel.baseChangeMap (IsLocalRing.residue O)).base (s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)))) :
    Function.Surjective ((IsLocalRing.residue ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((DRModel.baseChangeMap toκ).base ((𝔛.compInf k).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))))).comp
      (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ ((DRModel.baseChangeMap toκ).base ((𝔛.compInf k).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))) trivial).hom.comp
        (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom))) := by
  have h1 : DRModel.baseChangeMap (p := p) (IsLocalRing.residue O) ≫
      pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) := by
    simp only [DRModel.baseChangeMap, pullback.map, pullback.lift_snd]
  have ht : (s ≫ DRModel.baseChangeMap (p := p) (IsLocalRing.residue O)) ≫
      pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) := by
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (s ≫ ·) h1).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) hs).trans ?_
    exact Category.id_comp _
  exact HratBridge.surjective_residue_comp_of_section _ (s ≫ DRModel.baseChangeMap (p := p) (IsLocalRing.residue O)) ht _ hx.symm

#print axioms hrat_bridge

set_option maxHeartbeats 24000000 in
set_option synthInstance.maxHeartbeats 1600000 in
open Classical in
theorem assembly
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime p)
    (𝔛 : DRModelPackage p)

    [hneη : Nonempty (Scheme.Opens.toScheme
      ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
        ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hMη : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((𝔛.Mη.ffEquiv.symm
          (𝔛.Mη.C.germToFunctionField
            ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
            (((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))).app
                ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
              (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of
                  ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))))
          : ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    (ePl : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ≃ Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p))
    (hePl_fun : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
        (f : ↥(modularFunctionFieldBar (1 * p))) (f' : ↥(modularFunctionFieldBar p)),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = (f' : LaurentSeries (AlgebraicClosure ℚ)) →
        (f ∈ V.toValuationSubring ↔ f' ∈ (ePl V).toValuationSubring) ∧ V.evalAt f = (ePl V).evalAt f')

    {k : Type} [Field k] [CharP k p] [PerfectField k] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ)
    (R : ProlongationTuple P) [DecidableEq k] (hqN : ¬ p ∣ 1)
    (hR : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k 1)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces p 1 k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (e : Place k (modularFunctionFieldC k 1) → ℕ) (he : ∀ w ∈ W, 1 ≤ e w)
    (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)
    (hιK : ∀ o : O, ιK (algebraMap O K o) =
      algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)
        ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) :
          ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))))

    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)
    (toκ : O →+* k)
    (htoκ : ∀ o : O, toκ o = red ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)
      ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) :
        ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), (eO o).2⟩)

    (𝔛reg : DRResolvedModelPackage p 𝔛 O k toκ)
    (σN : ↥W ≃ 𝔛reg.node) (hσN : ∀ w : ↥W, 𝔛reg.width (σN w) = e (w : Place k (modularFunctionFieldC k 1)))
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W) (swap : Bool)

    (hswap : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V = V) →
      ∀ s : Spec (CommRingCat.of O) ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))),
        s ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) = 𝟙 _ →
        Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ s ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
          ((𝔛.Mη.pointEquivPlace).symm (ePl V)).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ →
        (P.IsStrictFst V →
          s.base (IsLocalRing.closedPoint O) ∈ Set.range ((if swap then 𝔛.compZero k else 𝔛.compInf k) ≫ DRModel.baseChangeMap toκ).base ∧
          s.base (IsLocalRing.closedPoint O) ∉ Set.range ((if swap then 𝔛.compInf k else 𝔛.compZero k) ≫ DRModel.baseChangeMap toκ).base) ∧
        (P.IsStrictSnd V →
          s.base (IsLocalRing.closedPoint O) ∈ Set.range ((if swap then 𝔛.compInf k else 𝔛.compZero k) ≫ DRModel.baseChangeMap toκ).base ∧
          s.base (IsLocalRing.closedPoint O) ∉ Set.range ((if swap then 𝔛.compZero k else 𝔛.compInf k) ≫ DRModel.baseChangeMap toκ).base))

    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
          ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤
          ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))) trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K a)))

    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((φ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField
          ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
            ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) :
            ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    (hnodePt : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (hw : P.reduceFst V ∈ W),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V = V) →
      ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
      ∀ s : Spec (CommRingCat.of O) ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))),
        s ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) = 𝟙 _ →
        Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ s ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
          ((𝔛.Mη.pointEquivPlace).symm (ePl V)).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ →
        s.base (IsLocalRing.closedPoint O) =
          (pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨P.reduceFst V, hw⟩)))

    (hxj : ∃ ĵ : O, red ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩ = w.evalAt (jGeomGen k 1) ∧
      ∃ t ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
          ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))),
        φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField t) =
          ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p -
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ)))

    (hspInf : ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)) ⤳ ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))))
    (hspZero : ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)) ⤳ ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))))

    (u v w₀ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))))
    (hw₀ : IsUnit w₀)
    (huv : u * v = ((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))) ^ (𝔛reg.width (σN ⟨w, hw⟩)) * w₀)
    (hmax : Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))), u, v} = IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))))

    (h𝔭inf : Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))), u} =
      Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hspInf).hom (IsLocalRing.maximalIdeal _))
    (h𝔭zero : Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))), v} =
      Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hspZero).hom (IsLocalRing.maximalIdeal _))

    (hchartV : ∀ (t : Spec (CommRingCat.of O) ⟶ 𝔛reg.Y), t ≫ 𝔛reg.toBase = 𝟙 _ →
      ∀ (htx : (t ≫ 𝔛reg.toDR).base (IsLocalRing.closedPoint O) = ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))),
      ∀ d : ℕ,
        IsDiscreteValuationRing.addVal O
          ((Scheme.stalkClosedPointTo (t ≫ 𝔛reg.toDR))
            (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes (specializes_of_eq htx)).hom v)) = d →
        ∀ c : X0MqComponents 𝔛reg.width,
          t.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp c).support ↔
            c = DRResolvedModelPackage.chainPos 𝔛reg.width (σN ⟨w, hw⟩) d) :

    ∃ (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K₀)
      (c₁ : R.NodeCoordinates K₀ w) (u₀ : ↥(R.nodeIntegersOver K₀ w)),
      IsUnit u₀ ∧
      c₁.x * c₁.y = R.nodeConst K₀ w ((p : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) ^ (𝔛reg.width (σN ⟨w, hw⟩)) * u₀ ∧
      ((φ (algebraMap _ ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) (if swap then v else u)) : ↥(modularFunctionFieldBar (1 * p))) =
        ((c₁.x : ↥(R.nodeIntegersOver K₀ w)) : ↥(modularFunctionFieldBar (1 * p)))) ∧
      ((φ (algebraMap _ ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) (if swap then u else v)) : ↥(modularFunctionFieldBar (1 * p))) =
        ((c₁.y : ↥(R.nodeIntegersOver K₀ w)) : ↥(modularFunctionFieldBar (1 * p)))) ∧
      (∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))), P.reduceFst V = w →
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V = V) →
        ∀ (t : Spec (CommRingCat.of O) ⟶ 𝔛reg.Y), t ≫ 𝔛reg.toBase = 𝟙 _ →
          Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
              (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫
            t ≫ 𝔛reg.toDR ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
            ((𝔛.Mη.pointEquivPlace).symm (ePl V)).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ →
          ∀ d : ℕ, c₁.yDepth V = A.valuation (((p : ℕ) : AlgebraicClosure ℚ)) ^ d →
            ∀ c : X0MqComponents 𝔛reg.width,
              t.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp c).support ↔
                c = DRResolvedModelPackage.chainPos 𝔛reg.width (σN ⟨w, hw⟩)
                  (if swap then 𝔛reg.width (σN ⟨w, hw⟩) - d else d)) := by
  classical

  have hwss : w ∈ ssPlaces p 1 k := (hW w).1 hw
  have hconv : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))),
      φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) s) ∈ R.nodeIntegers w := by
    exact ModularCurve.DRModelPackage.mem_nodeIntegers_of_stalk_of_specializes_of_exists_sub_mem p hp 𝔛 O hϖO K ιK _ φ hφO hφj
      P R hιA toκ (fun o => by rw [htoκ o]; congr 1; exact Subtype.ext (hιK o).symm) hspInf hspZero w (by convert hwss) hxj

  have hmono : ∀ (K K' : IntermediateField ℚ (AlgebraicClosure ℚ)), K ≤ K' →
      NodeLocalized.fieldOver (1 * p) K ≤ NodeLocalized.fieldOver (1 * p) K' := by
    intro K K' hKK'
    refine Subfield.closure_mono (Set.union_subset_union_left _ ?_)
    rintro _ ⟨c, rfl⟩
    exact ⟨⟨c, hKK' c.2⟩, rfl⟩
  have hK1 : ∀ f : ↥(modularFunctionFieldBar (1 * p)), ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K),
      ((f : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (1 * p) K := by
    intro f
    obtain ⟨K, hfd, hf, -⟩ := ModularCurve.exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq A red (red 1) ⟨1, rfl⟩ f
    exact ⟨K, hfd, hf⟩
  let xφ : ↥(modularFunctionFieldBar (1 * p)) := φ (algebraMap _ ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) (if swap then v else u))
  let yφ : ↥(modularFunctionFieldBar (1 * p)) := φ (algebraMap _ ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) (if swap then u else v))
  let uφ : ↥(modularFunctionFieldBar (1 * p)) := φ (algebraMap _ ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) w₀)
  obtain ⟨K₁, hK₁, hx₁⟩ := hK1 xφ
  obtain ⟨K₂, hK₂, hy₂⟩ := hK1 yφ
  obtain ⟨K₃, hK₃, hu₃⟩ := hK1 uφ
  haveI := hK₁; haveI := hK₂; haveI := hK₃
  let K₀ : IntermediateField ℚ (AlgebraicClosure ℚ) := K₁ ⊔ K₂ ⊔ K₃
  haveI hK₀ : FiniteDimensional ℚ K₀ := IntermediateField.finiteDimensional_sup _ _
  have hxK : ((xφ : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (1 * p) K₀ :=
    hmono K₁ K₀ (le_sup_left.trans le_sup_left) hx₁
  have hyK : ((yφ : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (1 * p) K₀ :=
    hmono K₂ K₀ (le_sup_right.trans le_sup_left) hy₂
  have huK : ((uφ : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (1 * p) K₀ :=
    hmono K₃ K₀ le_sup_right hu₃

  have hxI : xφ ∈ R.nodeIntegersOver K₀ w := ⟨hconv _, hxK⟩
  have hyI : yφ ∈ R.nodeIntegersOver K₀ w := ⟨hconv _, hyK⟩
  have huI : uφ ∈ R.nodeIntegersOver K₀ w := ⟨hconv _, huK⟩

  let Φ : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))) →+* ↥(modularFunctionFieldBar (1 * p)) := φ.comp (algebraMap _ ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField))
  have hΦ : ∀ s, Φ s = φ (algebraMap _ ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) s) := fun s => rfl

  have hΦp : Φ ((p : ℕ) : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))))) = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (p : AlgebraicClosure ℚ) := by
    rw [map_natCast, map_natCast]

  let u₀ : ↥(R.nodeIntegersOver K₀ w) := ⟨uφ, huI⟩
  have hu₀ : IsUnit u₀ := by
    obtain ⟨wunit, hwunit⟩ := hw₀
    refine ⟨⟨u₀, ⟨Φ (↑wunit⁻¹ : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))))), hconv _, ?_⟩, ?_, ?_⟩, rfl⟩
    ·
      have hmul : Φ (↑wunit⁻¹ : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))))) * uφ = 1 := by
        show Φ (↑wunit⁻¹ : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))))) * Φ w₀ = 1
        rw [← map_mul, ← hwunit, Units.inv_mul, map_one]
      have hne : (uφ : ↥(modularFunctionFieldBar (1 * p))) ≠ 0 := fun h => by rw [h, mul_zero] at hmul; exact zero_ne_one hmul
      have heq : Φ (↑wunit⁻¹ : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))))) = uφ⁻¹ := eq_inv_of_mul_eq_one_left hmul
      rw [heq]
      have : ((uφ⁻¹ : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
          ((uφ : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ))⁻¹ := by
        simp
      rw [this]
      exact inv_mem huK
    · exact Subtype.ext (by
        show uφ * Φ (↑wunit⁻¹ : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))))) = 1
        show Φ w₀ * Φ (↑wunit⁻¹ : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))))) = 1
        rw [← map_mul, ← hwunit, Units.mul_inv, map_one])
    · exact Subtype.ext (by
        show Φ (↑wunit⁻¹ : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))))) * uφ = 1
        show Φ (↑wunit⁻¹ : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))))) * Φ w₀ = 1
        rw [← map_mul, ← hwunit, Units.inv_mul, map_one])

  have hxy : (xφ : ↥(modularFunctionFieldBar (1 * p))) * yφ =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (p : AlgebraicClosure ℚ) ^ (𝔛reg.width (σN ⟨w, hw⟩)) * uφ := by
    have h1 : (xφ : ↥(modularFunctionFieldBar (1 * p))) * yφ = Φ (u * v) := by
      show Φ (if swap then v else u) * Φ (if swap then u else v) = Φ (u * v)
      rw [← map_mul]
      cases swap
      · rfl
      · simp only [ite_true, mul_comm]
    rw [h1, huv, map_mul, map_pow, hΦp]
    rfl

  have hcusps := ModularCurve.DRModel.exists_ne_and_notMem_chartFin_pFibre p hp k
  have hfinj := finj_block p 𝔛 O hϖO k toκ 𝔛reg hcusps (σN ⟨w, hw⟩)

  have hxFst : ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))) =
      (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))) := rfl
  have hxSnd : ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))) =
      (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))) := by
    show ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k) ≫ DRModel.baseChangeMap toκ).base _ =
      ((pullback.snd (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compZero k) ≫ DRModel.baseChangeMap toκ).base _
    rw [pullback.condition]

  have hPclosed : ∀ m : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)), IsClosed ({m} : Set ↥(pullback (𝔛.compInf k) (𝔛.compZero k))) := by
    haveI : IsClosedImmersion (𝔛.compZero k) := 𝔛.compZero_isClosedImmersion k
    haveI : IsClosedImmersion (𝔛.compInf k) := 𝔛.compInf_isClosedImmersion k
    haveI : IsClosedImmersion (pullback.fst (𝔛.compInf k) (𝔛.compZero k)) := MorphismProperty.pullback_fst _ _ inferInstance
    haveI : JacobsonSpace ↥(𝔛.ratModel k).C := LocallyOfFiniteType.jacobsonSpace (𝔛.ratModel k).toBase
    haveI : JacobsonSpace ↥(pullback (𝔛.compInf k) (𝔛.compZero k)) :=
      LocallyOfFiniteType.jacobsonSpace (pullback.fst (𝔛.compInf k) (𝔛.compZero k))
    have hcard : Nat.card ↥(pullback (𝔛.compInf k) (𝔛.compZero k)) ≠ 0 := by
      rw [𝔛.crossing_card k]
      haveI : Finite ↥(ssJSet p k) := (ModularCurve.ssJSet_finite p k).to_subtype
      haveI : Nonempty ↥(ssJSet p k) := (ModularCurve.ssJSet_nonempty (q := p) (k := k)).to_subtype
      exact Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩
    haveI : Finite ↥(pullback (𝔛.compInf k) (𝔛.compZero k)) := Nat.finite_of_card_ne_zero hcard
    haveI : DiscreteTopology ↥(pullback (𝔛.compInf k) (𝔛.compZero k)) :=
      JacobsonSpace.discreteTopology (Set.toFinite _)
    exact fun m => isClosed_discrete _
  have hyFst : IsClosed ({(pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))} : Set ↥(𝔛.ratModel k).C) := by
    haveI : IsClosedImmersion (𝔛.compZero k) := 𝔛.compZero_isClosedImmersion k
    haveI : IsClosedImmersion (pullback.fst (𝔛.compInf k) (𝔛.compZero k)) := MorphismProperty.pullback_fst _ _ inferInstance
    haveI : JacobsonSpace ↥(𝔛.ratModel k).C := LocallyOfFiniteType.jacobsonSpace (𝔛.ratModel k).toBase
    exact (pullback.fst (𝔛.compInf k) (𝔛.compZero k)).closePoints_subset_preimage_closedPoints (hPclosed _)
  have hySnd : IsClosed ({(pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))} : Set ↥(𝔛.ratModel k).C) := by
    haveI : IsClosedImmersion (𝔛.compInf k) := 𝔛.compInf_isClosedImmersion k
    haveI : IsClosedImmersion (pullback.snd (𝔛.compInf k) (𝔛.compZero k)) := MorphismProperty.pullback_snd _ _ inferInstance
    haveI : JacobsonSpace ↥(𝔛.ratModel k).C := LocallyOfFiniteType.jacobsonSpace (𝔛.ratModel k).toBase
    exact (pullback.snd (𝔛.compInf k) (𝔛.compZero k)).closePoints_subset_preimage_closedPoints (hPclosed _)

  have hunr : Ideal.map ((DRModel.baseChangeMap toκ).stalkMap ((𝔛.compInf k).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))))).hom
        (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
      Ideal.map ((DRModel.baseChangeMap toκ).stalkMap ((𝔛.compZero k).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))))).hom
        (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ := by
    refine ModularCurve.DRModelPackage.map_maximalIdeal_stalkMap_baseChangeMap_eq_of_inertia_grain p hA 𝔛 O eO hϖO toκ htoκ
      (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)) ?_

    haveI : IsAlgClosed (IsLocalRing.ResidueField O) := by
      let ι : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) →+* ↥A :=
        ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp (A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype).codRestrict
          A.toSubring (fun x => x.2)
      let ρ : O →+* IsLocalRing.ResidueField ↥A := ((IsLocalRing.residue ↥A).comp ι).comp eO.toRingHom
      have hρ : Function.Surjective ρ := by
        have h2 := (ModularCurve.inertiaField_comap_isDVR_and_residue_surjective_and_place_fixed p A hA 1).2.2.1
        intro c
        obtain ⟨x, hx⟩ := h2 c
        exact ⟨eO.symm x, by first | simpa [ρ, ι] using hx | (have h_1 := hx; simp [ρ, ι] at h_1; exact h_1) | (have h_1 := hx; simp [ρ, ι] at h_1 ⊢; exact h_1) | exact (hx)⟩
      have hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O :=
        (IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ρ hρ))
      let eres : IsLocalRing.ResidueField O ≃+* IsLocalRing.ResidueField ↥A :=
        (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hρ)
      haveI := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
      exact IsAlgClosed.of_ringEquiv (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField O) eres.symm
    obtain ⟨sO, hsO, hxO⟩ := ModularCurve.DRModelPackage.exists_residueField_point_baseChangeMap_eq_of_isAlgClosed_residueField
      p 𝔛 O hϖO k toκ (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))
    exact hrat_bridge p 𝔛 O k toκ (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)) sO hsO hxO

  have hord := ModularCurve.DRModelPackage.ord_placeOfPoint_stalkMap_eq_one_of_span_eq_maximalIdeal p 𝔛 O k toκ _
    (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)) hyFst hySnd hxFst hxSnd hspInf hspZero u v hmax h𝔭inf h𝔭zero hunr.1 hunr.2

  have htoκ' : ∀ o : O, toκ o = red ⟨ιK (algebraMap O K o), hιA o⟩ := fun o => by
    rw [htoκ o]; congr 1; exact Subtype.ext (hιK o).symm
  have hu𝔭 : u ∈ Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hspInf).hom (IsLocalRing.maximalIdeal _) := by
    rw [← h𝔭inf]; exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hv𝔭 : v ∈ Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hspZero).hom (IsLocalRing.maximalIdeal _) := by
    rw [← h𝔭zero]; exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

  have hclauses : R.nodeResidue₁ w ⟨xφ, hxI.1⟩ = 0 ∧ (arithFrobC p k 1 • w).ord (R.nodeResidue₂ w ⟨xφ, hxI.1⟩) = 1 ∧
      R.nodeResidue₂ w ⟨yφ, hyI.1⟩ = 0 ∧ w.ord (R.nodeResidue₁ w ⟨yφ, hyI.1⟩) = 1 := by
    cases swap with
    | false =>

      obtain ⟨tF, htF, hor⟩ : ∃ tF : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))), Φ tF = ProlongationTuple.jQFun 1 p - ProlongationTuple.jFun 1 p ^ p ∧
          ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hspInf).hom tF ∈ IsLocalRing.maximalIdeal _ := by
        exact (ModularCurve.DRModelPackage.exists_germ_jq_sub_pow_and_stalkSpecializes_mem_maximalIdeal_of_swap
          p hp hA 𝔛 hMη ePl hePl_fun P R hqN hR W hW hreg hval e he hVI O eO hϖO K ιK hιK hιA toκ htoκ 𝔛reg σN hσN w hw false hswap φ hφO hφj hnodePt hxj hspInf hspZero).1 rfl
      have hres := ModularCurve.DRModelPackage.nodeResidue_eq_zero_iff_and_ord_eq_of_specializes_of_mem_maximalIdeal p hp 𝔛 O hϖO K ιK _
        φ hφO hφj P R hιA toκ htoκ' w (by convert hwss) hxj (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)) hyFst hySnd hxFst hxSnd hspInf hspZero tF htF hor hconv
      exact ⟨(hres u).1.2 hu𝔭, (hres u).2.2.2.trans hord.2, (hres v).2.1.2 hv𝔭, (hres v).2.2.1.trans hord.1⟩
    | true =>
      obtain ⟨tF, htF, hor⟩ : ∃ tF : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))), Φ tF = ProlongationTuple.jQFun 1 p - ProlongationTuple.jFun 1 p ^ p ∧
          ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hspZero).hom tF ∈ IsLocalRing.maximalIdeal _ := by
        exact (ModularCurve.DRModelPackage.exists_germ_jq_sub_pow_and_stalkSpecializes_mem_maximalIdeal_of_swap
          p hp hA 𝔛 hMη ePl hePl_fun P R hqN hR W hW hreg hval e he hVI O eO hϖO K ιK hιK hιA toκ htoκ 𝔛reg σN hσN w hw true hswap φ hφO hφj hnodePt hxj hspInf hspZero).2 rfl
      have hres := ModularCurve.DRModelPackage.nodeResidue_eq_zero_iff_and_ord_eq_of_specializes_of_mem_maximalIdeal_swap p hp 𝔛 O hϖO K ιK _
        φ hφO hφj P R hιA toκ htoκ' w (by convert hwss) hxj (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)) hySnd hyFst hxSnd hxFst hspZero hspInf tF htF hor hconv
      exact ⟨(hres v).1.2 hv𝔭, (hres v).2.2.2.trans hord.1, (hres u).2.1.2 hu𝔭, (hres u).2.2.1.trans hord.2⟩
  obtain ⟨hx_fst, hx_snd, hy_snd, hy_fst⟩ := hclauses
  let c₁ : R.NodeCoordinates K₀ w := ⟨⟨xφ, hxI⟩, ⟨yφ, hyI⟩, hx_fst, hx_snd, hy_snd, hy_fst⟩
  refine ⟨K₀, hK₀, c₁, u₀, hu₀, ?_, rfl, rfl, ?_⟩
  ·
    apply Subtype.ext
    show (xφ : ↥(modularFunctionFieldBar (1 * p))) * yφ = ((R.nodeConst K₀ w ((p : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) ^ (𝔛reg.width (σN ⟨w, hw⟩)) * u₀ :
        ↥(R.nodeIntegersOver K₀ w)) : ↥(modularFunctionFieldBar (1 * p)))
    rw [hxy, Subring.coe_mul, SubmonoidClass.coe_pow, ProlongationTuple.coe_nodeConst]
    congr 2
  ·
    exact chart_block p hp hA 𝔛 hMη ePl hePl_fun P R hqN hR W hW hreg hval e he hVI O eO hϖO K ιK hιK hιA toκ htoκ 𝔛reg σN hσN w hw
      swap hswap φ hφO hφj hnodePt hxj hspInf hspZero u v w₀ hw₀ huv hmax h𝔭inf h𝔭zero hchartV hfinj

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
open Classical in

theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime p)
    (𝔛 : DRModelPackage p)

    [hneη : Nonempty (Scheme.Opens.toScheme
      ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
        ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hMη : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((𝔛.Mη.ffEquiv.symm
          (𝔛.Mη.C.germToFunctionField
            ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
            (((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))).app
                ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
              (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of
                  ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))))
          : ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    (ePl : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ≃ Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p))
    (hePl_fun : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
        (f : ↥(modularFunctionFieldBar (1 * p))) (f' : ↥(modularFunctionFieldBar p)),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = (f' : LaurentSeries (AlgebraicClosure ℚ)) →
        (f ∈ V.toValuationSubring ↔ f' ∈ (ePl V).toValuationSubring) ∧ V.evalAt f = (ePl V).evalAt f')

    {k : Type} [Field k] [CharP k p] [PerfectField k] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ)
    (R : ProlongationTuple P) [DecidableEq k] (hqN : ¬ p ∣ 1)
    (hR : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k 1)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces p 1 k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (e : Place k (modularFunctionFieldC k 1) → ℕ) (he : ∀ w ∈ W, 1 ≤ e w)
    (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)
    (hιK : ∀ o : O, ιK (algebraMap O K o) =
      algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)
        ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) :
          ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))))

    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)
    (toκ : O →+* k)
    (htoκ : ∀ o : O, toκ o = red ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)
      ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) :
        ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), (eO o).2⟩)

    (𝔛reg : DRResolvedModelPackage p 𝔛 O k toκ)
    (σN : ↥W ≃ 𝔛reg.node) (hσN : ∀ w : ↥W, 𝔛reg.width (σN w) = e (w : Place k (modularFunctionFieldC k 1)))
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W) (swap : Bool)

    (hswap : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V = V) →
      ∀ s : Spec (CommRingCat.of O) ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))),
        s ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) = 𝟙 _ →
        Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ s ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
          ((𝔛.Mη.pointEquivPlace).symm (ePl V)).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ →
        (P.IsStrictFst V →
          s.base (IsLocalRing.closedPoint O) ∈ Set.range ((if swap then 𝔛.compZero k else 𝔛.compInf k) ≫ DRModel.baseChangeMap toκ).base ∧
          s.base (IsLocalRing.closedPoint O) ∉ Set.range ((if swap then 𝔛.compInf k else 𝔛.compZero k) ≫ DRModel.baseChangeMap toκ).base) ∧
        (P.IsStrictSnd V →
          s.base (IsLocalRing.closedPoint O) ∈ Set.range ((if swap then 𝔛.compInf k else 𝔛.compZero k) ≫ DRModel.baseChangeMap toκ).base ∧
          s.base (IsLocalRing.closedPoint O) ∉ Set.range ((if swap then 𝔛.compZero k else 𝔛.compInf k) ≫ DRModel.baseChangeMap toκ).base))

    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
          ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤
          ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))) trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K a)))

    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((φ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField
          ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
            ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) :
            ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    (hnodePt : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (hw : P.reduceFst V ∈ W),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V = V) →
      ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
      ∀ s : Spec (CommRingCat.of O) ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))),
        s ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) = 𝟙 _ →
        Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ s ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
          ((𝔛.Mη.pointEquivPlace).symm (ePl V)).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ →
        s.base (IsLocalRing.closedPoint O) =
          (pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨P.reduceFst V, hw⟩)))

    (hxj : ∃ ĵ : O, red ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩ = w.evalAt (jGeomGen k 1) ∧
      ∃ t ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
          ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))),
        φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField t) =
          ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p -
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ)))

    (hspInf : ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)) ⤳ ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))))
    (hspZero : ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)) ⤳ ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))))

    (u v w₀ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))))
    (hw₀ : IsUnit w₀)
    (huv : u * v = ((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))) ^ (𝔛reg.width (σN ⟨w, hw⟩)) * w₀)
    (hmax : Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))), u, v} = IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))))

    (h𝔭inf : Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))), u} =
      Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hspInf).hom (IsLocalRing.maximalIdeal _))
    (h𝔭zero : Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))), v} =
      Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hspZero).hom (IsLocalRing.maximalIdeal _))

    (hchartV : ∀ (t : Spec (CommRingCat.of O) ⟶ 𝔛reg.Y), t ≫ 𝔛reg.toBase = 𝟙 _ →
      ∀ (htx : (t ≫ 𝔛reg.toDR).base (IsLocalRing.closedPoint O) = ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))),
      ∀ d : ℕ,
        IsDiscreteValuationRing.addVal O
          ((Scheme.stalkClosedPointTo (t ≫ 𝔛reg.toDR))
            (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes (specializes_of_eq htx)).hom v)) = d →
        ∀ c : X0MqComponents 𝔛reg.width,
          t.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp c).support ↔
            c = DRResolvedModelPackage.chainPos 𝔛reg.width (σN ⟨w, hw⟩) d) :

    ∃ (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K₀)
      (c₁ : R.NodeCoordinates K₀ w) (u₀ : ↥(R.nodeIntegersOver K₀ w)),
      IsUnit u₀ ∧
      c₁.x * c₁.y = R.nodeConst K₀ w ((p : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) ^ (𝔛reg.width (σN ⟨w, hw⟩)) * u₀ ∧
      ((φ (algebraMap _ ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) (if swap then v else u)) : ↥(modularFunctionFieldBar (1 * p))) =
        ((c₁.x : ↥(R.nodeIntegersOver K₀ w)) : ↥(modularFunctionFieldBar (1 * p)))) ∧
      ((φ (algebraMap _ ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) (if swap then u else v)) : ↥(modularFunctionFieldBar (1 * p))) =
        ((c₁.y : ↥(R.nodeIntegersOver K₀ w)) : ↥(modularFunctionFieldBar (1 * p)))) ∧
      (∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))), P.reduceFst V = w →
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V = V) →
        ∀ (t : Spec (CommRingCat.of O) ⟶ 𝔛reg.Y), t ≫ 𝔛reg.toBase = 𝟙 _ →
          Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
              (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫
            t ≫ 𝔛reg.toDR ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
            ((𝔛.Mη.pointEquivPlace).symm (ePl V)).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ →
          ∀ d : ℕ, c₁.yDepth V = A.valuation (((p : ℕ) : AlgebraicClosure ℚ)) ^ d →
            ∀ c : X0MqComponents 𝔛reg.width,
              t.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp c).support ↔
                c = DRResolvedModelPackage.chainPos 𝔛reg.width (σN ⟨w, hw⟩)
                  (if swap then 𝔛reg.width (σN ⟨w, hw⟩) - d else d)) := by
  exact assembly p hp hA 𝔛 hMη ePl hePl_fun P R hqN hR W hW hreg hval e he hVI O eO hϖO K ιK hιK hιA toκ htoκ 𝔛reg σN hσN w hw swap hswap φ hφO hφj hnodePt hxj hspInf hspZero u v w₀ hw₀ huv hmax h𝔭inf h𝔭zero hchartV

end S_ModularCurve_DRModelPackage_exists_nodeCoordinates_and_forall_mem_support_iff_chainPos_of_chartPresentation_of_branch_of_jPin
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_exists_nodeCoordinates_and_forall_mem_support_iff_chainPos_of_chartPresentation_of_branch_of_jPin (solution)
