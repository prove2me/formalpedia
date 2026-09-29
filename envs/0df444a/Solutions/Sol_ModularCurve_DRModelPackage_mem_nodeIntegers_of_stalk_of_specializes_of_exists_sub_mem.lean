-- Prove2me | solution 1 for ModularCurve.DRModelPackage.mem_nodeIntegers_of_stalk_of_specializes_of_exists_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/7aac7497-cdb1-5bc3-9bae-377135886df9

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModelCharts
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_GluedPic0
import Theorems.Thm_ModularCurve_isRational_place_modularFunctionFieldBar
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Theorems.Thm_ModularCurve_DRModelPackage_compl_jNeLocus_inter_range_comp_eq_singleton
import Theorems.Thm_ModularCurve_DRModelPackage_eq_of_forall_exists_comp_baseChangeMap_eq_of_not_mem_jNeLocus
import Theorems.Thm_ModularCurve_DRModelPackage_mem_integers_and_mem_integers_of_stalk_of_specializes
import Theorems.Thm_ModularCurve_DRModelPackage_range_compInf_comp_baseChangeMap_eq_closure_and_isClosed
import Theorems.Thm_ModularCurve_DRModelPackage_range_compZero_comp_baseChangeMap_eq_closure_and_isClosed
import Theorems.Thm_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_iff
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_mem_nodeIntegers_of_stalk_of_specializes_of_exists_sub_mem
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure"
p2m_attr_erase "instance" "continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq"
p2m_attr_erase "simp" "MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord RegularLocalRingQuotientAscent.dualNumberFst_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"
p2m_attr_erase "simp" "WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_DRModelPackage_mem_nodeIntegers_of_stalk_of_specializes_of_exists_sub_mem.ModularCurve IsLocalRing"

namespace LComposite

private noncomputable def _root_.LComposite.comp {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (hv : v.IsRational)
    (A : ValuationSubring K) : ValuationSubring F where
  carrier := {g | ∃ a : K, a ∈ A ∧ v.HasValue g a}
  mul_mem' := by
    rintro g g' ⟨a, ha, hg⟩ ⟨a', ha', hg'⟩
    exact ⟨a * a', mul_mem ha ha', hg.mul hg'⟩
  one_mem' := ⟨1, one_mem _, v.hasValue_one⟩
  add_mem' := by
    rintro g g' ⟨a, ha, ⟨hm, hr⟩⟩ ⟨a', ha', ⟨hm', hr'⟩⟩
    refine ⟨a + a', add_mem ha ha', ⟨add_mem hm hm', ?_⟩⟩
    have : (⟨g + g', add_mem hm hm'⟩ : v.toValuationSubring) = ⟨g, hm⟩ + ⟨g', hm'⟩ := rfl
    rw [this, map_add, hr, hr', map_add]
  zero_mem' := ⟨0, zero_mem _, ⟨zero_mem _, by
    have : (⟨(0 : F), zero_mem _⟩ : v.toValuationSubring) = 0 := rfl
    rw [this, map_zero, map_zero]⟩⟩
  neg_mem' := by
    rintro g ⟨a, ha, ⟨hm, hr⟩⟩
    refine ⟨-a, neg_mem ha, ⟨neg_mem hm, ?_⟩⟩
    have : (⟨-g, neg_mem hm⟩ : v.toValuationSubring) = -⟨g, hm⟩ := rfl
    rw [this, map_neg, hr, map_neg]
  mem_or_inv_mem' := by
    intro g
    by_cases hg : g ∈ v.toValuationSubring
    · obtain ⟨a, ha, -⟩ := v.exists_hasValue_of_surjective hv hg
      by_cases haA : a ∈ A
      · exact Or.inl ⟨a, haA, ha⟩
      · have ha0 : a ≠ 0 := by rintro rfl; exact haA (zero_mem _)
        refine Or.inr ⟨a⁻¹, ?_, ha.inv ha0⟩
        rcases A.mem_or_inv_mem a with h | h
        · exact absurd h haA
        · exact h
    ·
      have hgi : g⁻¹ ∈ v.toValuationSubring := by
        rcases v.toValuationSubring.mem_or_inv_mem g with h | h
        · exact absurd h hg
        · exact h
      refine Or.inr ⟨0, zero_mem _, ⟨hgi, ?_⟩⟩
      rw [map_zero, IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
      exact (ValuationSubring.inv_mem_nonunits_iff _).mpr (Or.inr hg)

p2m_export "LComposite" "comp"
theorem mem_comp {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (hv : v.IsRational)
    (A : ValuationSubring K) (g : F) : g ∈ comp v hv A ↔ ∃ a : K, a ∈ A ∧ v.HasValue g a := Iff.rfl

theorem exists_valuationSubring_mem_iff_hasValue
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k p] (red : ↥A →+* k)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
    {F : Type*} [Field F] (φ : F →+* ↥(modularFunctionFieldBar (1 * p))) :
    ∃ B' : ValuationSubring F,
      (∀ f : F, f ∈ B' ↔ φ f ∈ V.toValuationSubring ∧ ∃ a : AlgebraicClosure ℚ, a ∈ A ∧ V.HasValue (φ f) a) ∧
      (∀ (c : AlgebraicClosure ℚ), c ∈ A → ∀ f : F,
        φ f = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) c → f ∈ B') ∧
      ((p : F) ∈ B' ∧ ((p : F))⁻¹ ∉ B') := by
  haveI : NeZero (1 * p) := ⟨by rw [one_mul]; exact (Fact.out : p.Prime).ne_zero⟩
  have hV : V.IsRational := ModularCurve.isRational_place_modularFunctionFieldBar (1 * p) V
  refine ⟨(comp V hV A).comap φ, fun f => ?_, fun c hc f hf => ?_, ?_, ?_⟩
  · rw [ValuationSubring.mem_comap, mem_comp]
    exact ⟨fun ⟨a, ha, h⟩ => ⟨h.mem, a, ha, h⟩, fun ⟨_, a, ha, h⟩ => ⟨a, ha, h⟩⟩
  · rw [ValuationSubring.mem_comap, mem_comp, hf]
    exact ⟨c, hc, V.hasValue_algebraMap c⟩
  · rw [ValuationSubring.mem_comap, mem_comp, map_natCast]
    refine ⟨(p : AlgebraicClosure ℚ), ?_, ?_⟩
    · have : ((p : ℕ) : AlgebraicClosure ℚ) = ((p : ℕ) : ↥A) := by simp
      rw [this]; exact Subtype.mem _
    · have := V.hasValue_algebraMap ((p : ℕ) : AlgebraicClosure ℚ)
      rwa [map_natCast] at this
  · rw [ValuationSubring.mem_comap, mem_comp, map_inv₀, map_natCast]
    rintro ⟨b, hb, hval⟩

    have hp0 : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    have hval' : V.HasValue ((p : ↥(modularFunctionFieldBar (1 * p))))⁻¹ (((p : ℕ) : AlgebraicClosure ℚ))⁻¹ := by
      have := (V.hasValue_algebraMap ((p : ℕ) : AlgebraicClosure ℚ)).inv hp0
      rwa [map_natCast] at this
    have hb' : b = (((p : ℕ) : AlgebraicClosure ℚ))⁻¹ := hval.unique hval'
    subst hb'

    have hpA : ((p : ℕ) : AlgebraicClosure ℚ) ∈ A := by
      have : ((p : ℕ) : AlgebraicClosure ℚ) = ((p : ℕ) : ↥A) := by simp
      rw [this]; exact Subtype.mem _
    have hu : IsUnit ((p : ℕ) : ↥A) := by
      refine ⟨⟨(p : ↥A), ⟨_, hb⟩, ?_, ?_⟩, rfl⟩
      · apply Subtype.ext; show ((p : ℕ) : ↥A).1 * ((p : ℕ) : AlgebraicClosure ℚ)⁻¹ = 1
        rw [show ((p : ℕ) : ↥A).1 = ((p : ℕ) : AlgebraicClosure ℚ) by simp, mul_inv_cancel₀ hp0]
      · apply Subtype.ext; show ((p : ℕ) : AlgebraicClosure ℚ)⁻¹ * ((p : ℕ) : ↥A).1 = 1
        rw [show ((p : ℕ) : ↥A).1 = ((p : ℕ) : AlgebraicClosure ℚ) by simp, inv_mul_cancel₀ hp0]
    have := hu.map red
    rw [map_natCast, CharP.cast_eq_zero] at this
    exact not_isUnit_zero this

end LComposite

section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_mem_nodeIntegers_of_stalk_of_specializes_of_exists_sub_mem.AlgebraicGeometry IsLocalRing"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp Spec.map_preimage IsProper Scheme.toSpecΓ_naturality_assoc Spec.preimage_map Scheme.Hom Scheme.Pullback.range_map IsProper.eq_valuativeCriterion Scheme.SpecMap_stalkSpecializes_fromSpecStalk StructureSheaf.stalkAlgebra ValuativeCommSq Scheme.fromSpecStalk_toSpecΓ Spec IsIntegral Scheme.Opens.toScheme Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Scheme.mem_basicOpen'' Scheme.stalkClosedPointTo Scheme.Hom.comp_appTop Spec.map_injective Spec.preimage Scheme.Spec_stalkClosedPointTo_fromSpecStalk Spec.structureSheaf toSpecΓ_SpecMap_ΓSpecIso_inv StructureSheaf.IsLocalization.to_stalk Scheme.Opens ValuativeCriterion.Existence ValuativeCriterion Scheme.Hom.comp_preimage Scheme.ΓSpecIso" end AlgebraicGeometry
p2m_open_scoped "AlgebraicGeometry" in

theorem AlgebraicGeometry.exists_forall_algebraMap_functionField_mem_of_isProper
    {O : Type} [CommRing O] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of O)) [IsProper f] [IsIntegral X]
    (B : ValuationSubring X.functionField)
    (hB : ∀ a : O, (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ f)).hom a ∈ B) :
    ∃ x : X, (∀ g : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField g ∈ B) ∧
      (∀ g : X.presheaf.stalk x, g ∈ maximalIdeal (X.presheaf.stalk x) →
        algebraMap (X.presheaf.stalk x) X.functionField g ∈ B.nonunits) := by
  classical

  set ξ := genericPoint X with hξ
  let i₁ : Spec X.functionField ⟶ X := X.fromSpecStalk ξ
  let ψ : O →+* X.functionField := (Spec.preimage (i₁ ≫ f)).hom
  let ψ' : O →+* B := ψ.codRestrict B.toSubring hB
  have hw : i₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B X.functionField)) ≫ Spec.map (CommRingCat.ofHom ψ') := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (algebraMap (↥B) ↑X.functionField).comp ψ' = ψ := RingHom.ext fun _ => rfl
    rw [this]
    show i₁ ≫ f = Spec.map (CommRingCat.ofHom (Spec.preimage (i₁ ≫ f)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hsq : CommSq i₁ (Spec.map (CommRingCat.ofHom (algebraMap B X.functionField))) f
      (Spec.map (CommRingCat.ofHom ψ')) := ⟨hw⟩
  have hex : ValuativeCriterion.Existence f :=
    (IsProper.eq_valuativeCriterion ▸ (inferInstance : IsProper f)).1.1.1.existence
  let S : ValuativeCommSq f :=
    { R := B, K := X.functionField, i₁ := i₁, i₂ := Spec.map (CommRingCat.ofHom ψ'), commSq := hsq }
  haveI : S.commSq.HasLift := hex S
  let ℓ := S.commSq.lift
  have hℓ : Spec.map (CommRingCat.ofHom (algebraMap B X.functionField)) ≫ ℓ = i₁ := S.commSq.fac_left

  let x : X := ℓ.base (closedPoint B)
  let θ := Scheme.stalkClosedPointTo ℓ
  have hθℓ : Spec.map θ ≫ X.fromSpecStalk x = ℓ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ℓ

  have hspec : ξ ⤳ x := (genericPoint_spec X).specializes trivial
  have key : θ ≫ CommRingCat.ofHom (algebraMap B X.functionField) = X.presheaf.stalkSpecializes hspec := by
    have h1 : Spec.map (θ ≫ CommRingCat.ofHom (algebraMap B X.functionField)) ≫ X.fromSpecStalk x =
        Spec.map (X.presheaf.stalkSpecializes hspec) ≫ X.fromSpecStalk x := by
      rw [Spec.map_comp, Category.assoc, hθℓ, hℓ, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Spec.map_injective ((cancel_mono (X.fromSpecStalk x)).mp h1)
  have key' : ∀ g : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField g = (θ.hom g : X.functionField) := by
    intro g
    have := congrArg (fun φ => φ.hom g) key
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at this
    change (X.presheaf.stalkSpecializes hspec).hom g = ((θ.hom g : B) : X.functionField)
    rw [← this]
    rfl
  refine ⟨x, fun g => ?_, fun g hg => ?_⟩
  · rw [key']; exact (θ.hom g).2
  · rw [key', ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hg
    exact fun hu => hg (isUnit_of_map_unit θ.hom g hu)

p2m_open_scoped "AlgebraicGeometry" in

theorem AlgebraicGeometry.Spec_preimage_fromSpecStalk_comp_apply
    {O : Type} [CommRing O] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of O)) [IsIntegral X] (x : X) (a : O) :
    (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ f)).hom a =
      algebraMap (X.presheaf.stalk x) X.functionField
        ((X.presheaf.germ ⊤ x trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a))) := by
  have h : X.fromSpecStalk (genericPoint X) ≫ f =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial) := by
    rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ]
    simp only [Category.assoc]
    rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [h, Spec.preimage_map]
  have e : X.presheaf.germ ⊤ x trivial ≫ X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ x)) =
      X.presheaf.germ ⊤ (genericPoint X) trivial := X.presheaf.germ_stalkSpecializes _ _
  rw [← e]
  rfl

end

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_mem_nodeIntegers_of_stalk_of_specializes_of_exists_sub_mem.AlgebraicGeometry AlgebraicCurve"

namespace RmConv

universe u
variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
  (S : Type u) [CommRing S] [Algebra R S]

open _root_.AlgebraicCurve.TwoChartIntegralModel in

theorem mem_chartFinOpenBC_and_not_isUnit_germ_of_not_mem_jNeLocus (c : S) (y : ↥(baseChange R F j S))
    (hy : y ∉ jNeLocus R F j S c) :
    ∃ hyF : y ∈ chartFinOpenBC R F j S,
      ¬ IsUnit ((baseChange R F j S).presheaf.germ (chartFinOpenBC R F j S) y hyF
        (jCoordBC R F j S - ((baseChange R F j S).presheaf.map (homOfLE (le_top : chartFinOpenBC R F j S ≤ ⊤)).op).hom
          (constSection R F j S c))) := by
  classical
  have hy' := hy
  rw [jNeLocus] at hy'
  simp only [TopologicalSpace.Opens.mem_sup, not_or] at hy'
  obtain ⟨hy₁, hy₂⟩ := hy'

  have hcov : y ∈ chartFinOpenBC R F j S ⊔ chartInfOpenBC R F j S := by
    rw [chartFinOpenBC_sup_chartInfOpenBC]; trivial
  rw [TopologicalSpace.Opens.mem_sup] at hcov
  have hyF : y ∈ chartFinOpenBC R F j S := by
    by_contra hnot
    have hyI : y ∈ chartInfOpenBC R F j S := hcov.resolve_left hnot

    apply hy₂
    rw [Scheme.mem_basicOpen'']
    refine ⟨hyI, ?_⟩
    have hninv : ¬ IsUnit ((baseChange R F j S).presheaf.germ (chartInfOpenBC R F j S) y hyI (jInvCoordBC R F j S)) := by
      intro hu
      apply hnot
      have : y ∈ (baseChange R F j S).basicOpen (jInvCoordBC R F j S) := (Scheme.mem_basicOpen'' _ _ _).mpr ⟨hyI, hu⟩
      rw [← chartFinOpenBC_inf_chartInfOpenBC_eq_basicOpen_jInvCoordBC] at this
      exact this.1
    haveI : IsLocalRing ((baseChange R F j S).presheaf.stalk y) := inferInstance
    have hmem : (baseChange R F j S).presheaf.germ (chartInfOpenBC R F j S) y hyI (jInvCoordBC R F j S) ∈
        IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).mpr hninv
    rw [map_sub, map_one, map_mul]

    have hm : (baseChange R F j S).presheaf.germ (chartInfOpenBC R F j S) y hyI
        (((baseChange R F j S).presheaf.map (homOfLE (le_top : chartInfOpenBC R F j S ≤ ⊤)).op).hom (constSection R F j S c)) *
        (baseChange R F j S).presheaf.germ (chartInfOpenBC R F j S) y hyI (jInvCoordBC R F j S) ∈ IsLocalRing.maximalIdeal _ :=
      Ideal.mul_mem_left _ _ hmem
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ((IsLocalRing.mem_maximalIdeal _).mp hm)
  refine ⟨hyF, ?_⟩
  intro hu
  exact hy₁ ((Scheme.mem_basicOpen'' _ _ _).mpr ⟨hyF, hu⟩)

open _root_.AlgebraicCurve.TwoChartIntegralModel in

theorem not_mem_jNeLocus_of_not_isUnit_germ (c : S) (y : ↥(baseChange R F j S)) (hyF : y ∈ chartFinOpenBC R F j S)
    (h : ¬ IsUnit ((baseChange R F j S).presheaf.germ (chartFinOpenBC R F j S) y hyF
        (jCoordBC R F j S - ((baseChange R F j S).presheaf.map (homOfLE (le_top : chartFinOpenBC R F j S ≤ ⊤)).op).hom
          (constSection R F j S c)))) :
    y ∉ jNeLocus R F j S c := by
  classical
  intro hy
  rw [jNeLocus, TopologicalSpace.Opens.mem_sup] at hy
  rcases hy with hy | hy
  · rw [Scheme.mem_basicOpen''] at hy
    obtain ⟨m, hm⟩ := hy
    exact h hm
  · rw [Scheme.mem_basicOpen''] at hy
    obtain ⟨hyI, hu⟩ := hy
    have hyW : y ∈ chartFinOpenBC R F j S ⊓ chartInfOpenBC R F j S := ⟨hyF, hyI⟩

    have hprod : (baseChange R F j S).presheaf.germ (chartFinOpenBC R F j S) y hyF (jCoordBC R F j S) *
        (baseChange R F j S).presheaf.germ (chartInfOpenBC R F j S) y hyI (jInvCoordBC R F j S) = 1 := by
      have e := congrArg ((baseChange R F j S).presheaf.germ _ y hyW).hom (res_jCoordBC_mul_res_jInvCoordBC R F j S)
      rw [map_mul, map_one, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at e
      exact e

    rw [map_sub, TopCat.Presheaf.germ_res_apply] at h
    rw [map_sub, map_one, map_mul, TopCat.Presheaf.germ_res_apply] at hu
    apply h

    have key : (baseChange R F j S).presheaf.germ (chartInfOpenBC R F j S) y hyI (jInvCoordBC R F j S) *
        ((baseChange R F j S).presheaf.germ (chartFinOpenBC R F j S) y hyF (jCoordBC R F j S) -
          (baseChange R F j S).presheaf.germ ⊤ y trivial (constSection R F j S c)) =
        1 - (baseChange R F j S).presheaf.germ ⊤ y trivial (constSection R F j S c) *
          (baseChange R F j S).presheaf.germ (chartInfOpenBC R F j S) y hyI (jInvCoordBC R F j S) := by
      rw [mul_sub, mul_comm, hprod]
      ring
    have hk : IsUnit ((baseChange R F j S).presheaf.germ (chartInfOpenBC R F j S) y hyI (jInvCoordBC R F j S) *
        ((baseChange R F j S).presheaf.germ (chartFinOpenBC R F j S) y hyF (jCoordBC R F j S) -
          (baseChange R F j S).presheaf.germ ⊤ y trivial (constSection R F j S c))) := by
      rw [key]; exact hu
    exact isUnit_of_mul_isUnit_right hk

open _root_.AlgebraicCurve.TwoChartIntegralModel in

theorem not_isUnit_germ_jInvCoordBC_and_mul_eq_one [IsIntegral (baseChange R F j S)]
    (y : ↥(baseChange R F j S)) (hyI : y ∈ chartInfOpenBC R F j S) (hyF : y ∉ chartFinOpenBC R F j S)
    (x : ↥(baseChange R F j S)) (hxF : x ∈ chartFinOpenBC R F j S) :
    ¬ IsUnit ((baseChange R F j S).presheaf.germ (chartInfOpenBC R F j S) y hyI (jInvCoordBC R F j S)) ∧
    algebraMap ((baseChange R F j S).presheaf.stalk y) (baseChange R F j S).functionField
        ((baseChange R F j S).presheaf.germ (chartInfOpenBC R F j S) y hyI (jInvCoordBC R F j S)) *
      algebraMap ((baseChange R F j S).presheaf.stalk x) (baseChange R F j S).functionField
        ((baseChange R F j S).presheaf.germ (chartFinOpenBC R F j S) x hxF (jCoordBC R F j S)) = 1 := by
  classical
  constructor
  · intro hu
    apply hyF
    have : y ∈ (baseChange R F j S).basicOpen (jInvCoordBC R F j S) := (Scheme.mem_basicOpen'' _ _ _).mpr ⟨hyI, hu⟩
    rw [← chartFinOpenBC_inf_chartInfOpenBC_eq_basicOpen_jInvCoordBC] at this
    exact this.1
  ·
    have hξI : genericPoint ↥(baseChange R F j S) ∈ chartInfOpenBC R F j S :=
      ((genericPoint_spec ↥(baseChange R F j S)).mem_open_set_iff (chartInfOpenBC R F j S).isOpen).mpr ⟨y, trivial, hyI⟩
    have hξF : genericPoint ↥(baseChange R F j S) ∈ chartFinOpenBC R F j S :=
      ((genericPoint_spec ↥(baseChange R F j S)).mem_open_set_iff (chartFinOpenBC R F j S).isOpen).mpr ⟨x, trivial, hxF⟩
    have h1 : algebraMap ((baseChange R F j S).presheaf.stalk y) (baseChange R F j S).functionField
        ((baseChange R F j S).presheaf.germ (chartInfOpenBC R F j S) y hyI (jInvCoordBC R F j S)) =
        (baseChange R F j S).presheaf.germ (chartInfOpenBC R F j S) (genericPoint _) hξI (jInvCoordBC R F j S) := by
      show ((baseChange R F j S).presheaf.stalkSpecializes _).hom _ = _
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    have h2 : algebraMap ((baseChange R F j S).presheaf.stalk x) (baseChange R F j S).functionField
        ((baseChange R F j S).presheaf.germ (chartFinOpenBC R F j S) x hxF (jCoordBC R F j S)) =
        (baseChange R F j S).presheaf.germ (chartFinOpenBC R F j S) (genericPoint _) hξF (jCoordBC R F j S) := by
      show ((baseChange R F j S).presheaf.stalkSpecializes _).hom _ = _
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    rw [h1, h2]
    have e := congrArg ((baseChange R F j S).presheaf.germ _ (genericPoint _) (show genericPoint ↥(baseChange R F j S) ∈ chartFinOpenBC R F j S ⊓ chartInfOpenBC R F j S from ⟨hξF, hξI⟩)).hom (res_jCoordBC_mul_res_jInvCoordBC R F j S)
    rw [map_mul, map_one, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at e
    rw [mul_comm]
    exact e

end RmConv

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_mem_nodeIntegers_of_stalk_of_specializes_of_exists_sub_mem.AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRModelPackage_mem_nodeIntegers_of_stalk_of_specializes_of_exists_sub_mem.ModularCurve AlgebraicCurve"

namespace RmConv

theorem phi_algebraMap_germ_jCoordBC
    (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+* ↥(modularFunctionFieldBar (1 * p)))
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
    (hx : x ∈ TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) :
    haveI : NeZero (1 * p) := ⟨by rw [one_mul]; exact (Fact.out : p.Prime).ne_zero⟩
    φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ
          (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) x hx).hom
          (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O))) =
      ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p := by
  haveI : NeZero (1 * p) := ⟨by rw [one_mul]; exact (Fact.out : p.Prime).ne_zero⟩

  have hle : TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O ≤ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) :=
    fun y hy => TwoChartIntegralModel.chartFinOpen_le_image_top ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) hy
  have hxU : x ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) := hle hx

  have hj : TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O =
      ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.map (homOfLE hle).op).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
        (TwoChartIntegralModel.TwoChartsAux.f ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) := by
    rw [TwoChartIntegralModel.jCoordBC, TwoChartIntegralModel.jCoord]
    unfold TwoChartIntegralModel.baseChangeι
    have hnat := congrArg (fun ψ => ψ.hom (TwoChartIntegralModel.TwoChartsAux.f ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
      ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).naturality
        (homOfLE (TwoChartIntegralModel.chartFinOpen_le_image_top ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))).op)
    simp only [CommRingCat.comp_apply] at hnat
    refine Eq.trans ?_ (hnat.trans ?_)
    · rfl
    · exact congrArg (fun i => ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.map i).hom _) (Subsingleton.elim _ _)
  have hgerm : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) x hx).hom
        (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) =
      ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) x hxU).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
        (TwoChartIntegralModel.TwoChartsAux.f ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) := by
    rw [hj]
    exact TopCat.Presheaf.germ_res_apply _ (homOfLE hle) x hx _
  rw [hgerm]

  have halg : algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) x hxU).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
          (TwoChartIntegralModel.TwoChartsAux.f ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))) =
      (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
          (TwoChartIntegralModel.TwoChartsAux.f ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) := by
    show ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes _).hom _ = _
    exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
  rw [halg]
  apply Subtype.ext
  have h := hφj (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))
  rw [TwoChartIntegralModel.TwoChartsAux.f, TwoChartIntegralModel.TwoChartsAux.sF] at *
  rw [h]
  rfl

end RmConv

p2m_open "CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_mem_nodeIntegers_of_stalk_of_specializes_of_exists_sub_mem.AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel ModularCurve P2MW.S_ModularCurve_DRModelPackage_mem_nodeIntegers_of_stalk_of_specializes_of_exists_sub_mem.ModularCurve"

namespace RmConv

noncomputable abbrev bcMap (p : ℕ) [Fact p.Prime] (O κ : Type) [CommRing O] [CommRing κ] (toκ : O →+* κ) :
    (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ) ⟶ (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) :=
  DRModel.baseChangeMap (p := p) toκ

theorem bcMap_baseChangeι (p : ℕ) [Fact p.Prime] (O κ : Type) [CommRing O] [CommRing κ] (toκ : O →+* κ) :
    bcMap p O κ toκ ≫ TwoChartIntegralModel.baseChangeι ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O = TwoChartIntegralModel.baseChangeι ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ := by
  show DRModel.baseChangeMap (p := p) toκ ≫ pullback.fst _ _ = pullback.fst _ _
  rw [DRModel.baseChangeMap, pullback.lift_fst, Category.comp_id]

theorem bcMap_baseChangeToBase (p : ℕ) [Fact p.Prime] (O κ : Type) [CommRing O] [CommRing κ] (toκ : O →+* κ) :
    bcMap p O κ toκ ≫ TwoChartIntegralModel.baseChangeToBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O =
      TwoChartIntegralModel.baseChangeToBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ ≫ Spec.map (CommRingCat.ofHom toκ) := by
  show DRModel.baseChangeMap (p := p) toκ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ _
  rw [DRModel.baseChangeMap, pullback.lift_snd]

theorem preimage_chartFinOpenBC (p : ℕ) [Fact p.Prime] (O κ : Type) [CommRing O] [CommRing κ] (toκ : O →+* κ) :
    bcMap p O κ toκ ⁻¹ᵁ TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O = TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ := by
  show bcMap p O κ toκ ⁻¹ᵁ (TwoChartIntegralModel.baseChangeι ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O ⁻¹ᵁ _) = TwoChartIntegralModel.baseChangeι ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ ⁻¹ᵁ _
  rw [← Scheme.Hom.comp_preimage, bcMap_baseChangeι]

theorem mem_chartFinOpenBC_iff (p : ℕ) [Fact p.Prime] (O κ : Type) [CommRing O] [CommRing κ] (toκ : O →+* κ) (y : ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ)) :
    (bcMap p O κ toκ).base y ∈ TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O ↔
      y ∈ TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ := by
  rw [← preimage_chartFinOpenBC p O κ toκ]
  rfl

theorem stalkMap_germ_jCoordBC_sub (p : ℕ) [Fact p.Prime] (O κ : Type) [CommRing O] [CommRing κ] (toκ : O →+* κ) (ĵ : O)
    (y : ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ))
    (hyκ : y ∈ TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ)
    (hyO : (bcMap p O κ toκ).base y ∈ TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) :
    ((bcMap p O κ toκ).stalkMap y).hom
      ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) ((bcMap p O κ toκ).base y) hyO
        (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O -
          ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.map (homOfLE (le_top : TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O ≤ ⊤)).op).hom
            (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O ĵ))) =
    (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ) y hyκ
        (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ -
          ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).presheaf.map (homOfLE (le_top : TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ ≤ ⊤)).op).hom
            (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ (toκ ĵ))) := by

  set bc := bcMap p O κ toκ with hbc
  have hι := bcMap_baseChangeι p O κ toκ
  have hβ := bcMap_baseChangeToBase p O κ toκ
  rw [← hbc] at hι hβ

  have H1 : ∀ (s : Γ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O), ⊤)),
      ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).presheaf.germ (bc ⁻¹ᵁ TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) y hyO).hom
        ((bc.app (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O)).hom
          (((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.map (homOfLE (le_top : TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O ≤ ⊤)).op).hom s)) =
      ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).presheaf.germ ⊤ y trivial).hom (bc.appTop.hom s) := by
    intro s
    have e : (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.map (homOfLE (le_top : TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O ≤ ⊤)).op ≫
        bc.app (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) ≫
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).presheaf.germ (bc ⁻¹ᵁ TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) y hyO =
        bc.appTop ≫ (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).presheaf.germ ⊤ y trivial := by
      rw [bc.naturality_assoc, TopCat.Presheaf.germ_res]
      rfl
    have := congrArg (fun φ => φ.hom s) e
    simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using this

  have H1' : ∀ (t : Γ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ), ⊤)),
      ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ) y hyκ).hom
        (((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).presheaf.map (homOfLE (le_top : TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ ≤ ⊤)).op).hom t) =
      ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).presheaf.germ ⊤ y trivial).hom t := by
    intro t
    have e : (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).presheaf.map (homOfLE (le_top : TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ ≤ ⊤)).op ≫
        (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ) y hyκ = (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).presheaf.germ ⊤ y trivial :=
      TopCat.Presheaf.germ_res _ _ _ _
    have := congrArg (fun φ => φ.hom t) e
    simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using this

  have H2 : ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).presheaf.germ (bc ⁻¹ᵁ TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) y hyO).hom
        ((bc.app (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O)).hom (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O)) =
      ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ) y hyκ).hom (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ) := by
    have e : ∀ (g : (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ) ⟶ AlgebraicCurve.TwoChartIntegralModel ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) (_ : bc ≫ TwoChartIntegralModel.baseChangeι ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O = g)
        (hy : y ∈ g ⁻¹ᵁ chartFinOpen ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
        ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).presheaf.germ (bc ⁻¹ᵁ TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) y hyO).hom
          ((bc.app (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O)).hom
            (((TwoChartIntegralModel.baseChangeι ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).app (chartFinOpen ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))).hom (TwoChartIntegralModel.jCoord ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))) =
        ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).presheaf.germ (g ⁻¹ᵁ chartFinOpen ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) y hy).hom ((g.app (chartFinOpen ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))).hom (TwoChartIntegralModel.jCoord ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) := by
      rintro g rfl hy
      rfl
    exact e _ hι hyκ

  have H3 : bc.appTop.hom (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O ĵ) = TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ (toκ ĵ) := by
    show (bc.appTop).hom (((TwoChartIntegralModel.baseChangeToBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).appTop).hom _) =
      ((TwoChartIntegralModel.baseChangeToBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of κ)).inv (toκ ĵ))
    have e : (TwoChartIntegralModel.baseChangeToBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).appTop ≫ bc.appTop =
        (Spec.map (CommRingCat.ofHom toκ)).appTop ≫ (TwoChartIntegralModel.baseChangeToBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).appTop := by
      rw [← Scheme.Hom.comp_appTop, hβ, Scheme.Hom.comp_appTop]
    have e2 : CommRingCat.ofHom toκ ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).inv =
        (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ (Spec.map (CommRingCat.ofHom toκ)).appTop :=
      Scheme.ΓSpecIso_inv_naturality _
    have h1 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ĵ)) e
    have h2 := congrArg (fun φ => φ.hom ĵ) e2
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h1 h2
    rw [h1, ← h2]

  have HS : ∀ s, (bc.stalkMap y).hom (((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) (bc.base y) hyO) s) =
      ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).presheaf.germ (bc ⁻¹ᵁ TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) y hyO).hom
        ((bc.app (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O)).hom s) := fun s => by
    have e := bc.germ_stalkMap (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) y hyO
    have := congrArg (fun φ => φ.hom s) e
    simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using this
  rw [HS, map_sub, map_sub, H2, H1, H3, map_sub, H1']

end RmConv

namespace RmConv

theorem not_mem_jNeLocus_of_bcMap_eq (p : ℕ) [Fact p.Prime] (O κ : Type) [CommRing O] [CommRing κ] (toκ : O →+* κ) (ĵ : O)
    (x₀ : ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O)) (hx₀ : x₀ ∈ TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O)
    (h : ¬ IsUnit ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) x₀ hx₀
        (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O -
          ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.map (homOfLE (le_top : TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O ≤ ⊤)).op).hom
            (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O ĵ))))
    (y : ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ)) (hy : (bcMap p O κ toκ).base y = x₀) :
    y ∉ TwoChartIntegralModel.jNeLocus ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ (toκ ĵ) := by
  subst hy
  have hyκ : y ∈ TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ := (mem_chartFinOpenBC_iff p O κ toκ y).mp hx₀
  apply not_mem_jNeLocus_of_not_isUnit_germ ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ (toκ ĵ) y hyκ
  rw [← stalkMap_germ_jCoordBC_sub p O κ toκ ĵ y hyκ hx₀]
  exact fun hu => h (isUnit_of_map_unit ((bcMap p O κ toκ).stalkMap y).hom _ hu)
end RmConv

namespace RmConv

theorem mem_chartFinOpenBC_and_not_isUnit_of_phi_eq_jFun_sub
    (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    (K : Type) [Field K] [Algebra O K] (ιK : K →+* AlgebraicClosure ℚ)
    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+* ↥(modularFunctionFieldBar (1 * p)))
    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial).hom
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
    (ĵ : O) (t : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)
    (ht : t ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x))
    (hφt : haveI : NeZero (1 * p) := ⟨by rw [one_mul]; exact (Fact.out : p.Prime).ne_zero⟩
      φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField t) =
        ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ))) :
    ∃ hxF : x ∈ TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O,
      ¬ IsUnit (((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.germ
          (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) x hxF).hom
        (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O -
          (((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.map
            (homOfLE (le_top : TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O ≤ ⊤)).op).hom
            (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ĵ))))) := by
  classical
  haveI : NeZero (1 * p) := ⟨by rw [one_mul]; exact (Fact.out : p.Prime).ne_zero⟩

  obtain ⟨⟨x₀, hx₀U⟩⟩ := id hne
  haveI : IsIntegral (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) := hint
  have hx₀ : x₀ ∈ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) := by
    have e := TwoChartIntegralModel.TwoChartsAux.U_eq ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)
    change x₀ ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (TwoChartIntegralModel.chartFinOpen ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))
    rw [← e]; exact hx₀U

  set F := (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField with hFdef
  set J : ↥F := algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x₀) F
    (((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) x₀ hx₀).hom
      (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O)) with hJ
  set c' : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x := ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.germ ⊤ x trivial).hom (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ĵ)) with hc'
  set C : ↥F := algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) F c' with hC
  have hφJ : φ J = ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p :=
    phi_algebraMap_germ_jCoordBC p O x₀ φ hφj hx₀
  have hφC : φ C = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ)) := hφO ĵ
  have ht' : algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) F t = J - C := by
    apply φ.injective
    rw [map_sub, hφJ, hφC]
    exact hφt
  have hinj : Function.Injective (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) F) :=
    IsFractionRing.injective _ _

  have hxF : x ∈ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) := by
    by_contra hxnot
    have hcov : x ∈ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) ⊔ (TwoChartIntegralModel.chartInfOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) := by
      rw [TwoChartIntegralModel.chartFinOpenBC_sup_chartInfOpenBC]; trivial
    have hxI : x ∈ (TwoChartIntegralModel.chartInfOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) := (TopologicalSpace.Opens.mem_sup.mp hcov).resolve_left hxnot
    obtain ⟨hj', hprod⟩ := not_isUnit_germ_jInvCoordBC_and_mul_eq_one ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O
      x hxI hxnot x₀ hx₀
    set j' : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x := ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.germ (TwoChartIntegralModel.chartInfOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) x hxI).hom
      (TwoChartIntegralModel.jInvCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) with hj'def

    have hEq : t * j' = 1 - c' * j' := by
      apply hinj
      rw [map_mul, map_sub, map_one, map_mul, ht', sub_mul, ← hC]
      have hprod' : algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) F j' * J = 1 := hprod
      rw [mul_comm J, hprod']
    have hmem : t * j' ∈ IsLocalRing.maximalIdeal _ := Ideal.mul_mem_right _ _ ht
    have hj'm : j' ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).mpr hj'
    have hunit : IsUnit (1 - c' * j') := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
      ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_left _ _ hj'm))
    rw [← hEq] at hunit
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem hunit
  refine ⟨hxF, ?_⟩

  have hJx : algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) F
      (((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) x hxF).hom
        (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O)) = J := by
    have hξ : genericPoint ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ∈ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) :=
      ((genericPoint_spec ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))).mem_open_set_iff (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).isOpen).mpr ⟨x, trivial, hxF⟩
    have h1 : algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) F
        (((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) x hxF).hom
          (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O)) =
        ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) (genericPoint _) hξ).hom
          (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) := by
      show (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))).presheaf.stalkSpecializes _).hom _ = _
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    have h2 : J = ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) (genericPoint _) hξ).hom
          (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) := by
      rw [hJ]
      show (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))).presheaf.stalkSpecializes _).hom _ = _
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    rw [h1, h2]
  intro hu
  set jx : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x := ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) x hxF).hom
      (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) with hjx
  rw [map_sub, TopCat.Presheaf.germ_res_apply] at hu

  have hdiff : jx - c' = t := by
    apply hinj
    rw [map_sub, hJx, ht', hC]
  have hu' : IsUnit (jx - c') := hu
  rw [hdiff] at hu'
  exact (IsLocalRing.mem_maximalIdeal _).mp ht hu'

end RmConv

section Surj
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_mem_nodeIntegers_of_stalk_of_specializes_of_exists_sub_mem.AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRModelPackage_mem_nodeIntegers_of_stalk_of_specializes_of_exists_sub_mem.ModularCurve"
namespace ModularCurve p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage ModularPolynomialData modularFunctionFieldFull IgusaScheme.jFull IgusaScheme coeffEmb modularFunctionFieldBar PlaceSpecialization.ProlongationTuple.jFun PlaceSpecialization.ProlongationTuple modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence ssPlaces jGeomGen charLGeomPlaceOfPoint isRational_place_modularFunctionFieldBar PlaceSpecialization.ProlongationTuple.mem_nodeIntegers_iff DRModel.baseChangeMap DRModelPackage.eq_of_forall_exists_comp_baseChangeMap_eq_of_not_mem_jNeLocus DRModelPackage.mem_integers_and_mem_integers_of_stalk_of_specializes DRModelPackage.range_compInf_comp_baseChangeMap_eq_closure_and_isClosed DRModelPackage.range_compZero_comp_baseChangeMap_eq_closure_and_isClosed mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq PlaceSpecialization.redFst_eq_charLGeomPlaceOfPoint_iff PlaceSpecialization.jFun ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap" namespace DRModel p2m_export "ModularCurve.DRModel" "toBase baseChangeMap" end ModularCurve.DRModel
p2m_open_scoped "ModularCurve ModularCurve.DRModel" in

theorem ModularCurve.DRModel.exists_baseChangeMap_eq_of_natCast_mem
    (p : ℕ) [Fact p.Prime]
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    {κ : Type} [Field κ] [CharP κ p] (toκ : O →+* κ)
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (hx : ((p : ℕ) : O) ∈ ((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base x).asIdeal) :
    ∃ y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))),
      (DRModel.baseChangeMap (p := p) toκ).base y = x := by

  have hOpt : ∀ (𝔮 : Ideal O) [𝔮.IsPrime], ((p : ℕ) : O) ∈ 𝔮 → 𝔮 = IsLocalRing.maximalIdeal O := by
    intro 𝔮 _ hq
    have hle : IsLocalRing.maximalIdeal O ≤ 𝔮 := by
      rw [hϖ, Ideal.span_singleton_le_iff_mem]; exact hq
    exact ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (Ideal.IsPrime.ne_top ‹_›) hle).symm
  have hker : RingHom.ker toκ = IsLocalRing.maximalIdeal O := by
    haveI : (RingHom.ker toκ).IsPrime := RingHom.ker_isPrime toκ
    exact hOpt _ (by rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero])
  have hz : (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base x = IsLocalRing.closedPoint O :=
    PrimeSpectrum.ext (hOpt _ hx)
  have hr := Scheme.Pullback.range_map (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))
    (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) (𝟙 _) (Spec.map (CommRingCat.ofHom toκ)) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.ext_int (toκ.comp (algebraMap ℤ O)) (algebraMap ℤ κ)])
  have hx' : x ∈ Set.range ⇑(pullback.map (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))
    (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) (𝟙 _) (Spec.map (CommRingCat.ofHom toκ)) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.ext_int (toκ.comp (algebraMap ℤ O)) (algebraMap ℤ κ)])) := by
    rw [hr]
    refine ⟨by simp, ?_⟩
    show (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base x ∈
      Set.range (Spec.map (CommRingCat.ofHom toκ)).base
    refine ⟨IsLocalRing.closedPoint κ, ?_⟩
    rw [hz]
    apply PrimeSpectrum.ext
    change Ideal.comap toκ (IsLocalRing.closedPoint κ).asIdeal = (IsLocalRing.closedPoint O).asIdeal
    rw [show (IsLocalRing.closedPoint κ).asIdeal = ⊥ from IsLocalRing.maximalIdeal_eq_bot (R := κ) |>.symm ▸ rfl,
      ← RingHom.ker_eq_comap_bot, hker]
    rfl
  obtain ⟨y, hy⟩ := hx'
  exact ⟨y, hy⟩

end Surj

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_mem_nodeIntegers_of_stalk_of_specializes_of_exists_sub_mem.AlgebraicGeometry"
p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_DRModelPackage_mem_nodeIntegers_of_stalk_of_specializes_of_exists_sub_mem.ModularCurve ModularCurve.PlaceSpecialization"

open AlgebraicCurve IsLocalRing

open Classical in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_DRModelPackage_mem_nodeIntegers_of_stalk_of_specializes_of_exists_sub_mem.ModularCurve ModularCurve.DRModelPackage in

theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)

    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial).hom
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

    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k p] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ) (R : ProlongationTuple P)
    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)

    [IsAlgClosed k] (toκ : O →+* k) (htoκ : ∀ a : O, toκ a = red ⟨ιK (algebraMap O K a), hιA a⟩)

    (hsp₁ : (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)
    (hsp₂ : (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)

    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ ssPlaces p 1 k)
    (hxj : ∃ ĵ : O, red ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩ = w.evalAt (jGeomGen k 1) ∧
      ∃ t ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x),
        φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField t) =
          ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p -
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ)))
    :
    ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x,
      φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) s) ∈ R.nodeIntegers w := by
  classical
  haveI : NeZero (1 * p) := ⟨by rw [one_mul]; exact (Fact.out : p.Prime).ne_zero⟩
  intro s
  rw [ModularCurve.PlaceSpecialization.ProlongationTuple.mem_nodeIntegers_iff]
  refine ⟨?_, ?_, ?_⟩
  ·
    exact (ModularCurve.DRModelPackage.mem_integers_and_mem_integers_of_stalk_of_specializes p hp 𝔛 O hϖ K ιK x φ hφO hφj P R hιA toκ htoκ hsp₁ hsp₂ s).1
  ·
    exact (ModularCurve.DRModelPackage.mem_integers_and_mem_integers_of_stalk_of_specializes p hp 𝔛 O hϖ K ιK x φ hφO hφj P R hιA toκ htoκ hsp₁ hsp₂ s).2
  · intro V hV

    obtain ⟨B', hB'mem, hB'const, hB'p, hB'pinv⟩ := LComposite.exists_valuationSubring_mem_iff_hasValue red V φ

    have hconst : ∀ a : O, (Spec.preimage ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).fromSpecStalk (genericPoint _) ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))).hom a ∈ B' := by
      intro a
      rw [AlgebraicGeometry.Spec_preimage_fromSpecStalk_comp_apply (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) x a]
      exact hB'const (ιK (algebraMap O K a)) (hιA a) _ (by simpa using hφO a)

    haveI : IsProper (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) := by
      haveI := 𝔛.isProper
      exact MorphismProperty.pullback_snd _ _ inferInstance
    obtain ⟨x'', hx''B, hx''loc⟩ :=
      AlgebraicGeometry.exists_forall_algebraMap_functionField_mem_of_isProper (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) B' hconst

    obtain ⟨ĵ, hĵ, t, ht, hφt⟩ := hxj
    have hx''x : x'' = x := by

      obtain ⟨hxF, hxnu⟩ := RmConv.mem_chartFinOpenBC_and_not_isUnit_of_phi_eq_jFun_sub p O K ιK x φ hφO hφj ĵ t ht hφt

      have hCC₁ : Set.range (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base =
          closure {(𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)} :=
        (ModularCurve.DRModelPackage.range_compInf_comp_baseChangeMap_eq_closure_and_isClosed p 𝔛 O hϖ k toκ).1
      have hCC₂ : Set.range (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base =
          closure {(𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)} :=
        (ModularCurve.DRModelPackage.range_compZero_comp_baseChangeMap_eq_closure_and_isClosed p 𝔛 O hϖ k toκ).1
      have hx₁ : ∃ z : ↥(𝔛.ratModel k).C, (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base z = x ∧
          (𝔛.compInf k).base z ∉ ((TwoChartIntegralModel.jNeLocus ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k (toκ ĵ) :
            (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).Opens) :
          Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k)) := by
        have hxr : x ∈ Set.range (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base := by
          rw [hCC₁]; exact specializes_iff_mem_closure.mp hsp₁
        obtain ⟨z, hz⟩ := hxr
        exact ⟨z, hz, RmConv.not_mem_jNeLocus_of_bcMap_eq p O k toκ ĵ x hxF hxnu _ hz⟩
      have hx₂ : ∃ z : ↥(𝔛.ratModel k).C, (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base z = x ∧
          (𝔛.compZero k).base z ∉ ((TwoChartIntegralModel.jNeLocus ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k (toκ ĵ) :
            (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).Opens) :
          Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k)) := by
        have hxr : x ∈ Set.range (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base := by
          rw [hCC₂]; exact specializes_iff_mem_closure.mp hsp₂
        obtain ⟨z, hz⟩ := hxr
        exact ⟨z, hz, RmConv.not_mem_jNeLocus_of_bcMap_eq p O k toκ ĵ x hxF hxnu _ hz⟩

      have hx'' : ∃ y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))),
          (DRModel.baseChangeMap toκ).base y = x'' ∧ y ∉ ((TwoChartIntegralModel.jNeLocus ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k (toκ ĵ) :
            (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).Opens) :
          Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k)) := by

        haveI : NeZero (1 * p) := ⟨by rw [one_mul]; exact (Fact.out : p.Prime).ne_zero⟩

        have hne' := hne
        obtain ⟨⟨x₀, hx₀U⟩⟩ := hne'
        haveI : AlgebraicGeometry.IsIntegral (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) := hint
        have hx₀ : x₀ ∈ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) := by
          show (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base x₀ ∈ TwoChartIntegralModel.chartFinOpen ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)
          rw [← AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux.U_eq]
          exact hx₀U

        set J : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) := algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x₀) _
          (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) x₀ hx₀).hom (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O)) with hJdef
        have hφJ : φ J = ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p :=
          RmConv.phi_algebraMap_germ_jCoordBC p O x₀ φ hφj hx₀
        set C : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) := algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) _
          (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial).hom
            (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ĵ))) with hCdef
        have hφC : φ C = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ)) := hφO ĵ

        have hJB : J ∈ B' ∧ (J - C) ∈ B' ∧ (J - C) ∈ B'.nonunits := by

          have hvalOf : ∀ {K' F' : Type} [Field K'] [Field F'] [Algebra K' F'] (v : Place K' F') (g : F') (a : K'),
              0 < v.ord (g - algebraMap K' F' a) → v.HasValue g a := by
            intro K' F' _ _ _ v g a hord
            have hne : g - algebraMap K' F' a ≠ 0 := by
              intro h0; rw [h0, Place.ord_zero] at hord; exact lt_irrefl _ hord
            have hmem : g - algebraMap K' F' a ∈ v.toValuationSubring := Place.mem_of_ord_nonneg v hne hord.le
            have hmax := Place.mk_mem_maximalIdeal_of_ord_pos v hmem hord
            have ha := (v.hasValue_algebraMap a)
            have hg : g ∈ v.toValuationSubring := by
              have : g = (g - algebraMap K' F' a) + algebraMap K' F' a := by ring
              rw [this]; exact add_mem hmem ha.mem
            refine ⟨hg, ?_⟩
            have e : (⟨g, hg⟩ : v.toValuationSubring) = ⟨g - algebraMap K' F' a, hmem⟩ + ⟨algebraMap K' F' a, ha.mem⟩ := by
              apply Subtype.ext; show g = (g - _) + _; ring
            rw [e, map_add, (IsLocalRing.residue_eq_zero_iff _).mpr hmax, zero_add, ha.residue_eq]

          obtain ⟨a, haSS, hwa⟩ := (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq p k w).mp hw
          have hja : w.HasValue (jGeomGen k 1) a := by
            apply hvalOf
            rw [← hwa]
            have := ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap k a a
            rw [if_pos rfl] at this
            change (charLGeomPlaceOfPoint k a).ord (jGeomGen k 1 - _) = 1 at this
            rw [this]; exact zero_lt_one
          have hwev : w.evalAt (jGeomGen k 1) = a := by
            rw [Place.evalAt_of_mem _ hja.mem, hja.residue_eq, Place.residueInv_algebraMap]

          set c : ↥A := ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩ with hcdef
          have hredc : red c = a := by rw [hcdef, hĵ, hwev]
          obtain ⟨b, hredb, hordb⟩ := (ModularCurve.PlaceSpecialization.redFst_eq_charLGeomPlaceOfPoint_iff P V a).mp
            (by show P.reduceFst V = _; rw [hV, hwa])
          have hjf : ModularCurve.PlaceSpecialization.jFun (q := p) = ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p :=
            Subtype.ext rfl
          rw [hjf] at hordb
          have hjb : V.HasValue (ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p) (b : AlgebraicClosure ℚ) :=
            hvalOf V _ _ hordb

          have hJmem : J ∈ B' := (hB'mem J).mpr ⟨by rw [hφJ]; exact hjb.mem, b, b.2, by rw [hφJ]; exact hjb⟩
          have hCmem : C ∈ B' := hB'const (c : AlgebraicClosure ℚ) c.2 C (by rw [hφC])
          refine ⟨hJmem, sub_mem hJmem hCmem, ?_⟩

          have hval : V.HasValue (φ (J - C)) ((b : AlgebraicClosure ℚ) - (c : AlgebraicClosure ℚ)) := by
            rw [map_sub, hφJ, hφC]
            have hc := V.hasValue_algebraMap ((c : AlgebraicClosure ℚ))
            refine ⟨sub_mem hjb.mem hc.mem, ?_⟩
            have e : (⟨_, sub_mem hjb.mem hc.mem⟩ : V.toValuationSubring) = ⟨_, hjb.mem⟩ - ⟨_, hc.mem⟩ := rfl
            rw [e, map_sub, hjb.residue_eq, hc.residue_eq, map_sub]
          rw [ValuationSubring.mem_nonunits_iff]
          by_contra hlt

          have hne0 : J - C ≠ 0 := by
            intro h0; rw [h0, Valuation.map_zero] at hlt; exact hlt zero_lt_one
          have hinv : (J - C)⁻¹ ∈ B' := by
            rw [← B'.valuation_le_one_iff, map_inv₀]
            exact inv_le_one_of_one_le₀ (not_lt.mp hlt)
          obtain ⟨-, d, hdA, hd⟩ := (hB'mem _).mp hinv
          rw [map_inv₀] at hd
          have h1 := hval.mul hd
          rw [mul_inv_cancel₀ (by intro h0; exact hne0 (φ.injective (by rw [h0, map_zero])))] at h1
          have hbc : ((b : AlgebraicClosure ℚ) - c) * d = 1 := (V.hasValue_one.unique h1).symm

          have hu : IsUnit (b - c : ↥A) := by
            refine ⟨⟨b - c, ⟨d, hdA⟩, Subtype.ext hbc, Subtype.ext (by rw [mul_comm] at hbc; exact hbc)⟩, rfl⟩
          have := hu.map red
          rw [map_sub, hredb, hredc, sub_self] at this
          exact not_isUnit_zero this

        have hunit : ∀ g : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x'', IsUnit g →
            ∀ f : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField), f ∈ B'.nonunits → algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) g * f ≠ 1 := by
          intro g hg f hf e
          obtain ⟨u, rfl⟩ := hg
          have hle : B'.valuation (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x'') ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) ↑u) ≤ 1 :=
            (B'.valuation_le_one_iff _).mpr (hx''B _)
          rw [ValuationSubring.mem_nonunits_iff] at hf
          have : B'.valuation (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x'') ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) ↑u * f) < 1 :=
            calc B'.valuation (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x'') ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) ↑u * f)
                = B'.valuation (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x'') ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) ↑u) * B'.valuation f := map_mul _ _ _
              _ ≤ 1 * B'.valuation f := mul_le_mul_left hle _
              _ = B'.valuation f := one_mul _
              _ < 1 := hf
          rw [e, map_one] at this
          exact lt_irrefl _ this

        have hx''F : x'' ∈ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) := by
          by_contra hnot
          have hx''I : x'' ∈ (TwoChartIntegralModel.chartInfOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) := by
            have : x'' ∈ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) ⊔ (TwoChartIntegralModel.chartInfOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) := by
              rw [TwoChartIntegralModel.chartFinOpenBC_sup_chartInfOpenBC]; trivial
            exact (TopologicalSpace.Opens.mem_sup.mp this).resolve_left hnot
          obtain ⟨hnu, hmul⟩ :=
            RmConv.not_isUnit_germ_jInvCoordBC_and_mul_eq_one ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O x'' hx''I hnot x₀ hx₀

          have hJ' := hx''loc _ ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
          rw [ValuationSubring.mem_nonunits_iff] at hJ'
          have hle : B'.valuation J ≤ 1 := (B'.valuation_le_one_iff _).mpr hJB.1
          have hlt := calc B'.valuation (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x'') ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)
                  (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ (TwoChartIntegralModel.chartInfOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) x'' hx''I).hom (TwoChartIntegralModel.jInvCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O)) * J)
                = B'.valuation (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x'') ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)
                  (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ (TwoChartIntegralModel.chartInfOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) x'' hx''I).hom (TwoChartIntegralModel.jInvCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O))) * B'.valuation J := map_mul _ _ _
              _ ≤ _ * 1 := mul_le_mul_right hle _
              _ < 1 := by rw [mul_one]; exact hJ'
          rw [hJdef] at hlt
          erw [hmul] at hlt
          erw [Valuation.map_one] at hlt
          exact lt_irrefl _ hlt

        have hJx'' : algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x'') ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)
            (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) x'' hx''F).hom (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O)) = J := by
          apply φ.injective
          rw [RmConv.phi_algebraMap_germ_jCoordBC p O x'' φ hφj hx''F, hφJ]
        have hCx'' : algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x'') ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)
            (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) x'' hx''F).hom
              (((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.map (homOfLE (le_top : (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) ≤ ⊤)).op).hom (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O ĵ))) = C := by
          have eres : (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.map (homOfLE (le_top : (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) ≤ ⊤)).op ≫ (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) x'' hx''F =
              (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.germ ⊤ x'' trivial := TopCat.Presheaf.germ_res _ _ _ _
          have hres := congrArg (fun ψ => ψ.hom (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O ĵ)) eres
          simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hres
          erw [hres]
          rw [hCdef]
          show ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes _).hom _ = ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes _).hom _
          erw [TopCat.Presheaf.germ_stalkSpecializes_apply, TopCat.Presheaf.germ_stalkSpecializes_apply]
          rfl
        have hgerm : ¬ IsUnit (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) x'' hx''F).hom
            (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O -
              ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).presheaf.map (homOfLE (le_top : (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O) ≤ ⊤)).op).hom (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O ĵ))) := by
          intro hu
          obtain ⟨u, hu⟩ := hu
          apply hunit ↑u⁻¹ (Units.isUnit _) (J - C) hJB.2.2
          erw [← hJx'', ← hCx'', ← map_sub, ← map_sub, ← hu, ← map_mul, Units.inv_mul, map_one]

        have hpnon : ((p : ℕ) : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)) ∈ B'.nonunits := by
          rw [ValuationSubring.mem_nonunits_iff]
          by_contra h
          apply hB'pinv
          rw [← B'.valuation_le_one_iff, map_inv₀]
          have h1 : B'.valuation ((p : ℕ) : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)) ≤ 1 := (B'.valuation_le_one_iff _).mpr hB'p
          have h2 : B'.valuation ((p : ℕ) : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)) = 1 := le_antisymm h1 (not_lt.mp h)
          rw [h2, inv_one]
        have hpx : ¬ IsUnit ((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x'') := by
          intro hu
          obtain ⟨u, hu⟩ := hu
          apply hunit ↑u⁻¹ (Units.isUnit _) _ hpnon
          rw [← map_natCast (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x'') ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)), ← hu, ← map_mul, Units.inv_mul, map_one]
        have hpx' : ((p : ℕ) : O) ∈ ((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base x'').asIdeal := by
          set s := (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) with hs
          have h1 : ¬ IsUnit ((p : ℕ) : (Spec (CommRingCat.of O)).presheaf.stalk (s.base x'')) := by
            intro hu
            apply hpx
            have := hu.map (s.stalkMap x'').hom
            rwa [map_natCast] at this
          letI := StructureSheaf.stalkAlgebra (↑(CommRingCat.of O)) (s.base x'')
          haveI := StructureSheaf.IsLocalization.to_stalk (↑(CommRingCat.of O)) (s.base x'')
          by_contra hn
          apply h1
          have := (IsLocalization.AtPrime.isUnit_to_map_iff
            ((Spec.structureSheaf ↑(CommRingCat.of O)).presheaf.stalk (s.base x'')) (s.base x'').asIdeal ((p : ℕ) : O)).mpr hn
          rwa [map_natCast] at this
        obtain ⟨y, hy⟩ := ModularCurve.DRModel.exists_baseChangeMap_eq_of_natCast_mem p O hϖ toκ x'' hpx'
        exact ⟨y, hy, RmConv.not_mem_jNeLocus_of_bcMap_eq p O k toκ ĵ x'' hx''F hgerm y hy⟩

      exact ModularCurve.DRModelPackage.eq_of_forall_exists_comp_baseChangeMap_eq_of_not_mem_jNeLocus
        p 𝔛 O k toκ (toκ ĵ) x x'' hx₁ hx₂ hx''
    subst hx''x

    exact ((hB'mem _).mp (hx''B s)).1

end S_ModularCurve_DRModelPackage_mem_nodeIntegers_of_stalk_of_specializes_of_exists_sub_mem
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_mem_nodeIntegers_of_stalk_of_specializes_of_exists_sub_mem (solution)
