-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.exists_isTwistOf_of_componentGroupProj_depthDual_eq_zero_of_inertiaStable_of_laws
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/19256b3a-76ac-5f6d-815d-a0ba08f3c1d1

import Definitions.Def_ModularCurve_AnnulusSpecializationLevel
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_nodeCoordinates_presentation_of_orderLawFixed
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_xDepth_eq_and_yDepth_eq_of_nodeCoordinates
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable
import Theorems.Thm_ValuationSubring_eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictFst_or_isStrictSnd_iff
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ModularCurve_ssPlaces_nonempty
import Theorems.Thm_ModularCurve_one_le_placeWidthChar_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_exists_isTwistOf_of_componentGroupProj_depthDual_eq_zero_of_inertiaStable_of_laws
p2m_attr_erase "instance" "GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one"
p2m_attr_erase "simp" "AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.cuspCount_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of"
p2m_attr_erase "simp" "AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open ModularCurve.PlaceSpecialization.ProlongationTuple

namespace BookTwist

section Lattice
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem eq_const_of_forall_sum_mul_eq_zero (β : ι → ℤ)
    (h : ∀ c : characterLattice ι, ∑ s, β s * c.1 s = 0) : ∀ s s', β s = β s' := by
  intro s s'
  by_cases hss : s = s'
  · rw [hss]
  have hmem : (Pi.single s (1 : ℤ) - Pi.single s' 1) ∈ characterLattice ι := by
    rw [mem_characterLattice]
    simp [Finset.sum_sub_distrib]
  have h1 := h ⟨_, hmem⟩
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib] at h1
  have e1 : ∑ x, β x * Pi.single (M := fun _ => ℤ) s (1 : ℤ) x = β s := by
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · intro hs; exact absurd (Finset.mem_univ s) hs
  have e2 : ∑ x, β x * Pi.single (M := fun _ => ℤ) s' (1 : ℤ) x = β s' := by
    rw [Finset.sum_eq_single s']
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · intro hs; exact absurd (Finset.mem_univ s') hs
  rw [e1, e2] at h1
  linarith

theorem exists_coeff_of_mem_range_gramMap (e : ι → ℕ) (α : ι → ℤ)
    (h : (∑ s, α s • crossingCoord s : Module.Dual ℤ (characterLattice ι)) ∈ LinearMap.range (gramMap e)) :
    ∃ (γ : ι → ℤ) (κ : ℤ), (∑ s, γ s = 0) ∧ ∀ s, α s = (e s : ℤ) * γ s + κ := by
  obtain ⟨γΛ, hγ⟩ := h
  have hΛ : ∑ s, γΛ.1 s = 0 := mem_characterLattice.mp γΛ.2

  have hkill : ∀ c : characterLattice ι, ∑ s, (α s - (e s : ℤ) * γΛ.1 s) * c.1 s = 0 := by
    intro c
    have h1 := LinearMap.congr_fun hγ c
    rw [gramMap_apply, LinearMap.sum_apply] at h1
    simp only [LinearMap.smul_apply, crossingCoord_apply, smul_eq_mul] at h1
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero, ← h1]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hconst := eq_const_of_forall_sum_mul_eq_zero _ hkill
  by_cases hι : Nonempty ι
  · obtain ⟨s₁⟩ := hι
    refine ⟨γΛ.1, α s₁ - (e s₁ : ℤ) * γΛ.1 s₁, hΛ, fun s => ?_⟩
    have := hconst s s₁
    linarith
  · refine ⟨γΛ.1, 0, hΛ, fun s => ?_⟩
    exact absurd ⟨s⟩ hι

end Lattice

noncomputable def tent (t : ℚ) (d : ℕ) : ℚ := max 0 (1 - |t - d|)

theorem tent_eq (t : ℚ) (h0 : 0 ≤ t) (d : ℕ) :
    tent t d = if d = ⌊t⌋₊ then 1 - (t - ⌊t⌋₊) else if d = ⌊t⌋₊ + 1 then t - ⌊t⌋₊ else 0 := by
  have hfl : (⌊t⌋₊ : ℚ) ≤ t := Nat.floor_le h0
  have hlt : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
  unfold tent
  by_cases h1 : d = ⌊t⌋₊
  · subst h1
    rw [if_pos rfl, abs_of_nonneg (by linarith), max_eq_right (by linarith)]
  · rw [if_neg h1]
    by_cases h2 : d = ⌊t⌋₊ + 1
    · subst h2
      rw [if_pos rfl, abs_of_nonpos (by push_cast; linarith), max_eq_right (by push_cast; linarith)]
      push_cast; ring
    · rw [if_neg h2]
      apply max_eq_left

      rcases lt_or_gt_of_ne h1 with hlt' | hgt'
      ·
        have : (d : ℚ) + 1 ≤ ⌊t⌋₊ := by exact_mod_cast hlt'
        rw [abs_of_nonneg (by linarith)]
        linarith
      ·
        have hd2 : ⌊t⌋₊ + 2 ≤ d := by omega
        have : (⌊t⌋₊ : ℚ) + 2 ≤ d := by exact_mod_cast hd2
        rw [abs_of_nonpos (by linarith)]
        linarith

theorem tent_sum_eq_one {L : ℕ} {t : ℚ} (h0 : 0 < t) (hL : t < L) :
    ∑ d ∈ Finset.range (L + 1), tent t d = 1 := by
  have hfl : (⌊t⌋₊ : ℚ) ≤ t := Nat.floor_le h0.le
  have hn : ⌊t⌋₊ + 1 ≤ L := by
    have : ⌊t⌋₊ < L := by
      by_contra h
      push_neg at h
      have : (L : ℚ) ≤ ⌊t⌋₊ := by exact_mod_cast h
      linarith
    omega
  have hsub : ({⌊t⌋₊, ⌊t⌋₊ + 1} : Finset ℕ) ⊆ Finset.range (L + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_range]; omega
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_pair (by omega), tent_eq t h0.le, tent_eq t h0.le, if_pos rfl, if_neg (by omega), if_pos rfl]
    ring
  · intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    rw [tent_eq t h0.le, if_neg hx.1, if_neg hx.2]

theorem tent_sum_mul_eq {L : ℕ} {t : ℚ} (h0 : 0 < t) (hL : t < L) :
    ∑ d ∈ Finset.range (L + 1), (d : ℚ) * tent t d = t := by
  have hfl : (⌊t⌋₊ : ℚ) ≤ t := Nat.floor_le h0.le
  have hn : ⌊t⌋₊ + 1 ≤ L := by
    have : ⌊t⌋₊ < L := by
      by_contra h
      push_neg at h
      have : (L : ℚ) ≤ ⌊t⌋₊ := by exact_mod_cast h
      linarith
    omega
  have hsub : ({⌊t⌋₊, ⌊t⌋₊ + 1} : Finset ℕ) ⊆ Finset.range (L + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_range]; omega
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_pair (by omega), tent_eq t h0.le, tent_eq t h0.le, if_pos rfl, if_neg (by omega), if_pos rfl]
    push_cast; ring
  · intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    rw [tent_eq t h0.le, if_neg hx.1, if_neg hx.2, mul_zero]

theorem ker_red_eq_maximalIdeal {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) :
    ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A := by
  have hq : q.Prime := Fact.out

  have hqker : red ((q : ℕ) : A) = 0 := by rw [map_natCast]; exact CharP.cast_eq_zero k q
  have hker_ne_top : RingHom.ker red ≠ ⊤ := RingHom.ker_ne_top red
  have hker_le : RingHom.ker red ≤ IsLocalRing.maximalIdeal A := IsLocalRing.le_maximalIdeal hker_ne_top
  have hA : A.LiesOverPrime q := by
    show ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits
    have hmax : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := hker_le hqker
    have hcoe : (((q : ℕ) : A) : AlgebraicClosure ℚ) = ((q : ℕ) : AlgebraicClosure ℚ) := by norm_cast
    rw [← hcoe]
    exact (ValuationSubring.coe_mem_nonunits_iff).mpr hmax

  haveI : (RingHom.ker red).IsPrime := RingHom.ker_isPrime red
  have hne : RingHom.ker red ≠ ⊥ := by
    intro h
    have : ((q : ℕ) : A) = 0 := by
      have := (RingHom.mem_ker).mpr hqker
      rw [h] at this
      exact (Ideal.mem_bot).mp this
    have h2 : ((q : ℕ) : AlgebraicClosure ℚ) = 0 := by exact_mod_cast congrArg Subtype.val this
    exact hq.ne_zero (Nat.cast_eq_zero.mp h2)
  have heq : RingHom.ker red = IsLocalRing.maximalIdeal A := by
    by_contra hne'
    exact hne (ValuationSubring.eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime hq A hA _ hne')
  intro c
  rw [← heq, RingHom.mem_ker]

section Setting

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

theorem reduceFst_notMem_of_isStrict (hqN : ¬ q ∣ N) {W : Finset (Place k (modularFunctionFieldC k N))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.IsStrictFst V ∨ P.IsStrictSnd V) :
    P.reduceFst V ∉ W := by
  intro hmem
  have hss := (hW _).mp hmem
  have hfix := ModularCurve.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
    k N hqN data hKr (P.reduceFst V) hss
  exact ((ModularCurve.PlaceSpecialization.isStrictFst_or_isStrictSnd_iff P V).mp hV) hfix

theorem not_isStrictFst_and_isStrictSnd (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : ¬ (P.IsStrictFst V ∧ P.IsStrictSnd V) := by
  rintro ⟨⟨h1, h1'⟩, ⟨h2, _⟩⟩
  apply h1'
  rw [h1, ← h2]

theorem degree_eq_sum (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : Divisor.degree D = ∑ V ∈ D.support, D V := by
  unfold Divisor.degree
  rw [Finsupp.liftAddHom_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun V _ => by
    rw [AddMonoidHom.mulRight_apply, ModularCurve.deg_eq_one_modularFunctionFieldBar (N * q) V]
    simp

theorem degree_filter (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (p : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → Prop) [DecidablePred p] :
    Divisor.degree (D.filter p) = ∑ V ∈ D.support with p V, D V := by
  rw [degree_eq_sum, Finsupp.support_filter]
  refine Finset.sum_congr (by congr) fun V hV => ?_
  rw [Finset.mem_filter] at hV
  exact Finsupp.filter_apply_pos p D hV.2

theorem degree_eq_fst_add_snd_add_sum_annulusDeg (hqN : ¬ q ∣ N)
    {W : Finset (Place k (modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hsupp : ∀ V ∈ D.support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W) :
    Divisor.degree D = Divisor.degree (P.fstDiv D) + Divisor.degree (P.sndDiv D)
      + ∑ w ∈ W, ProlongationTuple.AnnulusDatumLevel.annulusDeg (P := P) D w := by
  classical
  unfold ProlongationTuple.AnnulusDatumLevel.annulusDeg PlaceSpecialization.fstDiv PlaceSpecialization.sndDiv
  rw [degree_filter, degree_filter, degree_eq_sum]

  rw [← Finset.sum_filter_add_sum_filter_not D.support P.IsStrictFst]

  rw [← Finset.sum_filter_add_sum_filter_not (D.support.filter fun V => ¬ P.IsStrictFst V) P.IsStrictSnd]
  have e2 : ∑ V ∈ (D.support.filter fun V => ¬ P.IsStrictFst V) with P.IsStrictSnd V, D V
      = ∑ V ∈ D.support with P.IsStrictSnd V, D V := by
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext V
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hV, _⟩, h2⟩; exact ⟨hV, h2⟩
    · rintro ⟨hV, h2⟩; exact ⟨⟨hV, fun h1 => not_isStrictFst_and_isStrictSnd V ⟨h1, h2⟩⟩, h2⟩
  have e3 : ∑ V ∈ (D.support.filter fun V => ¬ P.IsStrictFst V) with ¬ P.IsStrictSnd V, D V
      = ∑ w ∈ W, ∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), D V := by
    rw [Finset.filter_filter]

    have hfib : ∀ V ∈ D.support.filter (fun V => ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), P.reduceFst V ∈ W := by
      intro V hV
      rw [Finset.mem_filter] at hV
      rcases hsupp V hV.1 with h | h | h
      · exact absurd h hV.2.1
      · exact absurd h hV.2.2
      · exact h
    rw [← Finset.sum_fiberwise_of_maps_to (g := P.reduceFst) hfib]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr ?_ fun _ _ => rfl
    ext V
    simp only [Finset.mem_filter]
    tauto
  rw [e2, e3]
  ring

theorem depthQ_eq_div (R : ProlongationTuple P) (hqN : ¬ q ∣ N)
    {W : Finset (Place k (modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed)
    (dat : R.AnnulusDatumLevel W)
    (hK : ∀ w : Place k (modularFunctionFieldC k N), FiniteDimensional ℚ ↥(dat.K w))
    (hdepthQ : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
      0 < dat.depthQ V ∧ dat.depthQ V < dat.width w ∧ (dat.coord w hw).yDepth V ^ (dat.depthQ V).den =
      A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (dat.depthQ V).num.toNat)
    (ϖd : ∀ w : Place k (modularFunctionFieldC k N), ↥(NodeLocalized.coeffSubring A (dat.K w)))
    (eK : Place k (modularFunctionFieldC k N) → ℕ)
    (u : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), ↥(R.nodeIntegersOver (dat.K w) w))
    (hu : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), IsUnit (u w hw) ∧
      (dat.coord w hw).x * (dat.coord w hw).y = R.nodeConst (dat.K w) w (ϖd w) ^ (dat.width w * eK w) * u w hw)
    (Ks : ↥W → IntermediateField ℚ (AlgebraicClosure ℚ)) [∀ w : ↥W, FiniteDimensional ℚ (Ks w)]
    (cs : ∀ w : ↥W, R.NodeCoordinates (Ks w) (w : Place k (modularFunctionFieldC k N)))
    (ϖ : ∀ w : ↥W, ↥(NodeLocalized.coeffSubring A (Ks w)))
    (hvalA : ∀ w : ↥W, R.ValueIntegralityLaw (w : Place k (modularFunctionFieldC k N)))
    (hxy : ∀ w : ↥W, ∃ (E : ℕ) (u : ↥(R.nodeIntegersOver (Ks w) (w : Place k (modularFunctionFieldC k N)))),
      1 ≤ E ∧ IsUnit u ∧ (cs w).x * (cs w).y = R.nodeConst (Ks w) (w : Place k (modularFunctionFieldC k N)) (ϖ w) ^ E * u)
    (e' : ℕ) (he' : 0 < e')
    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ)
    (w : ↥W) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hVw : P.reduceFst V = (w : Place k (modularFunctionFieldC k N)))
    (hV₁ : ¬ P.IsStrictFst V) (hV₂ : ¬ P.IsStrictSnd V)
    (hdepV : (cs w).yDepth V ^ e' = A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ depth V) :
    dat.depthQ V = (depth V : ℚ) / e' := by
  classical
  set wP : Place k (modularFunctionFieldC k N) := (w : Place k (modularFunctionFieldC k N)) with hwP
  have hwW : wP ∈ W := w.2
  haveI : FiniteDimensional ℚ ↥(dat.K wP) := hK wP
  have hker := ker_red_eq_maximalIdeal (A := A) (q := q) red
  have hW' : ∀ w ∈ W, w ∈ ssPlaces q N k := fun w hw => (hW w).mp hw

  obtain ⟨K₀, instK₀, -, -, c₁, u₁, ⟨hu₁, hxy₁⟩, -⟩ :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.exists_inertiaFixed_nodeCoordinates_presentation_of_orderLawFixed
      R hqN hker hR hO W hW' hRL hNV wP hwW
  haveI := instK₀

  obtain ⟨E, uc, -, huc, hxyc⟩ := hxy w
  have h1 := (ModularCurve.PlaceSpecialization.ProlongationTuple.xDepth_eq_and_yDepth_eq_of_nodeCoordinates R hqN hR W hW'
    hRL hNV wP hwW (hvalA w) (Ks w) (cs w) (ϖ w) E uc huc hxyc K₀ c₁ (placeWidthChar q N wP) u₁ hu₁ hxy₁ V hVw).2
  have h2 := (ModularCurve.PlaceSpecialization.ProlongationTuple.xDepth_eq_and_yDepth_eq_of_nodeCoordinates R hqN hR W hW'
    hRL hNV wP hwW (hvalA w) (dat.K wP) (dat.coord wP hwW) (ϖd wP) (dat.width wP * eK wP) (u wP hwW) (hu wP hwW).1
    (hu wP hwW).2 K₀ c₁ (placeWidthChar q N wP) u₁ hu₁ hxy₁ V hVw).2
  have hyy : (cs w).yDepth V = (dat.coord wP hwW).yDepth V := h1.trans h2.symm

  obtain ⟨ht0, -, htlaw⟩ := hdepthQ wP hwW V hVw hV₁ hV₂

  have hq : q.Prime := Fact.out
  have hqne : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hv0 : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := (Valuation.ne_zero_iff _).mpr hqne
  have hv1 : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1 := by
    rw [← ValuationSubring.mem_nonunits_iff]
    have hqker : red ((q : ℕ) : A) = 0 := by rw [map_natCast]; exact CharP.cast_eq_zero k q
    have hmax : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := (hker _).mp hqker
    have hcoe : (((q : ℕ) : A) : AlgebraicClosure ℚ) = ((q : ℕ) : AlgebraicClosure ℚ) := by norm_cast
    rw [← hcoe]
    exact (ValuationSubring.coe_mem_nonunits_iff).mpr hmax

  have hnum0 : 0 < (dat.depthQ V).num := Rat.num_pos.mpr ht0
  have hpow : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ ((dat.depthQ V).num.toNat * e')
      = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ (depth V * (dat.depthQ V).den) := by
    rw [pow_mul, ← htlaw, ← hyy, ← pow_mul, mul_comm, pow_mul, hdepV, ← pow_mul]
  have hexp : (dat.depthQ V).num.toNat * e' = depth V * (dat.depthQ V).den :=
    pow_right_injective₀ (zero_lt_iff.mpr hv0) hv1.ne hpow

  have hden0 : ((dat.depthQ V).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (dat.depthQ V).den_nz
  have he0 : (e' : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr he'.ne'
  have hnumc : (((dat.depthQ V).num.toNat : ℕ) : ℚ) = (dat.depthQ V).num := by
    have : ((dat.depthQ V).num.toNat : ℤ) = (dat.depthQ V).num := Int.toNat_of_nonneg hnum0.le
    exact_mod_cast this
  have hexpQ : ((dat.depthQ V).num : ℚ) * e' = (depth V : ℚ) * (dat.depthQ V).den := by
    rw [← hnumc]; exact_mod_cast hexp
  rw [← Rat.num_div_den (dat.depthQ V)]
  rw [div_eq_div_iff hden0 he0]
  simpa [Rat.num_div_den] using hexpQ

end Setting

end BookTwist

open BookTwist in
set_option maxHeartbeats 6400000 in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    {W : Finset (Place k (modularFunctionFieldC k N))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (dat : R.AnnulusDatumLevel W)
    (hwidthc : ∀ w ∈ W, dat.width w = placeWidthChar q N w)
    (hdepthQ : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
      (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
      0 < dat.depthQ V ∧ dat.depthQ V < dat.width w ∧ (dat.coord w hw).yDepth V ^ (dat.depthQ V).den =
      A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (dat.depthQ V).num.toNat)
    (hdepthσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      dat.depthQ (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) = dat.depthQ V)
    (hKfix : ∀ w ∈ W, ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ dat.K w, σ z = z)
    (hK : ∀ w : Place k (modularFunctionFieldC k N), FiniteDimensional ℚ ↥(dat.K w))
    (ϖd : ∀ w : Place k (modularFunctionFieldC k N), ↥(NodeLocalized.coeffSubring A (dat.K w)))
    (hϖd : ∀ w ∈ W, ∀ d : ↥(NodeLocalized.coeffSubring A (dat.K w)),
      NodeLocalized.redRestrict red (dat.K w) d = 0 ↔ ∃ d', d = ϖd w * d')
    (eK : Place k (modularFunctionFieldC k N) → ℕ)
    (u : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), ↥(R.nodeIntegersOver (dat.K w) w))
    (hu : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), IsUnit (u w hw) ∧
      (dat.coord w hw).x * (dat.coord w hw).y = R.nodeConst (dat.K w) w (ϖd w) ^ (dat.width w * eK w) * u w hw)
    (Ks : ↥W → IntermediateField ℚ (AlgebraicClosure ℚ)) [∀ w : ↥W, FiniteDimensional ℚ (Ks w)]
    (cs : ∀ w : ↥W, R.NodeCoordinates (Ks w) (w : Place k (modularFunctionFieldC k N)))
    (ϖ : ∀ w : ↥W, ↥(NodeLocalized.coeffSubring A (Ks w)))
    (hϖ : ∀ (w : ↥W) (d : ↥(NodeLocalized.coeffSubring A (Ks w))), NodeLocalized.redRestrict red (Ks w) d = 0 ↔ ∃ d', d = ϖ w * d')
    (hvalA : ∀ w : ↥W, R.ValueIntegralityLaw (w : Place k (modularFunctionFieldC k N)))
    (hxy : ∀ w : ↥W, ∃ (E : ℕ) (u : ↥(R.nodeIntegersOver (Ks w) (w : Place k (modularFunctionFieldC k N)))),
      1 ≤ E ∧ IsUnit u ∧ (cs w).x * (cs w).y = R.nodeConst (Ks w) (w : Place k (modularFunctionFieldC k N)) (ϖ w) ^ E * u)
    (e' : ℕ) (he' : 0 < e')
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hD0 : D.degree = 0)
    (hDstab : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • D = D)
    (hsupp : ∀ V ∈ D.support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)
    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ)
    (hdepth : ∀ (w : ↥W), ∀ V ∈ D.support, P.reduceFst V = (w : Place k (modularFunctionFieldC k N)) →
      (cs w).yDepth V ^ e' = A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ depth V)
    (hread : ∀ (s₀ : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N))
      (hs₀ : s₀ ∈ nodePairsOfPlaces (arithFrobC q k N) W),
      componentGroupProj
          (fun s : ↥(nodePairsOfPlaces (arithFrobC q k N) W) => e' * widthOfPlaces (arithFrobC q k N) W (placeWidthChar q N) s)
          (P.depthDual (arithFrobC q k N) W depth D +
            Divisor.degree (P.sndDiv D) • (((e' * placeWidthChar q N s₀.1 : ℕ) : ℤ) •
              crossingCoord (⟨s₀, hs₀⟩ : ↥(nodePairsOfPlaces (arithFrobC q k N) W)))) = 0) :
    ∃ a : ProlongationTuple.TwistVectorLevel (k := k) (N := N) W, dat.IsTwistOf a D := by
  classical
  haveI : PerfectField k := IsAlgClosed.perfectField k

  obtain ⟨hint, hintM⟩ :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable
      dat hKfix hdepthQ hdepthσ D hDstab

  obtain ⟨m, hm⟩ : ∃ m : Place k (modularFunctionFieldC k N) → ℕ → ℤ, m = fun w d => (dat.circleDeg D w d).num :=
    ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Place k (modularFunctionFieldC k N) → ℤ, M = fun w => (dat.depthMoment D w).num := ⟨_, rfl⟩
  obtain ⟨annDeg, hann⟩ : ∃ annDeg : Place k (modularFunctionFieldC k N) → ℤ,
    annDeg = fun w => ProlongationTuple.AnnulusDatumLevel.annulusDeg (P := P) D w := ⟨_, rfl⟩
  have hm_cast : ∀ w ∈ W, ∀ d : ℕ, (m w d : ℚ) = dat.circleDeg D w d := fun w hw d => by
    rw [hm]; exact Rat.coe_int_num_of_den_eq_one (hint w hw d)
  have hM_cast : ∀ w ∈ W, (M w : ℚ) = dat.depthMoment D w := fun w hw => by
    rw [hM]; exact Rat.coe_int_num_of_den_eq_one (hintM w hw)

  have hAnn : ∀ w ∈ W, ∀ V ∈ D.support.filter (fun V => P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V),
      0 < dat.depthQ V ∧ dat.depthQ V < dat.width w := by
    intro w hw V hV
    rw [Finset.mem_filter] at hV
    have h := hdepthQ w hw V hV.2.1 hV.2.2.1 hV.2.2.2
    exact ⟨h.1, h.2.1⟩
  have S1 : ∀ w ∈ W, ∑ d ∈ Finset.range (dat.width w + 1), m w d = annDeg w := by
    intro w hw
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [Finset.sum_congr rfl fun d _ => hm_cast w hw d, hann]
    unfold ProlongationTuple.AnnulusDatumLevel.circleDeg ProlongationTuple.AnnulusDatumLevel.annulusDeg
    push_cast
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun V hV => ?_
    rw [← Finset.mul_sum]
    have ht := hAnn w hw V hV
    have := tent_sum_eq_one (L := dat.width w) ht.1 ht.2
    unfold tent at this
    rw [this, mul_one]
  have S2 : ∀ w ∈ W, ∑ d ∈ Finset.range (dat.width w + 1), (d : ℤ) * m w d = M w := by
    intro w hw
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [Finset.sum_congr rfl fun d _ => by rw [hm_cast w hw d], hM_cast w hw]
    unfold ProlongationTuple.AnnulusDatumLevel.circleDeg ProlongationTuple.AnnulusDatumLevel.depthMoment
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun V hV => ?_
    have ht := hAnn w hw V hV
    have := tent_sum_mul_eq (L := dat.width w) ht.1 ht.2
    unfold tent at this
    calc ∑ d ∈ Finset.range (dat.width w + 1), (d : ℚ) * ((D V : ℚ) * max 0 (1 - |dat.depthQ V - d|))
        = (D V : ℚ) * ∑ d ∈ Finset.range (dat.width w + 1), (d : ℚ) * max 0 (1 - |dat.depthQ V - d|) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun d _ => by ring
      _ = (D V : ℚ) * dat.depthQ V := by rw [this]

  have hT : ∀ w ∈ W, (P.depthDiv depth D) w = (e' : ℤ) * M w := by
    intro w hw

    have e1 : (P.depthDiv depth D) w = ∑ V ∈ D.support with P.reduceFst V = w, D V * (depth V : ℤ) := by
      unfold PlaceSpecialization.depthDiv
      rw [Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
      exact Finset.sum_congr rfl fun V _ => by rw [Finsupp.single_apply]

    have e2 : (D.support.filter fun V => P.reduceFst V = w)
        = D.support.filter fun V => P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V := by
      ext V
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hV, hVw⟩
        have hns : ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V) := fun h =>
          reduceFst_notMem_of_isStrict (P := P) hqN hW V h (hVw ▸ hw)
        exact ⟨hV, hVw, fun h => hns (Or.inl h), fun h => hns (Or.inr h)⟩
      · rintro ⟨hV, hVw, -, -⟩; exact ⟨hV, hVw⟩
    rw [e1, e2]

    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [hM_cast w hw]
    unfold ProlongationTuple.AnnulusDatumLevel.depthMoment
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun V hV => ?_
    rw [Finset.mem_filter] at hV
    obtain ⟨hVs, hVw, hV₁, hV₂⟩ := hV
    have hstep1 := depthQ_eq_div R hqN hW hR hRL hNV hO dat hK hdepthQ ϖd eK u hu Ks cs ϖ hvalA hxy e' he' depth
      ⟨w, hw⟩ V hVw hV₁ hV₂ (hdepth ⟨w, hw⟩ V hVs hVw)
    rw [hstep1]
    have he0 : (e' : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr he'.ne'
    field_simp

  obtain ⟨w₀, hw₀⟩ : W.Nonempty := by
    obtain ⟨w, hw⟩ := ModularCurve.ssPlaces_nonempty q N hqN k
    exact ⟨w, (hW w).mpr hw⟩
  have hunpack : ∃ (γ : Place k (modularFunctionFieldC k N) → ℤ) (κ' : ℤ),
      (∑ w ∈ W, γ w = 0) ∧
      ∀ w ∈ W, M w + (if w = w₀ then Divisor.degree (P.sndDiv D) * (dat.width w₀ : ℤ) else 0) = (dat.width w : ℤ) * γ w + κ' := by

    have hs₀ : smulNodePair (arithFrobC q k N) w₀ ∈ nodePairsOfPlaces (arithFrobC q k N) W := smulNodePair_mem_nodePairsOfPlaces _ hw₀
    obtain ⟨e, he⟩ : ∃ e : ↥(nodePairsOfPlaces (arithFrobC q k N) W) → ℕ,
        e = fun s => e' * widthOfPlaces (arithFrobC q k N) W (placeWidthChar q N) s := ⟨_, rfl⟩

    obtain ⟨α, hα⟩ : ∃ α : ↥(nodePairsOfPlaces (arithFrobC q k N) W) → ℤ,
        α = fun (s : ↥(nodePairsOfPlaces (arithFrobC q k N) W)) => P.depthDiv depth D s.1.1 +
          (if s = (⟨smulNodePair (arithFrobC q k N) w₀, hs₀⟩ : ↥(nodePairsOfPlaces (arithFrobC q k N) W)) then Divisor.degree (P.sndDiv D) * ((e' * placeWidthChar q N w₀ : ℕ) : ℤ) else 0) := ⟨_, rfl⟩
    have hfun : (∑ s, α s • crossingCoord s : Module.Dual ℤ (characterLattice ↥(nodePairsOfPlaces (arithFrobC q k N) W)))
        = P.depthDual (arithFrobC q k N) W depth D + Divisor.degree (P.sndDiv D) • (((e' * placeWidthChar q N w₀ : ℕ) : ℤ) • crossingCoord (⟨smulNodePair (arithFrobC q k N) w₀, hs₀⟩ : ↥(nodePairsOfPlaces (arithFrobC q k N) W))) := by
      unfold PlaceSpecialization.depthDual
      rw [hα]
      simp only [add_smul, Finset.sum_add_distrib, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        smul_smul]
    have hmem : (∑ s, α s • crossingCoord s : Module.Dual ℤ (characterLattice ↥(nodePairsOfPlaces (arithFrobC q k N) W)))
        ∈ LinearMap.range (gramMap e) := by
      rw [hfun, he]
      exact (Submodule.Quotient.mk_eq_zero _).mp (hread _ hs₀)
    obtain ⟨γS, κ, hγS0, hγS⟩ := exists_coeff_of_mem_range_gramMap e α hmem
    have hcoef : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
        (e' : ℤ) * M w + (if w = w₀ then Divisor.degree (P.sndDiv D) * ((e' * placeWidthChar q N w₀ : ℕ) : ℤ) else 0)
          = ((e' * placeWidthChar q N w : ℕ) : ℤ) * γS ⟨smulNodePair (arithFrobC q k N) w, smulNodePair_mem_nodePairsOfPlaces _ hw⟩ + κ := by
      intro w hw
      have h1 := hγS ⟨smulNodePair (arithFrobC q k N) w, smulNodePair_mem_nodePairsOfPlaces _ hw⟩
      rw [hα, he] at h1
      simp only [widthOfPlaces_apply] at h1
      have hsb_iff : (⟨smulNodePair (arithFrobC q k N) w, smulNodePair_mem_nodePairsOfPlaces _ hw⟩ : ↥(nodePairsOfPlaces (arithFrobC q k N) W))
          = (⟨smulNodePair (arithFrobC q k N) w₀, hs₀⟩ : ↥(nodePairsOfPlaces (arithFrobC q k N) W)) ↔ w = w₀ := by
        rw [Subtype.mk.injEq]
        exact ⟨fun h => smulNodePair_injective _ h, fun h => by subst h; rfl⟩
      rw [show (⟨smulNodePair (arithFrobC q k N) w, smulNodePair_mem_nodePairsOfPlaces _ hw⟩ : ↥(nodePairsOfPlaces (arithFrobC q k N) W)).1.1 = w from rfl, hT w hw] at h1
      by_cases hw0 : w = w₀
      · rw [if_pos (hsb_iff.mpr hw0)] at h1; rw [if_pos hw0]; exact h1
      · rw [if_neg (fun h => hw0 (hsb_iff.mp h))] at h1; rw [if_neg hw0]; simpa using h1

    have hdvd : (e' : ℤ) ∣ κ := by
      have h1 := hcoef w₀ hw₀
      rw [if_pos rfl] at h1
      have : κ = (e' : ℤ) * M w₀ + Divisor.degree (P.sndDiv D) * ((e' * placeWidthChar q N w₀ : ℕ) : ℤ)
          - ((e' * placeWidthChar q N w₀ : ℕ) : ℤ) * γS ⟨smulNodePair (arithFrobC q k N) w₀, smulNodePair_mem_nodePairsOfPlaces _ hw₀⟩ := by
        linarith
      rw [this]
      push_cast
      refine Dvd.intro (M w₀ + Divisor.degree (P.sndDiv D) * (placeWidthChar q N w₀ : ℤ)
        - (placeWidthChar q N w₀ : ℤ) * γS ⟨smulNodePair (arithFrobC q k N) w₀, smulNodePair_mem_nodePairsOfPlaces _ hw₀⟩) ?_
      ring
    obtain ⟨κ', hκ'⟩ := hdvd

    refine ⟨fun w => if hw : w ∈ W then γS ⟨smulNodePair (arithFrobC q k N) w, smulNodePair_mem_nodePairsOfPlaces _ hw⟩ else 0,
      κ', ?_, ?_⟩
    ·
      rw [← hγS0, ← Finset.sum_attach W, ← Fintype.sum_equiv (nodeEquivOfPlaces (arithFrobC q k N) W) _ γS (fun w => rfl)]
      refine Finset.sum_congr rfl fun w _ => ?_
      beta_reduce
      rw [dif_pos w.2]
      rfl
    · intro w hw
      dsimp only
      rw [dif_pos hw]
      have h1 := hcoef w hw
      rw [hκ'] at h1
      rw [hwidthc w hw, hwidthc w₀ hw₀]
      have he0 : (e' : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr he'.ne'
      apply mul_left_cancel₀ he0
      by_cases hw0 : w = w₀
      · subst hw0
        rw [if_pos rfl] at h1 ⊢
        push_cast at h1 ⊢
        linarith
      · rw [if_neg hw0] at h1 ⊢
        push_cast at h1 ⊢
        linarith
  obtain ⟨γ, κ', hγ0, hγ⟩ := hunpack

  obtain ⟨s, hs⟩ : ∃ s : Place k (modularFunctionFieldC k N) → ℤ,
      s = fun w => annDeg w - m w 0 - γ w + (if w = w₀ then Divisor.degree (P.sndDiv D) else 0) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : Place k (modularFunctionFieldC k N) → ℕ → ℤ,
      v = fun w (d : ℕ) => (d : ℤ) * s w - ∑ j ∈ Finset.range d, ((d : ℤ) - j) * m w j + (d : ℤ) * m w 0 := ⟨_, rfl⟩

  have hv0 : ∀ w, v w 0 = 0 := fun w => by rw [hv]; simp
  have hv1 : ∀ w, v w 1 = s w := fun w => by rw [hv]; simp
  have hstep : ∀ w (d : ℕ), v w (d + 1) - v w d = s w - ∑ j ∈ Finset.range (d + 1), m w j + m w 0 := by
    intro w d
    rw [hv]
    simp only
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have e1 : ∑ j ∈ Finset.range d, (((d + 1 : ℕ) : ℤ) - j) * m w j
        = ∑ j ∈ Finset.range d, ((d : ℤ) - j) * m w j + ∑ j ∈ Finset.range d, m w j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by push_cast; ring
    rw [e1]
    push_cast
    ring
  have hsecond : ∀ w (d : ℕ), 1 ≤ d → v w (d - 1) - 2 * v w d + v w (d + 1) = -m w d := by
    intro w d hd
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have h1 := hstep w (d' + 1)
    have h2 := hstep w d'
    rw [Nat.add_sub_cancel]
    rw [Finset.sum_range_succ] at h1
    linarith

  have hL1 : ∀ w ∈ W, 1 ≤ dat.width w := fun w hw => by
    rw [hwidthc w hw]; exact ModularCurve.one_le_placeWidthChar_of_mem_ssPlaces hqN ((hW w).mp hw)

  have hvL : ∀ w ∈ W, v w (dat.width w) = κ' := by
    intro w hw
    have hS1 := S1 w hw
    have hS2 := S2 w hw
    have hγw := hγ w hw
    rw [Finset.sum_range_succ] at hS1 hS2
    rw [hv]
    simp only
    have e1 : ∑ j ∈ Finset.range (dat.width w), ((dat.width w : ℤ) - j) * m w j
        = (dat.width w : ℤ) * ∑ j ∈ Finset.range (dat.width w), m w j - ∑ j ∈ Finset.range (dat.width w), (j : ℤ) * m w j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1, hs]
    simp only
    by_cases hw0 : w = w₀
    · subst hw0
      simp only [if_true] at hγw ⊢
      nlinarith [hS1, hS2, hγw]
    · simp only [if_neg hw0] at hγw ⊢
      nlinarith [hS1, hS2, hγw]

  have hchain : ∀ w ∈ W, ∀ d : ℕ, d ≤ dat.width w →
      dat.chainVal (⟨0, κ', v⟩ : ProlongationTuple.TwistVectorLevel (k := k) (N := N) W) w d = v w d := by
    intro w hw d hd
    unfold ProlongationTuple.AnnulusDatumLevel.chainVal
    by_cases hd0 : d = 0
    · subst hd0; simp [hv0]
    · rw [if_neg hd0]
      by_cases hLd : dat.width w ≤ d
      · rw [if_pos hLd]
        have : d = dat.width w := le_antisymm hd hLd
        rw [this, hvL w hw]
      · rw [if_neg hLd]
  refine ⟨⟨0, κ', v⟩, ?_, ?_, ?_⟩
  ·
    have hend : ∀ w ∈ W, dat.endOrderFst ⟨0, κ', v⟩ D w = annDeg w - γ w + (if w = w₀ then Divisor.degree (P.sndDiv D) else 0) := by
      intro w hw
      unfold ProlongationTuple.AnnulusDatumLevel.endOrderFst ProlongationTuple.AnnulusDatumLevel.endSlopeFst
        ProlongationTuple.AnnulusDatumLevel.endShareFst
      rw [hchain w hw 1 (hL1 w hw), hchain w hw 0 (Nat.zero_le _), hv1, hv0, if_pos (hint w hw 0)]
      rw [hs, hm]
      simp only
      ring
    rw [Finset.sum_congr rfl hend, Finset.sum_add_distrib, Finset.sum_sub_distrib, hγ0, Finset.sum_ite_eq' W w₀, if_pos hw₀]
    have hpart := degree_eq_fst_add_snd_add_sum_annulusDeg (P := P) hqN hW D hsupp
    rw [hD0] at hpart
    have hann' : ∑ w ∈ W, annDeg w = ∑ w ∈ W, ProlongationTuple.AnnulusDatumLevel.annulusDeg (P := P) D w := by
      rw [hann]
    linarith
  ·
    have hend : ∀ w ∈ W, dat.endOrderSnd ⟨0, κ', v⟩ D w = γ w - (if w = w₀ then Divisor.degree (P.sndDiv D) else 0) := by
      intro w hw
      unfold ProlongationTuple.AnnulusDatumLevel.endOrderSnd ProlongationTuple.AnnulusDatumLevel.endSlopeSnd
        ProlongationTuple.AnnulusDatumLevel.endShareSnd
      have hLw := hL1 w hw
      rw [hchain w hw (dat.width w - 1) (by omega), hchain w hw (dat.width w) le_rfl,
        if_pos (hint w hw _)]
      have hst := hstep w (dat.width w - 1)
      have hsub : dat.width w - 1 + 1 = dat.width w := by omega
      rw [hsub] at hst
      have hS1 := S1 w hw
      rw [← hsub, Finset.sum_range_succ, hsub] at hS1
      rw [show (dat.circleDeg D w (dat.width w)).num = m w (dat.width w) by rw [hm]]
      have : v w (dat.width w - 1) - v w (dat.width w) = -(s w - ∑ j ∈ Finset.range (dat.width w), m w j + m w 0) := by
        linarith
      rw [this, hs]
      simp only
      linarith
    rw [Finset.sum_congr rfl hend, Finset.sum_sub_distrib, hγ0, Finset.sum_ite_eq' W w₀, if_pos hw₀]
    ring
  ·
    intro w hw d hd1 hdL
    rw [hchain w hw (d - 1) (by omega), hchain w hw d (by omega), hchain w hw (d + 1) (by omega),
      hsecond w d hd1, ← hm_cast w hw d]
    push_cast
    ring

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_exists_isTwistOf_of_componentGroupProj_depthDual_eq_zero_of_inertiaStable_of_laws
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_exists_isTwistOf_of_componentGroupProj_depthDual_eq_zero_of_inertiaStable_of_laws (solution)
