-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_annulusDatumLevel_laws
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/eab0cb4b-e087-5e03-af3c-af66bc229419

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_AnnulusSpecializationLevel
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_depthQ_cleared_law_and_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeUnit_lam_mu_hasValue_of_ord_eq_one
import Theorems.Thm_ModularCurve_exists_unifFst_unifSnd_correctionDivisor_laws_of_ssPlaces
import Theorems.Thm_ValuationSubring_ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces_univ
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_reduceFst_eq_and_smul_eq_self_and_yDepth_eq_pow_of_orderLawFixed
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictFst_or_isStrictSnd_iff
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_nodeCoordinates_presentation_of_orderLawFixed
import Theorems.Thm_ModularCurve_sum_ord_jGeomGen_sub_eq_dedekindPsi
import Theorems.Thm_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidthChar_two_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidthChar_three_of_mem_ssPlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_annulusDatumLevel_laws
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ValuationSubring.instIsAlgClosedResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.coe_nodeEquiv_symm_apply"
p2m_attr_erase "simp" "ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace AnnLawsN

theorem one_le_placeWidthChar_of_mem_ssPlaces
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (hqN : ¬ q ∣ N) {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ ssPlaces q N k) :
    1 ≤ placeWidthChar q N w := by
  have hss : IsSupersingularPlace q N k w := hw
  have hpos : 0 < placeRamificationJ N w := by
    have hord := ord_sub_evalAt_pos_of_isRational hss.1 hss.2.1.1 (jGeomGen_sub_algebraMap_ne_zero k N _)
    unfold placeRamificationJ
    omega
  have hdvd : placeRamificationJ N w ∣ jWidthChar q (w.evalAt (jGeomGen k N)) := by
    by_cases h2 : q = 2
    · subst h2
      exact placeRamificationJ_dvd_jWidthChar_two_of_mem_ssPlaces hqN hw
    by_cases h3 : q = 3
    · subst h3
      exact placeRamificationJ_dvd_jWidthChar_three_of_mem_ssPlaces hqN hw
    have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
    have hq4 : q ≠ 4 := fun h => by
      have : (4 : ℕ).Prime := h ▸ (Fact.out : q.Prime)
      exact absurd this (by decide)
    have hq5 : 5 ≤ q := by omega
    rw [jWidthChar_of_ne h2 h3]
    exact placeRamificationJ_dvd_jWidth_of_mem_ssPlaces hq5 hqN hw
  rw [placeWidthChar_eq_div]
  exact Nat.div_pos (Nat.le_of_dvd (jWidthChar_pos q _) hdvd) hpos

end AnnLawsN

open AnnLawsN in
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
    (hO : R.OrderLawFixed) (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w) :
    ∃ dat : R.AnnulusDatumLevel W,
      (∀ w ∈ W, 1 ≤ dat.width w) ∧ (∀ w ∈ W, dat.width w = placeWidthChar q N w) ∧
      (∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
        (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
        P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
          0 < dat.depthQ V ∧ dat.depthQ V < dat.width w ∧ (dat.coord w hw).yDepth V ^ (dat.depthQ V).den =
            A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (dat.depthQ V).num.toNat) ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        dat.depthQ (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) = dat.depthQ V) ∧
      (∀ w ∈ W, 2 ≤ dat.width w → ∃ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V ∧
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧ dat.depthQ V = 1) ∧
      (∀ w ∈ W,
        ((∀ v, (Finsupp.single w (1 : ℤ) + dat.corrFst w) v = v.ord (dat.unifFst w)) ∧ (∀ v ∈ W, dat.corrFst w v = 0) ∧
          Divisor.degree (dat.corrFst w) = -1) ∧
        ((∀ v, (Finsupp.single (arithFrobC q k N • w) (1 : ℤ) + dat.corrSnd w) v = v.ord (dat.unifSnd w)) ∧
          (∀ v ∈ W, dat.corrSnd w v = 0) ∧ Divisor.degree (dat.corrSnd w) = -1)) ∧
      (∀ w ∈ W, ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ dat.K w, σ z = z) ∧
      (∀ w : Place k (modularFunctionFieldC k N), FiniteDimensional ℚ ↥(dat.K w)) ∧
      ∃ (ϖ : ∀ w : Place k (modularFunctionFieldC k N), ↥(NodeLocalized.coeffSubring A (dat.K w)))
        (eK : Place k (modularFunctionFieldC k N) → ℕ)
        (ε : ∀ w : Place k (modularFunctionFieldC k N), ↥(NodeLocalized.coeffSubring A (dat.K w)))
        (u : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), ↥(R.nodeIntegersOver (dat.K w) w)),
        (∀ w ∈ W, ∀ d : ↥(NodeLocalized.coeffSubring A (dat.K w)),
      NodeLocalized.redRestrict red (dat.K w) d = 0 ↔ ∃ d', d = ϖ w * d') ∧ (∀ w ∈ W, 1 ≤ eK w) ∧ (∀ w ∈ W, IsUnit (ε w)) ∧
        (∀ w ∈ W, ((q : ℕ) : ↥(NodeLocalized.coeffSubring A (dat.K w))) = ϖ w ^ eK w * ε w) ∧
        (∀ w ∈ W, NodeLocalized.redRestrict red (dat.K w) (ε w) = 1) ∧
        (∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), IsUnit (u w hw) ∧
        (dat.coord w hw).x * (dat.coord w hw).y = R.nodeConst (dat.K w) w (ϖ w) ^ (dat.width w * eK w) * u w hw) ∧
        (∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
        (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x, (dat.coord w hw).y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver (dat.K w) w), M.IsMaximal →
          M = Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x, (dat.coord w hw).y}) ∧
        (∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
        (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x}).IsPrime ∧
        (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).y}).IsPrime ∧
        (dat.coord w hw).y ∉ Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x} ∧
        (dat.coord w hw).x ∉ Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).y}) ∧
        (∀ w ∈ W, IsNoetherianRing ↥(R.nodeIntegersOver (dat.K w) w)) ∧
        (∀ w ∈ W, ∀ g : ↥(R.nodeIntegersOver (dat.K w) w),
        ∃ o : ↥(NodeLocalized.coeffSubring A (dat.K w)), ¬ IsUnit (g - R.nodeConst (dat.K w) w o)) ∧
        (∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨(u w hw : ↥(modularFunctionFieldBar (N * q))), (u w hw).2.1⟩) ((dat.u0 w : kˣ) : k)) ∧
        (∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨((dat.coord w hw).y : ↥(modularFunctionFieldBar (N * q))), (dat.coord w hw).y.2.1⟩
        / dat.unifFst w) ((dat.lam w : kˣ) : k)) ∧
        (∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      (arithFrobC q k N • w).HasValue
        (R.nodeResidue₂ w ⟨((dat.coord w hw).x : ↥(modularFunctionFieldBar (N * q))), (dat.coord w hw).x.2.1⟩
          / dat.unifSnd w) ((dat.mu w : kˣ) : k)) := by
  classical
  have hW' : ∀ w ∈ W, w ∈ ssPlaces q N k := fun w hw => (hW w).mp hw
  have hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A :=
    fun c => ValuationSubring.ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP A q red c

  have hNk : ((N : ℕ) : k) ≠ 0 := fun h => hqN ((CharP.cast_eq_zero_iff k q N).mp h)
  have hsep := ModularCurve.isSeparable_jqNModC_of_natCast_ne_zero k N hNk
  have hpsi : 0 < dedekindPsi N := by
    have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    unfold dedekindPsi
    refine lt_of_lt_of_le (by rwa [Nat.div_one] : 0 < N / 1) (Finset.single_le_sum (a := 1) (fun _ _ => Nat.zero_le _) ?_)
    simp [NeZero.ne N]
  have hplace : ∀ a : k, ∃ w : Place k (modularFunctionFieldC k N),
      0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a) := by
    intro a
    have hfin := ModularCurve.finite_setOf_ord_jGeomGen_sub_pos k N hsep a
    have hsum := ModularCurve.sum_ord_jGeomGen_sub_eq_dedekindPsi q N hqN k hsep a hfin.toFinset
      (fun w => by rw [Set.Finite.mem_toFinset]; rfl)
    by_contra hno
    have hzero : ∑ w ∈ hfin.toFinset, w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a) = 0 :=
      Finset.sum_eq_zero fun w hw => absurd ((Set.Finite.mem_toFinset hfin).mp hw) (fun h => hno ⟨w, h⟩)
    rw [hzero] at hsum
    omega
  choose pl hpl using hplace
  have hinj : Function.Injective pl := by
    intro a b hab
    by_contra hne
    have hja := jGeomGen_sub_algebraMap_ne_zero k N a
    have hjb := jGeomGen_sub_algebraMap_ne_zero k N b
    have ha := hpl a
    have hb := hpl b
    rw [← hab] at hb
    have hmema := (pl a).mem_of_ord_nonneg hja ha.le
    have hmemb := (pl a).mem_of_ord_nonneg hjb hb.le
    have hma := ((pl a).mem_maximalIdeal_iff_ord_pos hja hmema).mpr ha
    have hmb := ((pl a).mem_maximalIdeal_iff_ord_pos hjb hmemb).mpr hb
    have hdiff := Ideal.sub_mem _ hmb hma
    have heq : (⟨jGeomGen k N - algebraMap k (modularFunctionFieldC k N) b, hmemb⟩ : (pl a).toValuationSubring) -
        ⟨jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a, hmema⟩ =
        algebraMap k (pl a).toValuationSubring (a - b) := by
      apply Subtype.ext
      rw [Place.coe_algebraMap, map_sub]
      push_cast
      ring
    rw [heq] at hdiff
    exact (IsLocalRing.mem_maximalIdeal _).mp hdiff ((IsUnit.mk0 _ (sub_ne_zero.mpr hne)).map _)
  obtain ⟨S, hScard⟩ := Infinite.exists_subset_card_eq k (2 * genusFF k ↥(modularFunctionFieldC k N) + 2 + W.card)
  let U : Finset (Place k (modularFunctionFieldC k N)) := S.image pl \ W
  have hUW : Disjoint U W := Finset.sdiff_disjoint
  have hU : 2 * genusFF k ↥(modularFunctionFieldC k N) + 2 ≤ U.card := by
    have h1 : (S.image pl).card = S.card := Finset.card_image_of_injective S hinj
    have h2 := Finset.le_card_sdiff W (S.image pl)
    show _ ≤ (S.image pl \ W).card
    omega

  have hall : ∀ w : Place k (modularFunctionFieldC k N), ∃ K₀ : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ ↥K₀ ∧ ∀ hw : w ∈ W,
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ K₀, σ z = z) ∧
      (∀ d : ↥(NodeLocalized.coeffSubring A K₀),
        NodeLocalized.redRestrict red K₀ d = 0 ↔ ∃ d', d = ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) * d') ∧
      ∃ (c : R.NodeCoordinates K₀ w) (u : ↥(R.nodeIntegersOver K₀ w)),
        (IsUnit u ∧
          c.x * c.y = R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) ^ placeWidthChar q N w * u) ∧
        ((Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), c.x, c.y}).IsMaximal ∧
          ∀ M : Ideal ↥(R.nodeIntegersOver K₀ w), M.IsMaximal →
            M = Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), c.x, c.y}) ∧
        ((Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), c.x}).IsPrime ∧
          (Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), c.y}).IsPrime ∧
          c.y ∉ Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), c.x} ∧
          c.x ∉ Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), c.y}) ∧
        IsNoetherianRing ↥(R.nodeIntegersOver K₀ w) ∧
        (∀ g : ↥(R.nodeIntegersOver K₀ w),
          ∃ o : ↥(NodeLocalized.coeffSubring A K₀), ¬ IsUnit (g - R.nodeConst K₀ w o)) := by
    intro w
    by_cases hw : w ∈ W
    · obtain ⟨K₀, fd, h1, h2, hrest⟩ :=
        ModularCurve.PlaceSpecialization.ProlongationTuple.exists_inertiaFixed_nodeCoordinates_presentation_of_orderLawFixed
          R hqN hker hR hO W hW' hRL hNV w hw
      exact ⟨K₀, fd, fun _ => ⟨h1, h2, hrest⟩⟩
    · exact ⟨⊥, inferInstance, fun h => absurd h hw⟩
  choose Kf hfd hrest using hall
  haveI hKinst : ∀ w : Place k (modularFunctionFieldC k N), FiniteDimensional ℚ ↥(Kf w) := hfd
  have hKfix : ∀ w ∈ W, ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ Kf w, σ z = z := fun w hw => (hrest w hw).1
  have hϖ₀ : ∀ w ∈ W, ∀ d : ↥(NodeLocalized.coeffSubring A (Kf w)),
      NodeLocalized.redRestrict red (Kf w) d = 0 ↔ ∃ d', d = ((q : ℕ) : ↥(NodeLocalized.coeffSubring A (Kf w))) * d' :=
    fun w hw => (hrest w hw).2.1
  choose c u hcu using fun w (hw : w ∈ W) => (hrest w hw).2.2
  let ϖf : ∀ w : Place k (modularFunctionFieldC k N), ↥(NodeLocalized.coeffSubring A (Kf w)) :=
    fun w => ((q : ℕ) : ↥(NodeLocalized.coeffSubring A (Kf w)))
  let εf : ∀ w : Place k (modularFunctionFieldC k N), ↥(NodeLocalized.coeffSubring A (Kf w)) := fun _ => 1
  let eKf : Place k (modularFunctionFieldC k N) → ℕ := fun _ => 1
  let widthf : Place k (modularFunctionFieldC k N) → ℕ := fun w => placeWidthChar q N w
  have heK : ∀ w ∈ W, 1 ≤ eKf w := fun _ _ => le_rfl
  have hε : ∀ w ∈ W, IsUnit (εf w) := fun _ _ => isUnit_one
  have hqϖ : ∀ w ∈ W, ((q : ℕ) : ↥(NodeLocalized.coeffSubring A (Kf w))) = ϖf w ^ eKf w * εf w := fun w _ => by
    show ((q : ℕ) : ↥(NodeLocalized.coeffSubring A (Kf w))) = ((q : ℕ) : ↥(NodeLocalized.coeffSubring A (Kf w))) ^ 1 * 1
    rw [pow_one, mul_one]
  have hu : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), IsUnit (u w hw) ∧
      (c w hw).x * (c w hw).y = R.nodeConst (Kf w) w (ϖf w) ^ (widthf w * eKf w) * u w hw :=
    fun w hw => ⟨(hcu w hw).1.1, by
      show (c w hw).x * (c w hw).y = R.nodeConst (Kf w) w (ϖf w) ^ (placeWidthChar q N w * 1) * u w hw
      rw [mul_one]
      exact (hcu w hw).1.2⟩

  obtain ⟨depthQ, hdepthQ, hdepthσ⟩ :=
    ProlongationTuple.exists_depthQ_cleared_law_and_forall_inertia_smul_eq P hqN hW' R hR hRL hNV hO hVI
      Kf hKfix c widthf ϖf eKf heK εf hε hqϖ u hu

  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hvq0 : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by rwa [ne_eq, map_eq_zero]
  have hvq1 : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1 := by

    have hmem : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A := natCast_mem A q
    have hle : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ≤ 1 := (A.valuation_le_one_iff _).mpr hmem
    rcases hle.lt_or_eq with h | h
    · exact h
    · exfalso
      have hu : IsUnit ((⟨((q : ℕ) : AlgebraicClosure ℚ), hmem⟩ : A)) := (A.valuation_eq_one_iff _).mpr h
      have h2 := hu.map red
      have h3 : red ⟨((q : ℕ) : AlgebraicClosure ℚ), hmem⟩ = ((q : ℕ) : k) := by
        rw [← map_natCast red q]
        congr 1
      rw [h3, CharP.cast_eq_zero k q] at h2
      exact not_isUnit_zero h2
  have hnotstrict : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V ∈ W →
      ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V := fun V hVW =>
    not_or.mp (mt (ModularCurve.PlaceSpecialization.isStrictFst_or_isStrictSnd_iff P V).mp (not_not.mpr
      (ModularCurve.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k N hqN data hKr _ (hW' _ hVW))))
  have hD1 : ∀ w ∈ W, 2 ≤ widthf w → ∃ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧ depthQ V = 1 := by
    intro w hw h2
    have hdE : A.valuation (((ϖf w : ↥(NodeLocalized.coeffSubring A (Kf w))) : AlgebraicClosure ℚ)) ^ (widthf w * eKf w) <
        A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ 1 := by
      show A.valuation ((((q : ℕ) : ↥(NodeLocalized.coeffSubring A (Kf w))) : AlgebraicClosure ℚ)) ^ (placeWidthChar q N w * 1) < _
      rw [mul_one, pow_one]
      have hcoe : ((((q : ℕ) : ↥(NodeLocalized.coeffSubring A (Kf w))) : AlgebraicClosure ℚ)) = ((q : ℕ) : AlgebraicClosure ℚ) := by
        simp
      rw [hcoe]
      have h2' : 2 ≤ placeWidthChar q N w := h2
      exact pow_lt_self_of_lt_one₀ (zero_lt_iff.mpr hvq0) hvq1 (by omega)
    obtain ⟨V, hVw, hVfix, hVy⟩ :=
      ProlongationTuple.exists_reduceFst_eq_and_smul_eq_self_and_yDepth_eq_pow_of_orderLawFixed R hqN hR hO W hW' hRL hNV (Kf w) w hw (hVI w hw)
        (ϖf w) (c w hw) (widthf w * eKf w) (u w hw) (hu w hw).1 (hu w hw).2 1 one_pos hdE
    obtain ⟨hns1, hns2⟩ := hnotstrict V (hVw ▸ hw)
    refine ⟨V, hVw, hns1, hns2, hVfix, ?_⟩

    obtain ⟨hpos, -, hlaw⟩ := hdepthQ w hw V hVw hns1 hns2
    rw [hVy, pow_one] at hlaw
    have hden : (depthQ V).den = (depthQ V).num.toNat :=
      (pow_right_strictAnti₀ (zero_lt_iff.mpr hvq0) hvq1).injective hlaw
    have hnum : 0 < (depthQ V).num := Rat.num_pos.mpr hpos
    have hnumden : ((depthQ V).num : ℚ) = ((depthQ V).den : ℚ) := by
      have h1 : (((depthQ V).num.toNat : ℕ) : ℤ) = (depthQ V).num := Int.toNat_of_nonneg hnum.le
      rw [← hden] at h1
      exact_mod_cast h1.symm
    have h2 := Rat.num_div_den (depthQ V)
    rw [hnumden, div_self (by exact_mod_cast (depthQ V).den_nz)] at h2
    exact h2.symm

  have hφW : ∀ w ∈ W, arithFrobC q k N • w ∈ W := fun w hw =>
    (hW _).mpr (ModularCurve.arithFrobC_smul_mem_ssPlaces_univ q N k _ (hW' w hw))
  have hUφ : ∀ w ∈ W, arithFrobC q k N • w ∉ U := fun w hw h => Finset.disjoint_left.mp hUW h (hφW w hw)
  obtain ⟨unifFst, unifSnd, corrFst, corrSnd, hunif⟩ :=
    ModularCurve.exists_unifFst_unifSnd_correctionDivisor_laws_of_ssPlaces q k N hqN W hW' U hUW hUφ hU

  have hunifFst : ∀ w ∈ W, w.ord (unifFst w) = 1 := fun w hw => by
    have h1 := (hunif w hw).1.1 w
    rw [Finsupp.add_apply, Finsupp.single_eq_same, (hunif w hw).1.2.1 w hw, add_zero] at h1
    exact_mod_cast h1.symm
  have hunifSnd : ∀ w ∈ W, (arithFrobC q k N • w).ord (unifSnd w) = 1 := fun w hw => by
    have h1 := (hunif w hw).2.1 (arithFrobC q k N • w)
    rw [Finsupp.add_apply, Finsupp.single_eq_same, (hunif w hw).2.2.1 _ (hφW w hw), add_zero] at h1
    exact_mod_cast h1.symm

  obtain ⟨u0, lam, mu, hu0, hlam, hmu⟩ :=
    ProlongationTuple.exists_nodeUnit_lam_mu_hasValue_of_ord_eq_one P hW' R hRL Kf c u (fun w hw => (hcu w hw).1.1)
      unifFst unifSnd hunifFst hunifSnd

  let dat : R.AnnulusDatumLevel W :=
    { K := Kf, coord := c, width := widthf, depthQ := depthQ, unifFst := unifFst, unifSnd := unifSnd,
      corrFst := corrFst, corrSnd := corrSnd, u0 := u0, lam := lam, mu := mu }
  refine ⟨dat, fun w hw => one_le_placeWidthChar_of_mem_ssPlaces hqN (hW' w hw), fun w _ => rfl, hdepthQ, hdepthσ, hD1, hunif, hKfix, hKinst,
    ϖf, eKf, εf, u, hϖ₀, heK, hε, hqϖ, fun w _ => map_one _, hu, fun w hw => (hcu w hw).2.1,
    fun w hw => (hcu w hw).2.2.1, fun w hw => (hcu w hw).2.2.2.1, fun w hw => (hcu w hw).2.2.2.2, hu0, hlam, hmu⟩

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_annulusDatumLevel_laws
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_annulusDatumLevel_laws (solution)
