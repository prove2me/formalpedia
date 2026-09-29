-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_isGoodDiv_ord_residueFst_eq_neg_lcm_div_widthChar_of_orderLawFixed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/325fe315-5d64-5911-926e-dfb97ef9b1f5

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_and_forall_ord_eq_zero
import Theorems.Thm_ModularCurve_finite_setOf_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_seedDatum_of_nodeCoordinates_nodeEquation
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_nodeCoordinates_presentation_of_orderLawFixed
import Theorems.Thm_ValuationSubring_ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_isGoodDiv_ord_residueFst_eq_neg_lcm_div_widthChar_of_orderLawFixed
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ValuationSubring.instIsAlgClosedResidueField ModularCurve.numberField_of_finiteDimensional ModularCurve.instIsElliptic_tateBase GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero"
p2m_attr_erase "instance" "ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom"
p2m_attr_erase "simp" "ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl"
p2m_attr_erase "simp" "ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.crossingCoord_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.symPoly_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst"
p2m_attr_erase "simp" "ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec"
p2m_attr_erase "simp" "MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"
set_option Elab.async false
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false
open AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence arithFrobC placeWidthChar smulNodePair nodePairsOfPlaces mem_nodePairsOfPlaces_iff widthOfPlaces widthOfPlaces_apply ssPlaces PlaceSpecialization.ProlongationTuple PlaceSpecialization.ProlongationTuple.nodeResidue₁_apply NodeLocalized.coeffSubring PlaceSpecialization.ProlongationTuple.exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_and_forall_ord_eq_zero finite_setOf_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self PlaceSpecialization.ProlongationTuple.exists_seedDatum_of_nodeCoordinates_nodeEquation"
namespace NwRed
p2m_open "ModularCurve"

private theorem nwr_smul_def {M : ℕ} (c : AlgebraicClosure ℚ) (f : modularFunctionFieldBar M) :
    c • f = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar M) c * f :=
  Algebra.smul_def c f

section

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

private theorem nwr_isStrict_of_ne (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hV : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V)) ≠ P.reduceFst V) :
    P.IsStrictFst V ∨ P.IsStrictSnd V := by
  have hd := P.d1 V
  change P.reduceFst V = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd V) ∨
      frobOnPlacesGeomLevel k N data hKr (P.reduceFst V) = P.reduceSnd V at hd
  rcases hd with h2 | h1
  · refine Or.inr ⟨h2, fun hfix => hV ?_⟩
    rw [h2, hfix]
  · exact Or.inl ⟨h1, hV⟩

private theorem nwr_lcm_eq [IsAlgClosed k] [DecidableEq k] (W : Finset (Place k (modularFunctionFieldC k N)))
    (e : Place k (modularFunctionFieldC k N) → ℕ) :
    Finset.univ.lcm (widthOfPlaces (arithFrobC q k N) W e) = W.lcm e := by
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro s _
    obtain ⟨w, hw, hs⟩ := (mem_nodePairsOfPlaces_iff (arithFrobC q k N) W
      (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N))).mp s.2
    have hs1 : (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 = w := by
      rw [← hs]; rfl
    rw [widthOfPlaces_apply, hs1]
    exact Finset.dvd_lcm hw
  · apply Finset.lcm_dvd
    intro w hw
    have hmem : smulNodePair (arithFrobC q k N) w ∈ nodePairsOfPlaces (arithFrobC q k N) W :=
      (mem_nodePairsOfPlaces_iff _ _ _).mpr ⟨w, hw, rfl⟩
    have h := Finset.dvd_lcm (s := Finset.univ) (f := widthOfPlaces (arithFrobC q k N) W e)
      (Finset.mem_univ (⟨smulNodePair (arithFrobC q k N) w, hmem⟩ : ↥(nodePairsOfPlaces (arithFrobC q k N) W)))
    rw [widthOfPlaces_apply] at h
    exact h

private theorem nwr_clause_nodes [IsAlgClosed k] [DecidableEq k] (W : Finset (Place k (modularFunctionFieldC k N)))
    (R : PlaceSpecialization.ProlongationTuple P) (e : Place k (modularFunctionFieldC k N) → ℕ)
    {f : modularFunctionFieldBar (N * q)} (h₁ : f ∈ R.R₁.integers)
    (hc : (1 : AlgebraicClosure ℚ) • f ∈ R.R₁.integers)
    (key : (⟨(1 : AlgebraicClosure ℚ) • f, hc⟩ : R.R₁.integers) = ⟨f, h₁⟩)
    (n : Place k (modularFunctionFieldC k N) → ℕ) (hn : ∀ w ∈ W, n w = W.lcm e / e w)
    (hordW : ∀ (w) (_ : w ∈ W), w.ord (R.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k N) = -((n w : ℕ) : ℤ)) :
    ∀ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
      ((s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1).ord
          (R.residue₁ ⟨(1 : AlgebraicClosure ℚ) • f, hc⟩ : modularFunctionFieldC k N)
        = -((Finset.univ.lcm (widthOfPlaces (arithFrobC q k N) W e) /
              widthOfPlaces (arithFrobC q k N) W e s : ℕ) : ℤ) := by
  have hord' : ∀ w ∈ W, w.ord (R.residue₁ ⟨(1 : AlgebraicClosure ℚ) • f, hc⟩ : modularFunctionFieldC k N)
      = -((Finset.univ.lcm (widthOfPlaces (arithFrobC q k N) W e) / e w : ℕ) : ℤ) := by
    intro w hw
    have h := hordW w hw
    rw [hn w hw, ← nwr_lcm_eq W e] at h
    rw [key]
    exact h
  rintro ⟨val, prop⟩
  obtain ⟨w, hw, hs⟩ := (mem_nodePairsOfPlaces_iff (arithFrobC q k N) W val).mp prop
  subst hs
  exact hord' w hw

private theorem nwr_clause_offnode [IsAlgClosed k] [DecidableEq k] (W : Finset (Place k (modularFunctionFieldC k N)))
    (R : PlaceSpecialization.ProlongationTuple P)
    {f : modularFunctionFieldBar (N * q)} (h₁ : f ∈ R.R₁.integers)
    (hc : (1 : AlgebraicClosure ℚ) • f ∈ R.R₁.integers)
    (key : (⟨(1 : AlgebraicClosure ℚ) • f, hc⟩ : R.R₁.integers) = ⟨f, h₁⟩)
    (hiv : ∀ G : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ V, G V = V.ord f) →
      ∀ v : Place k (modularFunctionFieldC k N), v ∉ W →
        Finsupp.mapDomain P.reduceFst (P.fstDiv G) v = v.ord (R.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k N)) :
    ∀ G : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ V, G V = V.ord f) →
      ∀ v : Place k (modularFunctionFieldC k N), v ∉ W →
        Finsupp.mapDomain P.reduceFst (P.fstDiv G) v
          = v.ord (R.residue₁ ⟨(1 : AlgebraicClosure ℚ) • f, hc⟩ : modularFunctionFieldC k N) := by
  rw [key]
  exact hiv

private theorem nwr_of_datum [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : PlaceSpecialization.ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W)
    (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed) (e : Place k (modularFunctionFieldC k N) → ℕ)
    (y : Place k (modularFunctionFieldC k N) → modularFunctionFieldBar (N * q))
    (n : Place k (modularFunctionFieldC k N) → ℕ) (hn : ∀ w ∈ W, n w = W.lcm e / e w)
    (hyS : ∀ w ∈ W, y w ∈ R.nodeIntegers w)
    (hy₁ : ∀ w ∈ W, ∃ h : y w ∈ R.R₁.integers, R.R₁.residue ⟨y w, h⟩ ≠ 0)
    (hyV : ∀ w ∈ W, ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.reduceFst V = w → V.ord (y w) = 0)
    (hy_ord1 : ∀ (w) (_ : w ∈ W) (h : y w ∈ R.R₁.integers),
      w.ord (R.residue₁ ⟨y w, h⟩ : modularFunctionFieldC k N) = 1)
    (hvert : ∀ w ∈ W, ∀ w' ∈ W,
      ∃ h : y w ^ n w * (y w' ^ n w')⁻¹ ∈ R.R₂.integers, R.R₂.residue ⟨y w ^ n w * (y w' ^ n w')⁻¹, h⟩ ≠ 0) :
    ∃ (f : modularFunctionFieldBar (N * q)) (_ : f ≠ 0) (c : AlgebraicClosure ℚ)
      (hc : c • f ∈ R.R₁.integers),
      R.R₁.residue ⟨c • f, hc⟩ ≠ 0 ∧
      (∀ G : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        (∀ V, G V = V.ord f) → P.IsGoodDiv G) ∧
      (∀ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
        ((s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1).ord
            (R.residue₁ ⟨c • f, hc⟩ : modularFunctionFieldC k N)
          = -((Finset.univ.lcm (widthOfPlaces (arithFrobC q k N) W e) /
                widthOfPlaces (arithFrobC q k N) W e s : ℕ) : ℤ)) ∧
      (∀ G : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        (∀ V, G V = V.ord f) →
        ∀ v : Place k (modularFunctionFieldC k N), v ∉ W →
          Finsupp.mapDomain P.reduceFst (P.fstDiv G) v
            = v.ord (R.residue₁ ⟨c • f, hc⟩ : modularFunctionFieldC k N)) := by

  have hZf := ModularCurve.finite_setOf_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self k N data hKr
  have hZ : ∀ v : Place k (modularFunctionFieldC k N),
      v ∈ hZf.toFinset ↔ frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v :=
    fun v => by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]

  have hv5 :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_and_forall_ord_eq_zero
      R hqN hR W hW hRL hNV hO hZf.toFinset hZ y n hyS hy₁ hyV hy_ord1 hvert
  obtain ⟨f, hf0, ⟨h₁, hres, hordW, hiv⟩, -, hZcl⟩ := hv5
  have h1f : (1 : AlgebraicClosure ℚ) • f = f := by rw [nwr_smul_def, map_one, one_mul]
  have hc : (1 : AlgebraicClosure ℚ) • f ∈ R.R₁.integers := by rw [h1f]; exact h₁
  have key : (⟨(1 : AlgebraicClosure ℚ) • f, hc⟩ : R.R₁.integers) = ⟨f, h₁⟩ := Subtype.ext h1f
  refine ⟨f, hf0, 1, hc, ?_, ?_, ?_, ?_⟩
  · rw [key]; exact hres
  ·
    intro G hG V hV
    have hVord : V.ord f ≠ 0 := by rwa [Finsupp.mem_support_iff, hG] at hV
    have hnotZ : P.reduceFst V ∉ hZf.toFinset := fun hz => hVord (hZcl _ hz V rfl)
    exact nwr_isStrict_of_ne V (fun h => hnotZ ((hZ _).mpr h))
  ·
    exact nwr_clause_nodes W R e h₁ hc key n hn hordW
  ·
    exact nwr_clause_offnode W R h₁ hc key hiv

private theorem nwr_of_coordinates [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : PlaceSpecialization.ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W)
    (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed) (e : Place k (modularFunctionFieldC k N) → ℕ)
    (Ks : ↥W → IntermediateField ℚ (AlgebraicClosure ℚ)) [∀ w : ↥W, FiniteDimensional ℚ (Ks w)]
    (cs : ∀ w : ↥W, R.NodeCoordinates (Ks w) (w : Place k (modularFunctionFieldC k N)))
    (us : ∀ w : ↥W, ↥(R.nodeIntegersOver (Ks w) (w : Place k (modularFunctionFieldC k N))))
    (hus : ∀ w : ↥W, IsUnit (us w))
    (hxy : ∀ w : ↥W, (cs w).x * (cs w).y =
      R.nodeConst (Ks w) (w : Place k (modularFunctionFieldC k N))
        ((q : ℕ) : ↥(NodeLocalized.coeffSubring A (Ks w))) ^ e (w : Place k (modularFunctionFieldC k N)) * us w) :
    ∃ (f : modularFunctionFieldBar (N * q)) (_ : f ≠ 0) (c : AlgebraicClosure ℚ)
      (hc : c • f ∈ R.R₁.integers),
      R.R₁.residue ⟨c • f, hc⟩ ≠ 0 ∧
      (∀ G : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        (∀ V, G V = V.ord f) → P.IsGoodDiv G) ∧
      (∀ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
        ((s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1).ord
            (R.residue₁ ⟨c • f, hc⟩ : modularFunctionFieldC k N)
          = -((Finset.univ.lcm (widthOfPlaces (arithFrobC q k N) W e) /
                widthOfPlaces (arithFrobC q k N) W e s : ℕ) : ℤ)) ∧
      (∀ G : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        (∀ V, G V = V.ord f) →
        ∀ v : Place k (modularFunctionFieldC k N), v ∉ W →
          Finsupp.mapDomain P.reduceFst (P.fstDiv G) v
            = v.ord (R.residue₁ ⟨c • f, hc⟩ : modularFunctionFieldC k N)) := by
  have hdat :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.exists_seedDatum_of_nodeCoordinates_nodeEquation
      R hqN W Ks cs e us hus hxy
  obtain ⟨y, n, hyc, hn, hyS, hy₁, hyV, hvert⟩ := hdat
  have hy_ord1 : ∀ (w) (_ : w ∈ W) (h : y w ∈ R.R₁.integers),
      w.ord (R.residue₁ ⟨y w, h⟩ : modularFunctionFieldC k N) = 1 := by
    intro w hw h
    have e1 : (⟨y w, h⟩ : R.R₁.integers)
        = ⟨((cs ⟨w, hw⟩).y : modularFunctionFieldBar (N * q)), (cs ⟨w, hw⟩).y.2.1.1⟩ := Subtype.ext (hyc w hw)
    have h1 := (cs ⟨w, hw⟩).y_fst
    rw [PlaceSpecialization.ProlongationTuple.nodeResidue₁_apply] at h1
    rw [e1]
    exact h1
  exact nwr_of_datum hqN W hW R hR hRL hNV hO e y n hn hyS hy₁ hyV hy_ord1 hvert

end

end ModularCurve.NwRed

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_PlaceSpecialization_exists_isGoodDiv_ord_residueFst_eq_neg_lcm_div_widthChar_of_orderLawFixed.ModularCurve ModularCurve.PlaceSpecialization in

theorem solution
    {q : ℕ} [Fact q.Prime]
  {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
  [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
  {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} [IsAlgClosed k]
  [DecidableEq k]
  (hqN : ¬ q ∣ N)
  (P : PlaceSpecialization A q N data hKr k red hα hβ)
  (W : Finset (Place k (modularFunctionFieldC k N)))
  (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
  (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
  (hO : R.OrderLawFixed)
  (e : Place k (modularFunctionFieldC k N) → ℕ)
  (he : ∀ w ∈ W, e w = placeWidthChar q N w) :
    ∃ (f : modularFunctionFieldBar (N * q)) (hf : f ≠ 0) (c : AlgebraicClosure ℚ)
      (hc : c • f ∈ R.R₁.integers),
      R.R₁.residue ⟨c • f, hc⟩ ≠ 0 ∧
      (∀ G : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        (∀ V, G V = V.ord f) → P.IsGoodDiv G) ∧
      (∀ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
        ((s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1).ord
            (R.residue₁ ⟨c • f, hc⟩ : modularFunctionFieldC k N)
          = -((Finset.univ.lcm (widthOfPlaces (arithFrobC q k N) W e) /
                widthOfPlaces (arithFrobC q k N) W e s : ℕ) : ℤ)) ∧
      (∀ G : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        (∀ V, G V = V.ord f) →
        ∀ v : Place k (modularFunctionFieldC k N), v ∉ W →
          Finsupp.mapDomain P.reduceFst (P.fstDiv G) v
            = v.ord (R.residue₁ ⟨c • f, hc⟩ : modularFunctionFieldC k N)) := by

  have hker : ∀ c : ↥A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal ↥A :=
    fun c => ValuationSubring.ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP A q red c

  have hpack : ∀ w : ↥W, ∃ (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K₀)
      (c : R.NodeCoordinates K₀ (w : Place k (modularFunctionFieldC k N)))
      (u : ↥(R.nodeIntegersOver K₀ (w : Place k (modularFunctionFieldC k N)))), IsUnit u ∧
        c.x * c.y = R.nodeConst K₀ (w : Place k (modularFunctionFieldC k N))
          ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) ^ e (w : Place k (modularFunctionFieldC k N)) * u := by
    intro w
    have h :=
      ProlongationTuple.exists_inertiaFixed_nodeCoordinates_presentation_of_orderLawFixed R hqN hker hR hO W
        (fun w hw => (hW w).mp hw) hRL hNV (w : Place k (modularFunctionFieldC k N)) w.2
    obtain ⟨K₀, hfd, -, -, c, u, ⟨hu, hxy⟩, -, -, -, -⟩ := h
    refine ⟨K₀, hfd, c, u, hu, ?_⟩
    rw [he _ w.2]
    exact hxy
  choose Ks hfd cs us hus hxy using hpack
  haveI : ∀ w : ↥W, FiniteDimensional ℚ (Ks w) := hfd
  exact ModularCurve.NwRed.nwr_of_coordinates hqN W hW R hR hRL hNV hO e Ks cs us hus hxy

#print axioms solution

end S_ModularCurve_PlaceSpecialization_exists_isGoodDiv_ord_residueFst_eq_neg_lcm_div_widthChar_of_orderLawFixed
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_isGoodDiv_ord_residueFst_eq_neg_lcm_div_widthChar_of_orderLawFixed (solution)
