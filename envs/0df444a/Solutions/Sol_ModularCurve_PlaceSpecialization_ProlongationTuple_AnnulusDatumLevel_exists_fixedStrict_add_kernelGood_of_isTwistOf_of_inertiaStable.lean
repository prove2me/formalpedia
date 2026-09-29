-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.exists_fixedStrict_add_kernelGood_of_isTwistOf_of_inertiaStable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/669e5745-7372-5d14-8ec9-95ea9b2e84a1

import Mathlib
import Definitions.Def_ModularCurve_AnnulusSpecializationLevel
import Definitions.Def_ModularCurve_PlaceWidthChar
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_spData_mem_admissible
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_strict_gluedPic0Mk_glueData_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_isTwistOf_sub_and_spData_sub_eq_of_forall_isStrict
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_exists_fixedStrict_add_kernelGood_of_isTwistOf_of_inertiaStable
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.numberField_of_finiteDimensional ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instIsElliptic_tateBase ValuationSubring.instIsAlgClosedResidueField AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AdicCompletion.instIsLocalRingMaximalIdeal GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply"
p2m_attr_erase "simp" "WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe ModularCurve.symPoly_zero ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast"
p2m_attr_erase "simp" "ValuationSubring.reduceAt_zero AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe"
p2m_attr_erase "simp" "NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom"
p2m_attr_erase "simp" "AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatum.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.TwistVector.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.TwistVector.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatum.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.mk.injEq"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

set_option maxHeartbeats 16000000 in
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
    (hO : R.OrderLawFixed) (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w)
    (dat : R.AnnulusDatumLevel W)
    (hwidth : ∀ w ∈ W, 1 ≤ dat.width w)
    (hwidthc : ∀ w ∈ W, dat.width w = placeWidthChar q N w)
    (hdepthQ : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
      (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
      0 < dat.depthQ V ∧ dat.depthQ V < dat.width w ∧ (dat.coord w hw).yDepth V ^ (dat.depthQ V).den =
      A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (dat.depthQ V).num.toNat)
    (hdepthσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      dat.depthQ (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) = dat.depthQ V)
    (hD1 : ∀ w ∈ W, 2 ≤ dat.width w → ∃ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧ dat.depthQ V = 1)
    (hunif : ∀ w ∈ W,
      ((∀ v, (Finsupp.single w (1 : ℤ) + dat.corrFst w) v = v.ord (dat.unifFst w)) ∧ (∀ v ∈ W, dat.corrFst w v = 0) ∧
      Divisor.degree (dat.corrFst w) = -1) ∧
      ((∀ v, (Finsupp.single (arithFrobC q k N • w) (1 : ℤ) + dat.corrSnd w) v = v.ord (dat.unifSnd w)) ∧
      (∀ v ∈ W, dat.corrSnd w v = 0) ∧ Divisor.degree (dat.corrSnd w) = -1))
    (hKfix : ∀ w ∈ W, ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ dat.K w, σ z = z)
    (hK : ∀ w : Place k (modularFunctionFieldC k N), FiniteDimensional ℚ ↥(dat.K w))
    (ϖ : ∀ w : Place k (modularFunctionFieldC k N), ↥(NodeLocalized.coeffSubring A (dat.K w)))
      (eK : Place k (modularFunctionFieldC k N) → ℕ)
      (ε : ∀ w : Place k (modularFunctionFieldC k N), ↥(NodeLocalized.coeffSubring A (dat.K w)))
      (u : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), ↥(R.nodeIntegersOver (dat.K w) w))
    (hϖ : ∀ w ∈ W, ∀ d : ↥(NodeLocalized.coeffSubring A (dat.K w)),
      NodeLocalized.redRestrict red (dat.K w) d = 0 ↔ ∃ d', d = ϖ w * d')
    (heK : ∀ w ∈ W, 1 ≤ eK w)
    (hε : ∀ w ∈ W, IsUnit (ε w))
    (hqϖ : ∀ w ∈ W, ((q : ℕ) : ↥(NodeLocalized.coeffSubring A (dat.K w))) = ϖ w ^ eK w * ε w)
    (hε1 : ∀ w ∈ W, NodeLocalized.redRestrict red (dat.K w) (ε w) = 1)
    (hu : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), IsUnit (u w hw) ∧
      (dat.coord w hw).x * (dat.coord w hw).y = R.nodeConst (dat.K w) w (ϖ w) ^ (dat.width w * eK w) * u w hw)
    (hmax : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x, (dat.coord w hw).y}).IsMaximal ∧
      ∀ M : Ideal ↥(R.nodeIntegersOver (dat.K w) w), M.IsMaximal →
      M = Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x, (dat.coord w hw).y})
    (hbr : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x}).IsPrime ∧
      (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).y}).IsPrime ∧
      (dat.coord w hw).y ∉ Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x} ∧
      (dat.coord w hw).x ∉ Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).y})
    (hnoeth : ∀ w ∈ W, IsNoetherianRing ↥(R.nodeIntegersOver (dat.K w) w))
    (hres : ∀ w ∈ W, ∀ g : ↥(R.nodeIntegersOver (dat.K w) w),
      ∃ o : ↥(NodeLocalized.coeffSubring A (dat.K w)), ¬ IsUnit (g - R.nodeConst (dat.K w) w o))
    (hu0 : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨(u w hw : ↥(modularFunctionFieldBar (N * q))), (u w hw).2.1⟩) ((dat.u0 w : kˣ) : k))
    (hlam : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨((dat.coord w hw).y : ↥(modularFunctionFieldBar (N * q))), (dat.coord w hw).y.2.1⟩
      / dat.unifFst w) ((dat.lam w : kˣ) : k))
    (hmu : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      (arithFrobC q k N • w).HasValue
      (R.nodeResidue₂ w ⟨((dat.coord w hw).x : ↥(modularFunctionFieldBar (N * q))), (dat.coord w hw).x.2.1⟩
      / dat.unifSnd w) ((dat.mu w : kˣ) : k))
    (X : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
    (hXstab : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = X)
    (hXsupp : ∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)
    (a : ProlongationTuple.TwistVectorLevel (k := k) (N := N) W)
    (ha : dat.IsTwistOf a (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) :
    ∃ (Dt D₂ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))),
      (∀ V ∈ (Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).support,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
          (P.IsStrictFst V ∨ P.IsStrictSnd V)) ∧
      P.IsGoodDiv (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∧
      (∃ hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k N) W) (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W),
        GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k N) W) ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k N) W) (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), hadm⟩ = 0) ∧
      ((X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - Dt - D₂) ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI := Classical.decEq (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))

  have hdegMap : ∀ (f : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → Place k (modularFunctionFieldC k N))
      (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), Divisor.degree (Finsupp.mapDomain f E) = Divisor.degree E := by
    intro f E
    induction E using Finsupp.induction_linear with
    | zero => simp
    | add E₁ E₂ h₁ h₂ => rw [Finsupp.mapDomain_add, map_add, map_add, h₁, h₂]
    | single V n =>
      rw [Finsupp.mapDomain_single, Divisor.degree_single, Divisor.degree_single,
        ModularCurve.place_deg_eq_one_of_isAlgClosed k N (f V), ModularCurve.deg_eq_one_modularFunctionFieldBar (N * q) V]

  have hcorrFst : ∀ w ∈ W, (∀ v ∈ W, dat.corrFst w v = 0) ∧ Divisor.degree (dat.corrFst w) = -1 :=
    fun w hw => ⟨(hunif w hw).1.2.1, (hunif w hw).1.2.2⟩
  have hcorrSnd : ∀ w ∈ W, (∀ v ∈ W, dat.corrSnd w v = 0) ∧ Divisor.degree (dat.corrSnd w) = -1 :=
    fun w hw => ⟨(hunif w hw).2.2.1, (hunif w hw).2.2.2⟩
  have hadmX : dat.spData a (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W) :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.spData_mem_admissible hqN hW dat hcorrFst hcorrSnd a
      (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ha.1 ha.2.1

  have hTL := ModularCurve.PlaceSpecialization.ProlongationTuple.exists_inertiaFixed_strict_gluedPic0Mk_glueData_eq P hqN hW R hR hO
    (GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k N) W) ⟨dat.spData a (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), hadmX⟩)
  obtain ⟨Dt, hDtfix, hDtgood, hadmDt, hmkDt⟩ := hTL
  have hDtstrict : ∀ V ∈ (Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).support, P.IsStrictFst V ∨ P.IsStrictSnd V := fun V hV => hDtgood V hV

  have hadmDt' := (GluingData.mem_admissible (nodePairsOfPlaces (arithFrobC q k N) W)).mp hadmDt
  have hdeg₁ : Divisor.degree (P.fstDiv (Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) = 0 := by
    have h := Divisor.mem_degZero.mp hadmDt'.1
    dsimp only [PlaceSpecialization.glueData] at h
    rwa [hdegMap] at h
  have hdeg₂ : Divisor.degree (P.sndDiv (Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) = 0 := by
    have h := Divisor.mem_degZero.mp hadmDt'.2.1
    dsimp only [PlaceSpecialization.glueData] at h
    rwa [hdegMap] at h

  have hSS := ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.isTwistOf_sub_and_spData_sub_eq_of_forall_isStrict dat
      (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) hDtstrict hdeg₁ hdeg₂ a ha
  obtain ⟨haX', hspX'⟩ := hSS

  have hDtst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = Dt := by
    intro σ hσ
    rw [SemilinearAut.divisor_smul_def, Finsupp.mapDomain_congr (g := id) (fun V hV => hDtfix σ hσ V hV), Finsupp.mapDomain_id]
  have hX'stab : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      arithmeticGalois (modularFunctionFieldFull (N * q)) σ • ((X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - Dt) = (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - Dt := by
    intro σ hσ; rw [smul_sub, hXstab σ hσ, hDtst σ hσ]
  have hX'supp : ∀ V ∈ ((X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - Dt).support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W := by
    intro V hV
    rcases Finset.mem_union.mp (Finsupp.support_sub hV) with h | h
    · exact hXsupp V h
    · rcases hDtstrict V h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
  have hadmX' : dat.spData a ((X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - Dt) ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W) := by
    rw [hspX']; exact sub_mem hadmX hadmDt
  have hspX'0 : GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k N) W) ⟨dat.spData a ((X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - Dt), hadmX'⟩ = 0 := by
    have hsub : (⟨dat.spData a ((X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - Dt), hadmX'⟩ : ↥(GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W))) =
        ⟨dat.spData a (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), hadmX⟩ - ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k N) W) (Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), hadmDt⟩ := Subtype.ext hspX'
    rw [hsub, map_sub, hmkDt, sub_self]

  have hSC := ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable
      P hqN hW R hR hRL hNV hO hVI dat hwidth hwidthc hdepthQ hdepthσ hD1 hunif hKfix hK ϖ eK ε u hϖ heK hε hqϖ hε1 hu hmax hbr
      hnoeth hres hu0 hlam hmu ⟨(X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - Dt, sub_mem X.2 Dt.2⟩ hX'stab hX'supp a haX' hadmX' hspX'0
  obtain ⟨D₂, hadm₂, hD₂good, hmk₂, hcls⟩ := hSC
  refine ⟨Dt, D₂, fun V hV => ⟨fun σ hσ => hDtfix σ hσ V hV, hDtgood V hV⟩, hD₂good, ⟨hadm₂, hmk₂⟩, ?_⟩

  have := (QuotientAddGroup.eq (s := (Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))).addSubgroupOf _)).mp hcls
  rw [AddSubgroup.mem_addSubgroupOf] at this
  have hcoe : ((-D₂ + ⟨(X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - Dt, sub_mem X.2 Dt.2⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = -(D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) + ((X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - Dt) := rfl
  rw [hcoe, neg_add_eq_sub] at this
  exact this

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_exists_fixedStrict_add_kernelGood_of_isTwistOf_of_inertiaStable
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_exists_fixedStrict_add_kernelGood_of_isTwistOf_of_inertiaStable (solution)
