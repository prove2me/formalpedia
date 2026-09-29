-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mem_jIntegralClosure_ord_residues_pos_and_eq_zero_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/48c4202d-1a80-5caa-8937-b18ee3a2cf1c

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure
import Theorems.Thm_ModularCurve_exists_fieldOver_lift_isIntegral_of_isIntegral
import Theorems.Thm_ModularCurve_forall_isAffineGeomPlace_mem_iff_isIntegral_adjoin
import Theorems.Thm_ModularCurve_exists_coeff_pow_sq_eq_and_hasValue_zero_and_not_hasValue_zero_of_mem_ssPlaces_of_ne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure
import Theorems.Thm_ModularCurve_isIntegral_jRing_of_coeffMap_eq_of_isIntegral_adjoin_of_not_dvd
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_jIntegralClosure_ord_residues_pos_and_eq_zero_of_ne
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.cuspCount_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub"
p2m_attr_erase "simp" "CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.Gamma0Pair.map_toCurve"
p2m_attr_erase "simp" "WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of"
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace SupersingularNodeSeparation

private theorem exists_separator {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q]
    [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (w w' : Place k (modularFunctionFieldC k N))
    (hw : w ∈ ssPlaces q N k) (hne : w ≠ w') :
    ∃ t : ↥(modularFunctionFieldC k N),
      (∀ n : ℤ, ((t : LaurentSeries k).coeff n) ^ (q ^ 2) = (t : LaurentSeries k).coeff n) ∧
      (∀ u : Place k (modularFunctionFieldC k N), IsAffineGeomPlace k N u → t ∈ u.toValuationSubring) ∧
      w.HasValue t (0 : k) ∧ ¬ w'.HasValue t (0 : k) := by
  exact exists_coeff_pow_sq_eq_and_hasValue_zero_and_not_hasValue_zero_of_mem_ssPlaces_of_ne hqN w w' hw hne

private theorem exists_coeffMap_eq_of_forall_coeff_mem_range {S T : Type*} [CommRing S] [CommRing T] (φ : S →+* T)
    (x : LaurentSeries T) (hx : ∀ n : ℤ, x.coeff n ∈ Set.range φ) : ∃ y : LaurentSeries S, coeffMap φ y = x := by
  classical
  refine ⟨⟨fun n => if h : x.coeff n = 0 then 0 else (hx n).choose, ?_⟩, ?_⟩
  · refine x.isPWO_support.mono ?_
    intro n hn
    rw [HahnSeries.mem_support]
    intro h0
    exact hn (dif_pos h0)
  · ext n
    rw [coeffMap_coeff]
    dsimp only
    split_ifs with h
    · rw [map_zero, h]
    · exact (hx n).choose_spec

private theorem fieldOver_le_fieldOver_mul (N q : ℕ) [NeZero N] [NeZero q]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    NodeLocalized.fieldOver N K ≤ NodeLocalized.fieldOver (N * q) K := by
  have hgen := ModularCurve.functionFieldGeneration (N * q)
  have hN : qExpand ℚ N jq ∈ IntermediateField.adjoin ℚ {jq, qExpand ℚ (N * q) jq} :=
    hgen N (dvd_mul_right N q) inferInstance

  let S : Subfield (LaurentSeries ℚ) := (NodeLocalized.fieldOver (N * q) K).comap (coeffEmb (AlgebraicClosure ℚ))
  have hjq : jq ∈ S := by
    show coeffEmb (AlgebraicClosure ℚ) jq ∈ NodeLocalized.fieldOver (N * q) K
    rw [← jqModC_rat, coeffEmb, coeffMap_jqModC]
    exact Subfield.subset_closure (Or.inr (by simp))
  have hjNq : qExpand ℚ (N * q) jq ∈ S := by
    show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (N * q) jq) ∈ NodeLocalized.fieldOver (N * q) K
    rw [← jqModC_rat, ← jqNModC, coeffEmb, coeffMap_jqNModC]
    exact Subfield.subset_closure (Or.inr (by simp))
  have hadj : IntermediateField.adjoin ℚ {jq, qExpand ℚ (N * q) jq} ≤
      Subfield.toIntermediateField S (fun r => by
        show coeffEmb (AlgebraicClosure ℚ) (algebraMap ℚ (LaurentSeries ℚ) r) ∈ NodeLocalized.fieldOver (N * q) K
        rw [eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)) r, map_ratCast]
        exact SubfieldClass.ratCast_mem _ r) := by
    rw [IntermediateField.adjoin_le_iff]
    rintro x (rfl | rfl)
    · exact hjq
    · exact hjNq
  have hjN : jqNModC (AlgebraicClosure ℚ) N ∈ NodeLocalized.fieldOver (N * q) K := by
    have h := hadj hN
    change coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq) ∈ NodeLocalized.fieldOver (N * q) K at h
    rwa [← jqModC_rat, ← jqNModC, coeffEmb, coeffMap_jqNModC] at h
  refine Subfield.closure_le.mpr ?_
  rintro x (hx | hx)
  · exact Subfield.subset_closure (Or.inl hx)
  · rcases hx with rfl | rfl
    · exact Subfield.subset_closure (Or.inr (by simp))
    · exact hjN

set_option synthInstance.maxHeartbeats 1600000 in

private theorem exists_mem_jIntegralClosure_residue₁_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (gbar : ↥(modularFunctionFieldC k N))
    (y : LaurentSeries ↥(NodeLocalized.coeffSubring A K)) (g₀ : ↥(modularFunctionFieldBar N))
    (hg₀y : (g₀ : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap (NodeLocalized.coeffSubring A K).subtype y)
    (hy : coeffMap (NodeLocalized.redRestrict red K) y = (gbar : LaurentSeries k))
    (hg₀K : (g₀ : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver N K)
    (hint : IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ)
        ({⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩,
          ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full N (dvd_refl N))⟩} :
          Set ↥(modularFunctionFieldBar N))) g₀) :
    ∃ (g : ↥(modularFunctionFieldBar (N * q)))
      (_ : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.jIntegralClosure (N * q) A K)
      (h₁ : g ∈ R.R₁.integers),
      (R.residue₁ ⟨g, h₁⟩ : ↥(modularFunctionFieldC k N)) = gbar := by

  set y' : LaurentSeries A :=
    coeffMap (Subring.inclusion (inf_le_left : NodeLocalized.coeffSubring A K ≤ A.toSubring)) y with hy'
  have hy'coe : coeffMap A.subtype y' = (g₀ : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [hg₀y, hy', coeffMap_coeffMap]
    rfl
  have hmem : coeffMap A.subtype y' ∈ modularFunctionFieldBar (N * q) := by
    rw [hy'coe, ← coe_heckeAlphaBar (L := AlgebraicClosure ℚ) N q g₀]
    exact (heckeAlphaBar (AlgebraicClosure ℚ) N q g₀).2
  obtain ⟨h₁, hres⟩ := R.residue₁_coeffMap y' hmem
  refine ⟨⟨coeffMap A.subtype y', hmem⟩, ?_, h₁, ?_⟩
  ·
    refine ⟨?_, ?_⟩
    · show coeffMap A.subtype y' ∈ NodeLocalized.fieldOver (N * q) K
      rw [hy'coe]
      exact fieldOver_le_fieldOver_mul N q K hg₀K
    · show IsIntegral (NodeLocalized.jRing A K) (coeffMap A.subtype y')
      rw [hy'coe]
      exact ModularCurve.isIntegral_jRing_of_coeffMap_eq_of_isIntegral_adjoin_of_not_dvd A K red hqN y g₀ hg₀y hint
  ·
    apply Subtype.ext
    show ((R.ι (R.R₁.residue ⟨_, h₁⟩) : ↥(modularFunctionFieldC k N)) : LaurentSeries k) = (gbar : LaurentSeries k)
    rw [R.ι_coe, hres, ← hy, hy', coeffMap_coeffMap, coeffMap_coeffMap]
    congr 1
    ext c
    exact R.redBar_residue _

set_option synthInstance.maxHeartbeats 1600000 in

private theorem exists_residue₁_hasValue_zero_and_not
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K))
    (w w' : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (hne : w ≠ w') :
    ∃ (g : ↥(modularFunctionFieldBar (N * q)))
      (_ : ((g : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.jIntegralClosure (N * q) A K))
      (h₁ : g ∈ R.R₁.integers),
      w.HasValue (R.residue₁ ⟨g, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k) ∧
        ¬ w'.HasValue (R.residue₁ ⟨g, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k) := by
  obtain ⟨t, hfix, hreg, hw0, hw'0⟩ := exists_separator hqN w w' hw hne
  obtain ⟨h₀, hh₀⟩ := exists_coeffMap_eq_of_forall_coeff_mem_range (NodeLocalized.redRestrict red K)
    (t : LaurentSeries k) (fun n => hk₀ _ (hfix n))
  have hN : (N : k) ≠ 0 := fun h => hqN ((CharP.cast_eq_zero_iff k q N).1 h)
  have hint := (forall_isAffineGeomPlace_mem_iff_isIntegral_adjoin hN t).1 hreg
  obtain ⟨y, g₀, hg₀y, hy, hg₀K, hg₀int⟩ :=
    exists_fieldOver_lift_isIntegral_of_isIntegral red hqN K h₀ t hh₀ hint
  obtain ⟨g, hgC, h₁, hres⟩ := exists_mem_jIntegralClosure_residue₁_eq R hqN K t y g₀ hg₀y hy hg₀K hg₀int
  refine ⟨g, hgC, h₁, ?_, ?_⟩
  · rw [hres]; exact hw0
  · rw [hres]; exact hw'0

set_option synthInstance.maxHeartbeats 1600000 in

private theorem residue₂_hasValue_zero_iff
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (v : Place k (modularFunctionFieldC k N)) (hv : v ∈ ssPlaces q N k)
    (g : ↥(modularFunctionFieldBar (N * q)))
    (hg : ((g : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.jIntegralClosure (N * q) A K))
    (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers) :
    (arithFrobC q k N • v).HasValue (R.residue₂ ⟨g, h₂⟩ : ↥(modularFunctionFieldC k N)) (0 : k) ↔
      v.HasValue (R.residue₁ ⟨g, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k) := by
  exact hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure R hqN K v hv g hg h₁ h₂

set_option synthInstance.maxHeartbeats 1600000 in

private theorem mem_integers₂_and_regular
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (v : Place k (modularFunctionFieldC k N)) (hv : v ∈ ssPlaces q N k)
    (g : ↥(modularFunctionFieldBar (N * q)))
    (hg : ((g : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.jIntegralClosure (N * q) A K)) :
    ∃ (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers),
      (R.residue₁ ⟨g, h₁⟩ : ↥(modularFunctionFieldC k N)) ∈ v.toValuationSubring ∧
      (R.residue₂ ⟨g, h₂⟩ : ↥(modularFunctionFieldC k N)) ∈ (arithFrobC q k N • v).toValuationSubring := by
  obtain ⟨hnode, hreg₁, hreg₂⟩ :=
    mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure R hqN K v hv g hg
  exact ⟨hnode.1, hnode.2.1, hreg₁ hnode.1, hreg₂ hnode.2.1⟩

private theorem ord_pos_of_hasValue_zero {k : Type*} [Field k] [IsAlgClosed k] {N : ℕ} [NeZero N]
    (v : Place k (modularFunctionFieldC k N)) (f : ↥(modularFunctionFieldC k N)) (hf : f ≠ 0)
    (h : v.HasValue f (0 : k)) : 0 < v.ord f := by
  obtain ⟨hm, hres⟩ := h
  rw [map_zero] at hres
  rcases (v.ord_nonneg_of_mem hm).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm', hu⟩ := v.exists_isUnit_of_ord_eq_zero hf heq.symm
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu hres

private theorem ord_eq_zero_of_not_hasValue_zero {k : Type*} [Field k] [IsAlgClosed k] {N : ℕ} [NeZero N]
    (v : Place k (modularFunctionFieldC k N)) (f : ↥(modularFunctionFieldC k N)) (hreg : f ∈ v.toValuationSubring)
    (h : ¬ v.HasValue f (0 : k)) : v.ord f = 0 := by
  have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hreg⟩ ≠ 0 := fun h0 => h ⟨hreg, by rw [h0, map_zero]⟩
  have h0 := v.ord_coe_unit ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 hres).unit
  rwa [IsUnit.unit_spec] at h0

private theorem ne_zero_of_not_hasValue_zero {k : Type*} [Field k] [IsAlgClosed k] {N : ℕ} [NeZero N]
    (v : Place k (modularFunctionFieldC k N)) (f : ↥(modularFunctionFieldC k N))
    (h : ¬ v.HasValue f (0 : k)) : f ≠ 0 := by
  rintro rfl
  have h0 := v.hasValue_algebraMap (0 : k)
  rw [map_zero] at h0
  exact h h0

end SupersingularNodeSeparation

open SupersingularNodeSeparation in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K))
    (w w' : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k) (hw' : w' ∈ ssPlaces q N k)
    (hne : w ≠ w') :
    ∃ (g : ↥(modularFunctionFieldBar (N * q)))
      (_ : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.jIntegralClosure (N * q) A K)
      (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers),
      0 < w.ord (R.residue₁ ⟨g, h₁⟩ : ↥(modularFunctionFieldC k N)) ∧
      0 < (arithFrobC q k N • w).ord (R.residue₂ ⟨g, h₂⟩ : ↥(modularFunctionFieldC k N)) ∧
      w'.ord (R.residue₁ ⟨g, h₁⟩ : ↥(modularFunctionFieldC k N)) = 0 ∧
      (arithFrobC q k N • w').ord (R.residue₂ ⟨g, h₂⟩ : ↥(modularFunctionFieldC k N)) = 0 := by
  obtain ⟨g, hgC, h₁, hw0, hw'0⟩ := exists_residue₁_hasValue_zero_and_not R hqN K hk₀ w w' hw hne
  obtain ⟨h₁', h₂, hreg₁, hreg₂⟩ := mem_integers₂_and_regular R hqN K w' hw' g hgC
  obtain ⟨h₁'', h₂', -, hreg₂'⟩ := mem_integers₂_and_regular R hqN K w hw g hgC
  have hv₂w : (arithFrobC q k N • w).HasValue (R.residue₂ ⟨g, h₂⟩ : ↥(modularFunctionFieldC k N)) (0 : k) :=
    (residue₂_hasValue_zero_iff R hqN K w hw g hgC h₁ h₂).2 hw0
  have hv₂w' : ¬ (arithFrobC q k N • w').HasValue (R.residue₂ ⟨g, h₂⟩ : ↥(modularFunctionFieldC k N)) (0 : k) :=
    fun h => hw'0 ((residue₂_hasValue_zero_iff R hqN K w' hw' g hgC h₁ h₂).1 h)
  refine ⟨g, hgC, h₁, h₂, ?_, ?_, ?_, ?_⟩
  · exact ord_pos_of_hasValue_zero w _ (ne_zero_of_not_hasValue_zero w' _ hw'0) hw0
  · exact ord_pos_of_hasValue_zero _ _ (ne_zero_of_not_hasValue_zero _ _ hv₂w') hv₂w
  · exact ord_eq_zero_of_not_hasValue_zero w' _ hreg₁ hw'0
  · exact ord_eq_zero_of_not_hasValue_zero _ _ hreg₂ hv₂w'

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_jIntegralClosure_ord_residues_pos_and_eq_zero_of_ne
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_jIntegralClosure_ord_residues_pos_and_eq_zero_of_ne (solution)
