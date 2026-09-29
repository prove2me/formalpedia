-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.existsUnique_reduceFst_eq_and_hasValue_y_of_orderLawFixed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/b7579fa0-7777-55f9-a183-8f19759c4c5f

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_reduceFst_eq_and_evalAt_y_eq_of_ringEquiv_uvCrossingModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_eq_of_evalAt_y_eq_of_reduceFst_eq_of_ringEquiv_uvCrossingModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_exponent_ringEquiv_adicCompletion_nodeIntegersOver_uvCrossingModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isLocalRing_and_isNoetherianRing_nodeIntegersOver_of_nodeCoordinates_of_orderLawFixed_of_range_redRestrict
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_not_isUnit_sub_nodeConst_of_evalAt_mem_range_redRestrict_of_orderLawFixed
import Theorems.Thm_ModularCurve_NodeLocalized_exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_completeDVR_ringHom_adicCompletion_nodeIntegersOver
import Theorems.Thm_ModularCurve_NodeLocalized_exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul
import Theorems.Thm_ModularCurve_isRational_place_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_existsUnique_reduceFst_eq_and_hasValue_y_of_orderLawFixed
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AdicCompletion.instIsLocalRingMaximalIdeal ValuationSubring.instIsAlgClosedResidueField AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero"
p2m_attr_erase "instance" "ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.instIsElliptic_tateBase WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent"
p2m_attr_erase "instance" "ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk"
p2m_attr_erase "simp" "WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.mulAdele_apply"
p2m_attr_erase "simp" "AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace KBGlue

section
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

private theorem red_eq_zero_iff (R : ProlongationTuple P) (c : A) : red c = 0 ↔ c ∈ maximalIdeal A := by
  rw [← R.redBar_residue, map_eq_zero_iff _ R.redBar.injective, IsLocalRing.residue_eq_zero_iff]

omit [Fact q.Prime] in
private theorem fieldOver_mono (M : ℕ) [NeZero M] {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K') :
    NodeLocalized.fieldOver M K ≤ NodeLocalized.fieldOver M K' := by
  unfold NodeLocalized.fieldOver
  apply Subfield.closure_mono
  apply Set.union_subset_union_left
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨x.1, hKK' x.2⟩, rfl⟩

private theorem nodeIntegersOver_mono (R : ProlongationTuple P) {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K')
    (w : Place k (modularFunctionFieldC k N)) : R.nodeIntegersOver K w ≤ R.nodeIntegersOver K' w :=
  fun _ hf => ⟨hf.1, fieldOver_mono (N * q) hKK' hf.2⟩

private def enlargeCoordinates (R : ProlongationTuple P) [PerfectField k] {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hKK' : K ≤ K') {w : Place k (modularFunctionFieldC k N)} (c : R.NodeCoordinates K w) : R.NodeCoordinates K' w where
  x := ⟨c.x.1, nodeIntegersOver_mono R hKK' w c.x.2⟩
  y := ⟨c.y.1, nodeIntegersOver_mono R hKK' w c.y.2⟩
  x_fst := c.x_fst
  x_snd := c.x_snd
  y_snd := c.y_snd
  y_fst := c.y_fst

omit [Fact q.Prime] [CharP k q] in
private theorem range_redRestrict_mono {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K') {a : k}
    (ha : a ∈ Set.range (NodeLocalized.redRestrict red K)) : a ∈ Set.range (NodeLocalized.redRestrict red K') := by
  obtain ⟨z, rfl⟩ := ha
  exact ⟨⟨(z : AlgebraicClosure ℚ), z.2.1, hKK' z.2.2⟩, rfl⟩

end

private theorem evalAt_eq_of_hasValue {K L : Type*} [Field K] [Field L] [Algebra K L] (v : Place K L) {g : L} {a : K}
    (h : v.HasValue g a) : v.evalAt g = a := by
  rw [v.evalAt_of_mem h.mem, h.residue_eq, v.residueInv_algebraMap]

end KBGlue

section
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

set_option maxHeartbeats 6400000 in
theorem solution
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (hvalA : R.ValueIntegralityLaw w)
    (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K₀]
    (hK₀fix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ K₀, σ z = z)
    (hϖq₀ : ∀ d : ↥(NodeLocalized.coeffSubring A K₀),
        NodeLocalized.redRestrict red K₀ d = 0 ↔
          ∃ d', d = ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) * d')
    (c₁ : R.NodeCoordinates K₀ w) (E₀ : ℕ) (u₀ : ↥(R.nodeIntegersOver K₀ w)) (hu₀ : IsUnit u₀)
    (hxy₁ : c₁.x * c₁.y = R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) ^ E₀ * u₀)
    (c_val : A) (hc : c_val ∈ IsLocalRing.maximalIdeal A)
    (hcE₀ : ∃ m ∈ IsLocalRing.maximalIdeal A, c_val * m = ((q : ℕ) : A) ^ E₀) :
    ∃! V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.reduceFst V = w ∧
        V.HasValue (↑c₁.y : ↥(modularFunctionFieldBar (N * q))) (c_val : AlgebraicClosure ℚ) := by
  classical
  have hwss : w ∈ ssPlaces q N k := hW w hw
  have hker := KBGlue.red_eq_zero_iff R

  have hXne : (Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero k (Nat.one_lt_pow two_ne_zero (Fact.out : q.Prime).one_lt)
  obtain ⟨KT, hKTfd, -, hKT⟩ :=
    ModularCurve.NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict q A k red
      ((Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots.toFinset) (by
        intro a ha
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hXne, Polynomial.IsRoot.def, Polynomial.eval_sub,
          Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero] at ha
        exact ha)
  haveI := hKTfd
  haveI hK'fd : FiniteDimensional ℚ ↥(K₀ ⊔ KT) := IntermediateField.finiteDimensional_sup K₀ KT
  have hK₀K' : K₀ ≤ K₀ ⊔ KT := le_sup_left
  have hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red (K₀ ⊔ KT)) := fun a ha =>
    KBGlue.range_redRestrict_mono le_sup_right (hKT a (by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hXne, Polynomial.IsRoot.def, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
      exact ha))

  let c' : R.NodeCoordinates (K₀ ⊔ KT) w := KBGlue.enlargeCoordinates R hK₀K' c₁
  obtain ⟨hloc, hnoe⟩ :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.isLocalRing_and_isNoetherianRing_nodeIntegersOver_of_nodeCoordinates_of_orderLawFixed_of_range_redRestrict
      R hqN hmodel hO W hW hreg hval (K₀ ⊔ KT) hk₀ w hw c'
  haveI := hloc
  haveI := hnoe
  have hres : ∀ g : ↥(R.nodeIntegersOver (K₀ ⊔ KT) w), ∃ o : ↥(NodeLocalized.coeffSubring A (K₀ ⊔ KT)),
      ¬ IsUnit (g - R.nodeConst (K₀ ⊔ KT) w o) := fun g =>
    ModularCurve.PlaceSpecialization.ProlongationTuple.exists_not_isUnit_sub_nodeConst_of_evalAt_mem_range_redRestrict_of_orderLawFixed
      R hqN hO W hW hreg (K₀ ⊔ KT) w hw hk₀ g

  obtain ⟨ϖ', hϖ', eK', ε', heK', hε', hqϖ'⟩ :=
    ModularCurve.NodeLocalized.exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul red hker (K₀ ⊔ KT)
  obtain ⟨Wc, _, _, _, _, π, hπ, σ, hσπ, hσ⟩ :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.exists_completeDVR_ringHom_adicCompletion_nodeIntegersOver
      R hqN hker (K₀ ⊔ KT) w hres ϖ' hϖ'
  obtain ⟨E, hE, -, -, -, -, ι, -, -, -, -, hconst, -, -, hres₁, hres₂⟩ :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.exists_exponent_ringEquiv_adicCompletion_nodeIntegersOver_uvCrossingModel
      R hqN hmodel W hW hreg hval hO (K₀ ⊔ KT) w hw ϖ' hϖ' π hπ σ hσπ hσ

  have hu' : IsUnit (R.nodeConst (K₀ ⊔ KT) w ε' ^ E₀ * Subring.inclusion (KBGlue.nodeIntegersOver_mono R hK₀K' w) u₀) :=
    ((hε'.map _).pow _).mul (hu₀.map _)
  have hxy' : c'.x * c'.y = R.nodeConst (K₀ ⊔ KT) w ϖ' ^ (eK' * E₀) *
      (R.nodeConst (K₀ ⊔ KT) w ε' ^ E₀ * Subring.inclusion (KBGlue.nodeIntegersOver_mono R hK₀K' w) u₀) := by
    apply Subtype.ext
    have h1 := congrArg (fun z : ↥(R.nodeIntegersOver K₀ w) => (z : ↥(modularFunctionFieldBar (N * q)))) hxy₁
    have h2 := congrArg (fun z : ↥(NodeLocalized.coeffSubring A (K₀ ⊔ KT)) => (z : AlgebraicClosure ℚ)) hqϖ'
    simp only [Subring.coe_mul, Subring.coe_pow, ProlongationTuple.coe_nodeConst, Subring.coe_inclusion,
      SubringClass.coe_natCast] at h1 h2 ⊢
    change ((c₁.x : ↥(modularFunctionFieldBar (N * q))) : ↥(modularFunctionFieldBar (N * q))) * (c₁.y : ↥(modularFunctionFieldBar (N * q))) = _
    rw [h1, h2, map_mul, map_pow, pow_mul]
    ring

  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  obtain ⟨m, hm, hcm⟩ := hcE₀
  have hcm' : (c_val : AlgebraicClosure ℚ) * (m : AlgebraicClosure ℚ) = ((q : ℕ) : AlgebraicClosure ℚ) ^ E₀ := by
    have := congrArg (fun z : A => (z : AlgebraicClosure ℚ)) hcm
    simpa using this
  have hc0 : (c_val : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0; apply pow_ne_zero E₀ hq0; rw [← hcm', h0, zero_mul]

  have hεA : IsUnit (⟨(ε' : AlgebraicClosure ℚ), ε'.2.1⟩ : A) :=
    hε'.map (Subring.inclusion (inf_le_left : NodeLocalized.coeffSubring A (K₀ ⊔ KT) ≤ A.toSubring))
  obtain ⟨eu, heu⟩ := hεA
  have hdiv : ∃ m' ∈ maximalIdeal A, (ϖ' : AlgebraicClosure ℚ) ^ (eK' * E₀) = (c_val : AlgebraicClosure ℚ) * (m' : AlgebraicClosure ℚ) := by
    refine ⟨m * (((eu⁻¹ : Aˣ) : A) ^ E₀), Ideal.mul_mem_right _ _ hm, ?_⟩
    have h2 := congrArg (fun z : ↥(NodeLocalized.coeffSubring A (K₀ ⊔ KT)) => (z : AlgebraicClosure ℚ)) hqϖ'
    simp only [Subring.coe_mul, Subring.coe_pow, SubringClass.coe_natCast] at h2

    have hinv : ((eu : A) : AlgebraicClosure ℚ) * (((eu⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) = 1 := by
      rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
    have heu' : ((eu : A) : AlgebraicClosure ℚ) = (ε' : AlgebraicClosure ℚ) := by rw [heu]
    rw [heu'] at hinv
    calc (ϖ' : AlgebraicClosure ℚ) ^ (eK' * E₀)
        = (ϖ' : AlgebraicClosure ℚ) ^ (eK' * E₀) * ((ε' : AlgebraicClosure ℚ) * (((eu⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ)) ^ E₀ := by
          rw [hinv, one_pow, mul_one]
      _ = (((ϖ' : AlgebraicClosure ℚ) ^ eK' * (ε' : AlgebraicClosure ℚ)) ^ E₀) * (((eu⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) ^ E₀ := by
          rw [pow_mul]; ring
      _ = (c_val : AlgebraicClosure ℚ) * ((m : AlgebraicClosure ℚ) * (((eu⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) ^ E₀) := by
          rw [← h2, ← hcm']; ring
      _ = (c_val : AlgebraicClosure ℚ) * ((m * ((eu⁻¹ : Aˣ) : A) ^ E₀ : A) : AlgebraicClosure ℚ) := by
          simp

  obtain ⟨V', hV'w, hV'val⟩ :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.exists_reduceFst_eq_and_evalAt_y_eq_of_ringEquiv_uvCrossingModel
      R hqN hmodel hO (K₀ ⊔ KT) w hwss hvalA hres ϖ' hϖ' π hπ σ hσπ E hE ι hconst hres₁ hres₂
      c' (eK' * E₀) _ hu' hxy' c_val hc hc0 hdiv
  have hy : ((c'.y : ↥(modularFunctionFieldBar (N * q))) : ↥(modularFunctionFieldBar (N * q))) = (c₁.y : ↥(modularFunctionFieldBar (N * q))) := rfl
  have hmem : ((c₁.y : ↥(modularFunctionFieldBar (N * q))) : ↥(modularFunctionFieldBar (N * q))) ∈ V'.toValuationSubring :=
    mem_toValuationSubring_of_mem_nodeIntegers R c₁.y.2.1 hV'w
  have hHV : V'.HasValue ((c₁.y : ↥(modularFunctionFieldBar (N * q))) : ↥(modularFunctionFieldBar (N * q))) (c_val : AlgebraicClosure ℚ) := by
    refine ⟨hmem, ?_⟩
    rw [← Place.algebraMap_evalAt V' (ModularCurve.isRational_place_modularFunctionFieldBar (N * q) V') hmem, ← hy, hV'val]

  refine ⟨V', ⟨hV'w, hHV⟩, ?_⟩
  rintro V'' ⟨hV''w, hHV''⟩
  exact ModularCurve.PlaceSpecialization.ProlongationTuple.eq_of_evalAt_y_eq_of_reduceFst_eq_of_ringEquiv_uvCrossingModel
    R hqN hmodel hO (K₀ ⊔ KT) w hwss hvalA hres ϖ' hϖ' π hπ σ hσπ E hE ι hconst hres₁ hres₂
    c' (eK' * E₀) _ hu' hxy' V'' V' hV''w hV'w
    (by rw [hy, KBGlue.evalAt_eq_of_hasValue V'' hHV'', KBGlue.evalAt_eq_of_hasValue V' hHV])

end

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_existsUnique_reduceFst_eq_and_hasValue_y_of_orderLawFixed
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_existsUnique_reduceFst_eq_and_hasValue_y_of_orderLawFixed (solution)
