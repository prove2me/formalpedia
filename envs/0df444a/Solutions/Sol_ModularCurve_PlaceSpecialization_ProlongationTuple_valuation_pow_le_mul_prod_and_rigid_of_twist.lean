-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.valuation_pow_le_mul_prod_and_rigid_of_twist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/4840777f-9586-556c-ab85-f44b0386e521

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_crossingPresentation
import Theorems.Thm_AlgebraicCurve_Annulus_chord_bounds_and_rigid_of_isAttached_both_ends_of_twist
import Theorems.Thm_ValuationSubring_exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_pow_le_mul_prod_and_rigid_of_twist
p2m_attr_erase "instance" "AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ValuationSubring.instIsAlgClosedResidueField AdicCompletion.instIsLocalRingMaximalIdeal GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf"
p2m_attr_erase "instance" "ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.instIsElliptic_tateBase WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar"
p2m_attr_erase "instance" "ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "simp" "AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply"
p2m_attr_erase "simp" "HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
p2m_attr_erase "simp" "ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe"
p2m_attr_erase "simp" "GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.tateUnivCurve_a₂"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace CptMu

variable {L : Type*} [Field L] (A : ValuationSubring L) (μ : AbsoluteValue L ℝ)
  (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
include hμA

theorem valuation_le_iff {a b : L} (hb : b ≠ 0) : A.valuation a ≤ A.valuation b ↔ μ a ≤ μ b := by
  have hvb : A.valuation b ≠ 0 := (Valuation.ne_zero_iff _).mpr hb
  have hμb : 0 < μ b := μ.pos hb
  have key : A.valuation a ≤ A.valuation b ↔ a / b ∈ A := by
    rw [← A.valuation_le_one_iff, map_div₀, div_le_one₀ (zero_lt_iff.mpr hvb)]
  rw [key, hμA, map_div₀, div_le_one hμb]

theorem valuation_eq_iff {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) : A.valuation a = A.valuation b ↔ μ a = μ b := by
  rw [le_antisymm_iff, le_antisymm_iff, valuation_le_iff A μ hμA hb, valuation_le_iff A μ hμA ha]

theorem valuation_lt_iff {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) : A.valuation a < A.valuation b ↔ μ a < μ b := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, valuation_le_iff A μ hμA hb, valuation_le_iff A μ hμA ha]

end CptMu

namespace CptAnn

variable {L F : Type*} [Field L] [Field F] [Algebra L F] {A : ValuationSubring L}

theorem ne_zero_of_ord_ne_zero {v : Place L F} {g : F} (h : v.ord g ≠ 0) : g ≠ 0 := by
  rintro rfl; exact h (Place.ord_zero v)

theorem ord_prod_zpow {ι : Type*} (v : Place L F) (s : Finset ι) (f : ι → F) (n : ι → ℤ)
    (hf : ∀ i ∈ s, f i ≠ 0) : v.ord (∏ i ∈ s, f i ^ n i) = ∑ i ∈ s, n i * v.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      Place.ord_mul v (zpow_ne_zero _ (hf a (Finset.mem_insert_self a s)))
        (Finset.prod_ne_zero_iff.mpr fun i hi => zpow_ne_zero _ (hf i (Finset.mem_insert_of_mem hi))),
      Place.ord_zpow, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem evalAt_param_injOn (An : Annulus A F) {P R : Place L F} (hP : P ∈ An.dom) (hR : R ∈ An.dom)
    (h : P.evalAt An.param = R.evalAt An.param) : P = R := by
  obtain ⟨-, -, ⟨hzRA, hzRm⟩, hzR0, mR, hmR, hmodR⟩ := An.mem_dom R hR
  obtain ⟨Q, -, huniq⟩ := An.existsUnique_evalAt_eq ⟨_, hzRA⟩ hzRm hzR0 ⟨mR, hmR, hmodR⟩
  exact (huniq P ⟨hP, h⟩).trans (huniq R ⟨hR, rfl⟩).symm

theorem ord_param_sub_evalAt_of_ne (An : Annulus A F) {P R : Place L F} (hP : P ∈ An.dom) (hR : R ∈ An.dom)
    (hne : P ≠ R) : P.ord (An.param - algebraMap L F (R.evalAt An.param)) = 0 := by
  obtain ⟨hPrat, hzP, -, -, -⟩ := An.mem_dom P hP
  have hneval : P.evalAt An.param ≠ R.evalAt An.param := fun h => hne (evalAt_param_injOn An hP hR h)
  set g : F := An.param - algebraMap L F (R.evalAt An.param) with hg
  have hgmem : g ∈ P.toValuationSubring := sub_mem hzP (P.algebraMap_mem' _)

  have hres : IsLocalRing.residue P.toValuationSubring ⟨g, hgmem⟩ =
      algebraMap L P.ResidueField (P.evalAt An.param - R.evalAt An.param) := by
    have h1 := P.algebraMap_evalAt hPrat hzP
    have h2 : IsLocalRing.residue P.toValuationSubring ⟨algebraMap L F (R.evalAt An.param), P.algebraMap_mem' _⟩ =
        algebraMap L P.ResidueField (R.evalAt An.param) := (IsScalarTower.algebraMap_apply L P.toValuationSubring P.ResidueField _).symm
    have : (⟨g, hgmem⟩ : P.toValuationSubring) = ⟨An.param, hzP⟩ - ⟨algebraMap L F (R.evalAt An.param), P.algebraMap_mem' _⟩ :=
      Subtype.ext rfl
    rw [this, map_sub, ← h1, h2, map_sub]
  have hunit : IsUnit (⟨g, hgmem⟩ : P.toValuationSubring) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hres, map_ne_zero_iff _ (algebraMap L P.ResidueField).injective]
    exact sub_ne_zero.mpr hneval
  have := P.ord_coe_unit hunit.unit
  rw [IsUnit.unit_spec] at this
  exact this

theorem ord_prod_param_sub_zpow (An : Annulus A F) (e : Place L F →₀ ℤ) (he : ∀ R, e R ≠ 0 → R ∈ An.dom)
    {P : Place L F} (hP : P ∈ An.dom) :
    P.ord (∏ R ∈ e.support, (An.param - algebraMap L F (R.evalAt An.param)) ^ e R) = e P := by
  classical
  have hne : ∀ R ∈ e.support, An.param - algebraMap L F (R.evalAt An.param) ≠ 0 := fun R hR =>
    ne_zero_of_ord_ne_zero (v := R) (by rw [An.ord_param_sub R (he R (Finsupp.mem_support_iff.mp hR))]; exact one_ne_zero)
  rw [ord_prod_zpow P e.support _ _ hne]
  have hterm : ∀ R ∈ e.support, e R * P.ord (An.param - algebraMap L F (R.evalAt An.param)) = if R = P then e P else 0 := by
    intro R hR
    by_cases h : R = P
    · subst h; rw [if_pos rfl, An.ord_param_sub R hP, mul_one]
    · rw [if_neg h, ord_param_sub_evalAt_of_ne An hP (he R (Finsupp.mem_support_iff.mp hR)) (Ne.symm h), mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h).symm

theorem ord_mul_prod_param_sub_zpow (An : Annulus A F) (e : Place L F →₀ ℤ) (he : ∀ R, e R ≠ 0 → R ∈ An.dom)
    {f : F} (hf : f ≠ 0) {P : Place L F} (hP : P ∈ An.dom) :
    P.ord (f * ∏ R ∈ e.support, (An.param - algebraMap L F (R.evalAt An.param)) ^ e R) = P.ord f + e P := by
  classical
  have hne : ∀ R ∈ e.support, An.param - algebraMap L F (R.evalAt An.param) ≠ 0 := fun R hR =>
    ne_zero_of_ord_ne_zero (v := R) (by rw [An.ord_param_sub R (he R (Finsupp.mem_support_iff.mp hR))]; exact one_ne_zero)
  rw [Place.ord_mul P hf (Finset.prod_ne_zero_iff.mpr fun R hR => zpow_ne_zero _ (hne R hR)), ord_prod_param_sub_zpow An e he hP]

end CptAnn

namespace CptLies

theorem liesOverPrime_of_ker {q : ℕ} [Fact q.Prime] {L : Type*} [Field L] [CharZero L] (A : ValuationSubring L)
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) :
    A.LiesOverPrime q := by
  unfold ValuationSubring.LiesOverPrime
  have hqA : ((q : ℕ) : L) ∈ A := natCast_mem A q
  have hred : red ⟨_, hqA⟩ = 0 := by
    have : (⟨((q : ℕ) : L), hqA⟩ : A) = ((q : ℕ) : A) := Subtype.ext (by simp)
    rw [this, map_natCast, CharP.cast_eq_zero]
  have hlt := (A.valuation_lt_one_iff _).mp ((hker _).mp hred)
  exact (A.mem_nonunits_iff).mpr hlt

end CptLies

set_option maxHeartbeats 16000000 in
open ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple in

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
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)

    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) (hVI : R.ValueIntegralityLaw w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (heK : 1 ≤ eK) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (c : R.NodeCoordinates K w) (ew : ℕ) (hew : 1 ≤ ew)
    (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ (ew * eK) * u)
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hbr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
        c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (hnoeth : IsNoetherianRing ↥(R.nodeIntegersOver K w))
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))

    (f : ↥(modularFunctionFieldBar (N * q))) (hf0 : f ≠ 0)
    (c₁ c₂ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ R.R₁.integers) (hr₁ : R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0)
    (h₂ : c₂ • f ∈ R.R₂.integers) (hr₂ : R.R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0)

    (e : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) →₀ ℤ)
    (he : ∀ V, e V ≠ 0 → P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V)
    (hpole : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V → 0 ≤ V.ord f + e V) :

    A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^
        ((ew : ℤ) * (w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + ∑ V ∈ e.support, e V)) ≤
      A.valuation (c₁ * c₂⁻¹) *
        ∏ V ∈ e.support, A.valuation (V.evalAt (c.y : ↥(modularFunctionFieldBar (N * q)))) ^ e V ∧

    A.valuation (c₁ * c₂⁻¹) *
        (∏ V ∈ e.support, A.valuation (V.evalAt (c.y : ↥(modularFunctionFieldBar (N * q)))) ^ e V) *
        A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^
          ((ew : ℤ) * (arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩)) ≤ 1 ∧

    ((A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^
          ((ew : ℤ) * (w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + ∑ V ∈ e.support, e V)) =
        A.valuation (c₁ * c₂⁻¹) *
          ∏ V ∈ e.support, A.valuation (V.evalAt (c.y : ↥(modularFunctionFieldBar (N * q)))) ^ e V ∨
      A.valuation (c₁ * c₂⁻¹) *
          (∏ V ∈ e.support, A.valuation (V.evalAt (c.y : ↥(modularFunctionFieldBar (N * q)))) ^ e V) *
          A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^
            ((ew : ℤ) * (arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩)) = 1) →
      (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
          P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V → V.ord f + e V = 0) ∧
        w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + (∑ V ∈ e.support, e V) +
          (arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩) = 0) := by
  classical

  letI : Algebra (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k N) :=
    ((algebraMap k ↥(modularFunctionFieldC k N)).comp R.redBar).toAlgebra

  obtain ⟨μ, -, -, hμA⟩ := ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime
    (Fact.out : q.Prime) A (CptLies.liesOverPrime_of_ker A red hker)

  obtain ⟨C₁, x₁, C₂, x₂, An₁, An₂, hdom, hmod, hmod0, htwo, hatt₁, hatt₂, hwide, hd0₁, hd0₂, hd1₁, hd1₂, hddom, hd2, hd3⟩ :=
    ProlongationTuple.exists_componentCharts_annuli_isAttached_of_crossingPresentation P hqN hW R hR hRL hNV hO hker K w hw hVI ϖ hϖ eK heK ε hε
      hqϖ c ew hew u hu hxy hmax hbr hnoeth hres μ hμA

  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have hc₁0 : c₁ ≠ 0 := by
    rintro rfl; apply hr₁
    have : (⟨(0 : AlgebraicClosure ℚ) • f, h₁⟩ : R.R₁.integers) = 0 :=
      Subtype.ext (show ((0 : AlgebraicClosure ℚ) • f) = ((0 : R.R₁.integers) : ↥(modularFunctionFieldBar (N * q))) by rw [zero_smul]; rfl)
    rw [this, map_zero]
  have hc₂0 : c₂ ≠ 0 := by
    rintro rfl; apply hr₂
    have : (⟨(0 : AlgebraicClosure ℚ) • f, h₂⟩ : R.R₂.integers) = 0 :=
      Subtype.ext (show ((0 : AlgebraicClosure ℚ) • f) = ((0 : R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))) by rw [zero_smul]; rfl)
    rw [this, map_zero]
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)

  have hC : c₁ • f ∈ C₁.integers := (hd0₁ _).mpr h₁
  have hresT : C₁.residue ⟨c₁ • f, hC⟩ ≠ 0 := (hd1₁ _ hC h₁).1.mpr hr₁
  have hc'0 : c₁ * c₂⁻¹ ≠ 0 := mul_ne_zero hc₁0 (inv_ne_zero hc₂0)
  have hc'f : (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c₁ * c₂⁻¹))⁻¹ * (c₁ • f) = c₂ • f := by
    have hα0 : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c₁ ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).injective).mpr hc₁0
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_inv₀, mul_inv, inv_inv]
    calc (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c₁)⁻¹ * algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c₂ *
          (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c₁ * f)
        = ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c₁)⁻¹ * algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c₁) *
          (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c₂ * f) := by ring
      _ = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c₂ * f := by rw [inv_mul_cancel₀ hα0]; exact one_mul _
  have hC' : (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c₁ * c₂⁻¹))⁻¹ * (c₁ • f) ∈ C₂.integers := by rw [hc'f]; exact (hd0₂ _).mpr h₂
  have hsub : (⟨_, hC'⟩ : C₂.integers) = ⟨c₂ • f, (hd0₂ _).mpr h₂⟩ := Subtype.ext hc'f
  have hres' : C₂.residue ⟨_, hC'⟩ ≠ 0 := by rw [hsub]; exact (hd1₂ _ _ h₂).1.mpr hr₂
  have hD : ∀ V, e V ≠ 0 → V ∈ An₁.dom := fun V hV => (hddom V).mpr (he V hV)
  have hf₁0 : c₁ • f ≠ 0 := smul_ne_zero hc₁0 hf0
  have hordT : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V.ord (c₁ • f) = V.ord f := by
    intro V
    rw [Algebra.smul_def, Place.ord_mul V ((map_ne_zero_iff _ (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).injective).mpr hc₁0) hf0,
      Place.ord_algebraMap, zero_add]
  have hpoleT : ∀ V ∈ An₁.dom, 0 ≤ V.ord (c₁ • f * ∏ R ∈ e.support, (An₁.param - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (R.evalAt An₁.param)) ^ e R) := by
    intro V hV
    rw [CptAnn.ord_mul_prod_param_sub_zpow An₁ e hD hf₁0 hV, hordT]
    obtain ⟨hVw, hs1, hs2⟩ := (hddom V).mp hV
    exact hpole V hVw hs1 hs2

  obtain ⟨T1, T2, T3⟩ := AlgebraicCurve.Annulus.chord_bounds_and_rigid_of_isAttached_both_ends_of_twist μ hμA An₁ An₂ hdom hmod hmod0 htwo
    C₁ x₁ hatt₁ C₂ x₂ hatt₂ hwide (c₁ • f) hC hresT (c₁ * c₂⁻¹) hc'0 hC' hres' e hD hpoleT

  have ho₁ : x₁.ord (C₁.residue ⟨c₁ • f, hC⟩) = w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) := (hd1₁ _ hC h₁).2
  have ho₂ : x₂.ord (C₂.residue ⟨_, hC'⟩) = (arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩) := by
    rw [hsub]; exact (hd1₂ _ _ h₂).2

  have hy0 : ∀ R ∈ An₁.dom, R.evalAt (c.y : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := by
    intro R hR h0
    obtain ⟨-, -, -, hz0, -⟩ := An₁.mem_dom R hR
    have := hd2 R hR
    rw [h0, map_zero, AbsoluteValue.eq_zero] at this
    exact hz0 this

  set o₁ := w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) with ho₁def
  set o₂ := (arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩) with ho₂def
  set M := ∑ V ∈ e.support, e V with hMdef
  set Y : AlgebraicClosure ℚ := ∏ R ∈ e.support, R.evalAt (c.y : ↥(modularFunctionFieldBar (N * q))) ^ e R with hYdef
  have hY0 : Y ≠ 0 := Finset.prod_ne_zero_iff.mpr fun R hR => zpow_ne_zero _ (hy0 R (hD R (Finsupp.mem_support_iff.mp hR)))

  have bΛ : ∏ R ∈ e.support, μ (R.evalAt An₁.param) ^ e R = μ Y := by
    rw [hYdef, map_prod]
    exact Finset.prod_congr rfl fun R hR => by rw [map_zpow₀, hd2 R (hD R (Finsupp.mem_support_iff.mp hR))]
  have bmod : ∀ n : ℤ, μ (An₁.modulus : AlgebraicClosure ℚ) ^ n = μ (((q : ℕ) : AlgebraicClosure ℚ) ^ ((ew : ℤ) * n)) := fun n => by
    rw [map_zpow₀, zpow_mul, zpow_natCast, hd3]

  have vY : A.valuation Y = ∏ R ∈ e.support, A.valuation (R.evalAt (c.y : ↥(modularFunctionFieldBar (N * q)))) ^ e R := by
    rw [hYdef, map_prod]; simp_rw [map_zpow₀]

  have H1 : A.valuation (((q : ℕ) : AlgebraicClosure ℚ) ^ ((ew : ℤ) * (o₁ + M))) ≤ A.valuation ((c₁ * c₂⁻¹) * Y) := by
    apply (CptMu.valuation_le_iff A μ hμA (mul_ne_zero hc'0 hY0)).mpr
    rw [← bmod, map_mul, ← bΛ, ← ho₁]
    exact T1
  have R1 := H1
  rw [map_zpow₀, map_mul, vY] at R1

  have H2 : A.valuation ((c₁ * c₂⁻¹) * Y * ((q : ℕ) : AlgebraicClosure ℚ) ^ ((ew : ℤ) * o₂)) ≤ A.valuation (1 : AlgebraicClosure ℚ) := by
    apply (CptMu.valuation_le_iff A μ hμA one_ne_zero).mpr
    rw [map_mul, map_mul, ← bΛ, ← bmod, map_one, ← ho₂]
    exact T2
  have R2 := H2
  rw [map_mul, map_mul, map_zpow₀, vY, map_one] at R2

  refine ⟨R1, R2, fun hEq => ?_⟩
  have hEqT : μ (An₁.modulus : AlgebraicClosure ℚ) ^ (x₁.ord (C₁.residue ⟨c₁ • f, hC⟩) + ∑ R ∈ e.support, e R)
        = μ (c₁ * c₂⁻¹) * ∏ R ∈ e.support, μ (R.evalAt An₁.param) ^ e R ∨
      μ (c₁ * c₂⁻¹) * (∏ R ∈ e.support, μ (R.evalAt An₁.param) ^ e R) *
          μ (An₁.modulus : AlgebraicClosure ℚ) ^
            (x₂.ord (C₂.residue ⟨(algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c₁ * c₂⁻¹))⁻¹ * (c₁ • f), hC'⟩)) = 1 := by
    rcases hEq with h | h
    · left
      have h' : A.valuation (((q : ℕ) : AlgebraicClosure ℚ) ^ ((ew : ℤ) * (o₁ + M))) = A.valuation ((c₁ * c₂⁻¹) * Y) := by
        rw [map_zpow₀, map_mul, vY]; exact h
      have h'' := (CptMu.valuation_eq_iff A μ hμA (zpow_ne_zero _ hq0) (mul_ne_zero hc'0 hY0)).mp h'
      rw [← bmod, map_mul, ← bΛ, ← ho₁] at h''
      exact h''
    · right
      have h' : A.valuation ((c₁ * c₂⁻¹) * Y * ((q : ℕ) : AlgebraicClosure ℚ) ^ ((ew : ℤ) * o₂)) = A.valuation (1 : AlgebraicClosure ℚ) := by
        rw [map_mul, map_mul, map_zpow₀, vY, map_one]; exact h
      have h'' := (CptMu.valuation_eq_iff A μ hμA (mul_ne_zero (mul_ne_zero hc'0 hY0) (zpow_ne_zero _ hq0)) one_ne_zero).mp h'
      rw [map_mul, map_mul, ← bΛ, ← bmod, map_one, ← ho₂] at h''
      exact h''
  obtain ⟨hzero, hsum⟩ := T3 hEqT
  refine ⟨fun V hVw hs1 hs2 => ?_, ?_⟩
  · have hV : V ∈ An₁.dom := (hddom V).mpr ⟨hVw, hs1, hs2⟩
    have hz := hzero V hV
    rwa [CptAnn.ord_mul_prod_param_sub_zpow An₁ e hD hf₁0 hV, hordT] at hz
  · rw [ho₁, ho₂] at hsum
    exact hsum

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_pow_le_mul_prod_and_rigid_of_twist
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_pow_le_mul_prod_and_rigid_of_twist (solution)
