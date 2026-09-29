-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentCharts_annuli_isAttached_of_crossingPresentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/30fe4382-c222-5a9e-a146-dd32d33e756c

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_annulus_dom_iff_reduceFst_eq_and_param_eq_y_of_ringEquiv_uvCrossingModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_exponent_ringEquiv_adicCompletion_nodeIntegersOver_uvCrossingModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_reduceFst_eq_and_evalAt_y_eq_of_ringEquiv_uvCrossingModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isAttached_fst_of_ringEquiv_uvCrossingModel_of_regularityLaw
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isAttached_snd_of_ringEquiv_uvCrossingModel_of_regularityLaw
import Theorems.Thm_ModularCurve_arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentChart_fst_of_isModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentChart_snd_of_isModel
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces_univ
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_completeDVR_ringHom_adicCompletion_nodeIntegersOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_crossingPresentation
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

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace ChartOkAbv

set_option autoImplicit false

variable {L : Type*} [Field L] (A : ValuationSubring L) (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
include hμA

theorem abv_lt_one_iff_inv_not_mem {a : L} (ha : a ≠ 0) : μ a < 1 ↔ a⁻¹ ∉ A := by
  rw [hμA, not_le, map_inv₀, one_lt_inv₀ (μ.pos ha)]

theorem abv_lt_one_iff_mem_maximalIdeal {a : L} (haA : a ∈ A) (ha : a ≠ 0) :
    μ a < 1 ↔ (⟨a, haA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
  rw [abv_lt_one_iff_inv_not_mem A μ hμA ha, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro h hu
    apply h
    have hmul : ((hu.unit⁻¹ : Aˣ) : A).1 * a = 1 := by
      have h' := congrArg Subtype.val hu.unit.inv_mul
      rw [IsUnit.unit_spec] at h'
      exact h'
    have : ((hu.unit⁻¹ : Aˣ) : A).1 = a⁻¹ := eq_inv_of_mul_eq_one_left hmul
    rw [← this]; exact Subtype.mem _
  · intro h hinv
    exact h ⟨⟨⟨a, haA⟩, ⟨a⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha), Subtype.ext (inv_mul_cancel₀ ha)⟩, rfl⟩

theorem abv_le_abv_iff_div_mem {b c : L} (hc : c ≠ 0) : μ b ≤ μ c ↔ b / c ∈ A := by
  rw [hμA, map_div₀, div_le_one (μ.pos hc)]

theorem abv_zpow_le_iff {x c : L} (hc : c ≠ 0) (n : ℤ) : μ x ^ n ≤ μ c ↔ x ^ n / c ∈ A := by
  rw [← map_zpow₀, abv_le_abv_iff_div_mem A μ hμA hc]

theorem abv_le_zpow_iff {x c : L} (hx : x ≠ 0) (n : ℤ) : μ c ≤ μ x ^ n ↔ c / x ^ n ∈ A := by
  rw [← map_zpow₀, abv_le_abv_iff_div_mem A μ hμA (zpow_ne_zero n hx)]

end ChartOkAbv

namespace C4Skel

theorem not_strict_of_reduceFst_mem
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) {w : Place k ↥(modularFunctionFieldC k N)} (hw : w ∈ ssPlaces q N k) (hV : P.reduceFst V = w) :
    ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V := by
  have hφ : ∀ v : Place k ↥(modularFunctionFieldC k N), frobOnPlacesGeomLevel k N data hKr v = arithFrobC q k N • v :=
    fun v => (ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr v).symm
  have hfix2 : arithFrobC q k N • (arithFrobC q k N • w) = w :=
    ModularCurve.arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces q N hqN k w hw
  constructor
  · rintro ⟨-, h2⟩
    apply h2
    rw [hφ, hφ, hV]
    exact hfix2
  · rintro ⟨h1, h2⟩
    apply h2
    rw [hφ] at h1
    rw [hφ, hφ]
    have h3 : arithFrobC q k N • P.reduceSnd V = w := h1.symm.trans hV
    have hinj : Function.Injective fun v : Place k ↥(modularFunctionFieldC k N) => arithFrobC q k N • v := MulAction.injective _
    have h4 : P.reduceSnd V = arithFrobC q k N • w := hinj (by simp only; rw [h3, hfix2])
    rw [h3, h4]

end C4Skel

set_option maxHeartbeats 16000000 in
theorem C4Skel.assemble
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

    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]

    {Wc : Type*} [CommRing Wc] [IsDomain Wc] [IsDiscreteValuationRing Wc] [IsAdicComplete (maximalIdeal Wc) Wc]
    (π : Wc) (hπ : Irreducible π)
    (σ : Wc →+* AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))
    (hσπ : σ π = algebraMap _ _ (R.nodeConst K w ϖ))
    (hσ : ∀ f : ↥(R.nodeIntegersOver K w), ∃ o : Wc, algebraMap _ (AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)) f - σ o
      ∈ Ideal.map (algebraMap _ (AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))) (maximalIdeal ↥(R.nodeIntegersOver K w)))

    (hy₁ : R.nodeResidue₁ w ⟨(c.y : ↥(modularFunctionFieldBar (N * q))), c.y.2.1⟩ ≠ 0 ∧ w.ord (R.nodeResidue₁ w ⟨(c.y : ↥(modularFunctionFieldBar (N * q))), c.y.2.1⟩) = 1)
    (hx₂ : R.nodeResidue₂ w ⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1⟩ ≠ 0 ∧ (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1⟩) = 1)

    :
    letI : Algebra (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k N) :=
      ((algebraMap k ↥(modularFunctionFieldC k N)).comp R.redBar).toAlgebra
    ∃ (C₁ : ComponentChart A ↥(modularFunctionFieldBar (N * q)) ↥(modularFunctionFieldC k N)) (x₁ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k N))
      (C₂ : ComponentChart A ↥(modularFunctionFieldBar (N * q)) ↥(modularFunctionFieldC k N)) (x₂ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k N))
      (An₁ An₂ : Annulus A ↥(modularFunctionFieldBar (N * q))),

      An₂.dom = An₁.dom ∧ An₂.modulus = An₁.modulus ∧ ((An₁.modulus : AlgebraicClosure ℚ) ≠ 0) ∧
      An₂.param * An₁.param = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (An₁.modulus : AlgebraicClosure ℚ) ∧
      An₁.IsAttached C₁ x₁ ∧ An₂.IsAttached C₂ x₂ ∧
      (∃ Q₁ ∈ An₁.dom, ∃ Q₂ ∈ An₁.dom, μ (Q₁.evalAt An₁.param) ≠ μ (Q₂.evalAt An₁.param)) ∧

      (∀ f : ↥(modularFunctionFieldBar (N * q)), f ∈ C₁.integers ↔ f ∈ R.R₁.integers) ∧ (∀ f : ↥(modularFunctionFieldBar (N * q)), f ∈ C₂.integers ↔ f ∈ R.R₂.integers) ∧

      (∀ (f : ↥(modularFunctionFieldBar (N * q))) (hC : f ∈ C₁.integers) (h₁ : f ∈ R.R₁.integers),
        (C₁.residue ⟨f, hC⟩ ≠ 0 ↔ R.R₁.residue ⟨f, h₁⟩ ≠ 0) ∧
        x₁.ord (C₁.residue ⟨f, hC⟩) = w.ord (R.residue₁ ⟨f, h₁⟩)) ∧
      (∀ (f : ↥(modularFunctionFieldBar (N * q))) (hC : f ∈ C₂.integers) (h₂ : f ∈ R.R₂.integers),
        (C₂.residue ⟨f, hC⟩ ≠ 0 ↔ R.R₂.residue ⟨f, h₂⟩ ≠ 0) ∧
        x₂.ord (C₂.residue ⟨f, hC⟩) = (arithFrobC q k N • w).ord (R.residue₂ ⟨f, h₂⟩)) ∧

      (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V ∈ An₁.dom ↔ (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V)) ∧

      (∀ V ∈ An₁.dom, μ (V.evalAt An₁.param) = μ (V.evalAt (c.y : ↥(modularFunctionFieldBar (N * q))))) ∧

      μ (An₁.modulus : AlgebraicClosure ℚ) = μ ((q : ℕ) : AlgebraicClosure ℚ) ^ ew  := by
  letI : Algebra (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k N) := ((algebraMap k ↥(modularFunctionFieldC k N)).comp R.redBar).toAlgebra

  have hCF := ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentChart_fst_of_isModel P hqN R hR
  obtain ⟨C₁, rc₁, hbij₁, hval₁, hord₁, hint₁', hresC₁, hdomC₁, hnodes₁, hpm₁⟩ := hCF
  have hCS := ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentChart_snd_of_isModel P hqN R hR
  obtain ⟨C₂, rc₂, hbij₂, hval₂, hord₂, hint₂', hresC₂, hdomC₂, hnodes₂, hpm₂⟩ := hCS

  have hwss : w ∈ ssPlaces q N k := (hW w).mp hw
  have hW₀ : ∀ v ∈ W, v ∈ ssPlaces q N k := fun v hv => (hW v).mp hv
  have hφ : ∀ v : Place k ↥(modularFunctionFieldC k N), frobOnPlacesGeomLevel k N data hKr v = arithFrobC q k N • v :=
    fun v => (ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr v).symm
  have hφw : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w := by
    rw [hφ, hφ]; exact ModularCurve.arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces q N hqN k w hwss
  have hφwss : arithFrobC q k N • w ∈ ssPlaces q N k := ModularCurve.arithFrobC_smul_mem_ssPlaces_univ q N k w hwss
  have hφw' : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (arithFrobC q k N • w)) = arithFrobC q k N • w := by
    rw [hφ, hφ]; exact ModularCurve.arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces q N hqN k _ hφwss
  have hx₁n : rc₁ w ∈ C₁.nodes := (hnodes₁ w).mpr hφw
  have hx₂n : rc₂ (arithFrobC q k N • w) ∈ C₂.nodes := (hnodes₂ _).mpr hφw'

  have hint₁ : ∀ f : ↥(modularFunctionFieldBar (N * q)), f ∈ C₁.integers ↔ f ∈ R.R₁.integers := fun f => by rw [hint₁']
  have hint₂ : ∀ f : ↥(modularFunctionFieldBar (N * q)), f ∈ C₂.integers ↔ f ∈ R.R₂.integers := fun f => by rw [hint₂']
  have hdict₁ : ∀ (f : ↥(modularFunctionFieldBar (N * q))) (hC : f ∈ C₁.integers) (h₁ : f ∈ R.R₁.integers),
      (C₁.residue ⟨f, hC⟩ ≠ 0 ↔ R.R₁.residue ⟨f, h₁⟩ ≠ 0) ∧ (rc₁ w).ord (C₁.residue ⟨f, hC⟩) = w.ord (R.residue₁ ⟨f, h₁⟩) := by
    intro f hC h₁
    rw [hresC₁ f hC h₁, hord₁]
    refine ⟨?_, rfl⟩
    rw [ProlongationTuple.residue₁_apply]
    exact map_ne_zero_iff _ R.ι.injective
  have hdict₂ : ∀ (f : ↥(modularFunctionFieldBar (N * q))) (hC : f ∈ C₂.integers) (h₂ : f ∈ R.R₂.integers),
      (C₂.residue ⟨f, hC⟩ ≠ 0 ↔ R.R₂.residue ⟨f, h₂⟩ ≠ 0) ∧
      (rc₂ (arithFrobC q k N • w)).ord (C₂.residue ⟨f, hC⟩) = (arithFrobC q k N • w).ord (R.residue₂ ⟨f, h₂⟩) := by
    intro f hC h₂
    rw [hresC₂ f hC h₂, hord₂]
    refine ⟨?_, rfl⟩
    rw [ProlongationTuple.residue₂_apply]
    exact map_ne_zero_iff _ R.ι.injective

  have hX := ModularCurve.PlaceSpecialization.ProlongationTuple.exists_exponent_ringEquiv_adicCompletion_nodeIntegersOver_uvCrossingModel
    R hqN hR W hW₀ hRL hNV hO K w hw ϖ hϖ π hπ σ hσπ hσ
  obtain ⟨E, hE, c', u', hu', hxy', ι, α, β, hα, hβ, hrest⟩ := hX
  obtain ⟨hconst, hcx, hcy, hres₁, hres₂⟩ := hrest

  have hAN := ModularCurve.PlaceSpecialization.ProlongationTuple.exists_annulus_dom_iff_reduceFst_eq_and_param_eq_y_of_ringEquiv_uvCrossingModel
    R hqN hR hO K w hwss hVI hres ϖ hϖ π hπ σ hσπ E hE ι hconst hres₁ hres₂ c (ew * eK) u hu hxy
  obtain ⟨An, An', hdom, hdomAn', hmodAn', hmodϖ, hparam, hprod⟩ := hAN
  have hdomAn'' : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V' ∈ An'.dom ↔ (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V') :=
    fun V' => by rw [hdomAn']; exact hdom V'
  have hmod'' : (An'.modulus : AlgebraicClosure ℚ) = (ϖ : AlgebraicClosure ℚ) ^ (ew * eK) := by rw [hmodAn', hmodϖ]
  have hparam' : An'.param * (↑c.y : ↥(modularFunctionFieldBar (N * q))) = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((ϖ : AlgebraicClosure ℚ) ^ (ew * eK)) := by
    rw [← hparam, hprod, hmodϖ]

  have hatt₁ := ModularCurve.PlaceSpecialization.ProlongationTuple.isAttached_fst_of_ringEquiv_uvCrossingModel_of_regularityLaw
    R hqN hR hO K w hwss hVI W hw hRL hres ϖ hϖ π hπ σ hσπ E hE ι hconst hres₁ hres₂ c (ew * eK) u hu hxy hy₁ An hdom hparam hmodϖ
    C₁ (rc₁ w) hx₁n hint₁ hdict₁
  have hatt₂ := ModularCurve.PlaceSpecialization.ProlongationTuple.isAttached_snd_of_ringEquiv_uvCrossingModel_of_regularityLaw
    R hqN hR hO K w hwss hVI W hw hRL hres ϖ hϖ π hπ σ hσπ E hE ι hconst hres₁ hres₂ c (ew * eK) u hu hxy hx₂ An' hdomAn'' hparam' hmod''
    C₂ (rc₂ (arithFrobC q k N • w)) hx₂n hint₂ hdict₂

  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have hqϖQ : ((q : ℕ) : AlgebraicClosure ℚ) = (ϖ : AlgebraicClosure ℚ) ^ eK * (ε : AlgebraicClosure ℚ) := by
    have h1 := congrArg Subtype.val hqϖ
    simp only [Subring.coe_natCast, Subring.coe_mul, SubmonoidClass.coe_pow] at h1
    exact h1
  have hϖ0 : (ϖ : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    apply hq0
    rw [hqϖQ, h0, zero_pow (by omega), zero_mul]
  have hS3 : (An.modulus : AlgebraicClosure ℚ) ≠ 0 := by
    rw [hmodϖ]; exact pow_ne_zero _ hϖ0

  have hεA : (ε : AlgebraicClosure ℚ) ∈ A := ε.2.1
  have hμε : μ (ε : AlgebraicClosure ℚ) = 1 := by
    obtain ⟨εu, hεu⟩ := hε
    apply le_antisymm ((hμA _).mp hεA)
    have hinvA : ((εu⁻¹ : (↥(NodeLocalized.coeffSubring A K))ˣ) : ↥(NodeLocalized.coeffSubring A K)).1 ∈ A := (εu⁻¹ : (↥(NodeLocalized.coeffSubring A K))ˣ).1.2.1
    have hprod1 : (ε : AlgebraicClosure ℚ) * ((εu⁻¹ : (↥(NodeLocalized.coeffSubring A K))ˣ) : ↥(NodeLocalized.coeffSubring A K)).1 = 1 := by
      have := congrArg (fun z : ↥(NodeLocalized.coeffSubring A K) => (z : AlgebraicClosure ℚ)) εu.mul_inv
      simpa [hεu] using this
    have h1 : μ ((ε : AlgebraicClosure ℚ) * ((εu⁻¹ : (↥(NodeLocalized.coeffSubring A K))ˣ) : ↥(NodeLocalized.coeffSubring A K)).1) = 1 := by
      rw [hprod1, map_one]
    rw [map_mul] at h1
    have hle : μ (((εu⁻¹ : (↥(NodeLocalized.coeffSubring A K))ˣ) : ↥(NodeLocalized.coeffSubring A K)).1) ≤ 1 := (hμA _).mp hinvA
    have hpos : 0 ≤ μ (ε : AlgebraicClosure ℚ) := μ.nonneg _
    nlinarith
  have hϖm : (⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    rw [← hker]
    have h := (hϖ ϖ).mpr ⟨1, (mul_one _).symm⟩
    exact h
  have hμϖ : μ (ϖ : AlgebraicClosure ℚ) < 1 := (ChartOkAbv.abv_lt_one_iff_mem_maximalIdeal A μ hμA ϖ.2.1 hϖ0).mpr hϖm
  have hd3 : μ (An.modulus : AlgebraicClosure ℚ) = μ ((q : ℕ) : AlgebraicClosure ℚ) ^ ew := by
    rw [hmodϖ, hqϖQ, map_mul, hμε, mul_one, map_pow, map_pow, ← pow_mul, mul_comm]

  have hE₀ : 1 ≤ ew * eK := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq ((ϖ : AlgebraicClosure ℚ) ^ (ew * eK)) two_pos
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq t two_pos
  have hμmod : μ ((ϖ : AlgebraicClosure ℚ) ^ (ew * eK)) < 1 := by
    rw [map_pow]; exact pow_lt_one₀ (μ.nonneg _) hμϖ (by omega)
  have ht0 : t ≠ 0 := by
    intro h0; apply pow_ne_zero (ew * eK) hϖ0; rw [← ht, h0]; norm_num
  have hs0 : s ≠ 0 := by
    intro h0; apply ht0; rw [← hs, h0]; norm_num
  have hμt : μ t < 1 := by
    have h2 : μ t ^ 2 < 1 := by rw [← map_pow, ht]; exact hμmod
    nlinarith [μ.nonneg t]
  have hμs : μ s < 1 := by
    have h2 : μ s ^ 2 < 1 := by rw [← map_pow, hs]; exact hμt
    nlinarith [μ.nonneg s]
  have hμspos : 0 < μ s := μ.pos hs0
  have htA : t ∈ A := (hμA t).mpr hμt.le
  have hsA : s ∈ A := (hμA s).mpr hμs.le
  have htm : (⟨t, htA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := (ChartOkAbv.abv_lt_one_iff_mem_maximalIdeal A μ hμA htA ht0).mp hμt
  have hsm : (⟨s, hsA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := (ChartOkAbv.abv_lt_one_iff_mem_maximalIdeal A μ hμA hsA hs0).mp hμs
  have hEX := ModularCurve.PlaceSpecialization.ProlongationTuple.exists_reduceFst_eq_and_evalAt_y_eq_of_ringEquiv_uvCrossingModel
    R hqN hR hO K w hwss hVI hres ϖ hϖ π hπ σ hσπ E hE ι hconst hres₁ hres₂ c (ew * eK) u hu hxy
  obtain ⟨Q₁, hQ₁w, hQ₁v⟩ := hEX ⟨t, htA⟩ htm ht0 ⟨⟨t, htA⟩, htm, by rw [← ht]; ring⟩
  obtain ⟨Q₂, hQ₂w, hQ₂v⟩ := hEX ⟨s, hsA⟩ hsm hs0 ⟨⟨s, hsA⟩ ^ 3, Ideal.pow_mem_of_mem _ hsm 3 (by norm_num), by
    rw [← ht, ← hs]; push_cast; ring⟩
  have hQ₁d : Q₁ ∈ An.dom := (hdom Q₁).mpr ⟨hQ₁w, C4Skel.not_strict_of_reduceFst_mem P hqN Q₁ hwss hQ₁w⟩
  have hQ₂d : Q₂ ∈ An.dom := (hdom Q₂).mpr ⟨hQ₂w, C4Skel.not_strict_of_reduceFst_mem P hqN Q₂ hwss hQ₂w⟩
  have hS7 : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, μ (Q₁.evalAt An.param) ≠ μ (Q₂.evalAt An.param) := by
    refine ⟨Q₁, hQ₁d, Q₂, hQ₂d, ?_⟩
    rw [hparam, hQ₁v, hQ₂v]
    change μ t ≠ μ s
    intro hts
    have : μ t = μ s ^ 2 := by rw [← map_pow, hs]
    rw [this] at hts
    nlinarith
  refine ⟨C₁, rc₁ w, C₂, rc₂ (arithFrobC q k N • w), An, An', hdomAn', hmodAn', hS3, hprod, hatt₁, hatt₂, hS7,
    hint₁, hint₂, hdict₁, hdict₂, hdom, ?_, hd3⟩
  intro V hV
  rw [hparam]

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

    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) :
    letI : Algebra (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k N) :=
      ((algebraMap k ↥(modularFunctionFieldC k N)).comp R.redBar).toAlgebra
    ∃ (C₁ : ComponentChart A ↥(modularFunctionFieldBar (N * q)) ↥(modularFunctionFieldC k N)) (x₁ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k N))
      (C₂ : ComponentChart A ↥(modularFunctionFieldBar (N * q)) ↥(modularFunctionFieldC k N)) (x₂ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k N))
      (An₁ An₂ : Annulus A ↥(modularFunctionFieldBar (N * q))),

      An₂.dom = An₁.dom ∧ An₂.modulus = An₁.modulus ∧ ((An₁.modulus : AlgebraicClosure ℚ) ≠ 0) ∧
      An₂.param * An₁.param = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (An₁.modulus : AlgebraicClosure ℚ) ∧
      An₁.IsAttached C₁ x₁ ∧ An₂.IsAttached C₂ x₂ ∧
      (∃ Q₁ ∈ An₁.dom, ∃ Q₂ ∈ An₁.dom, μ (Q₁.evalAt An₁.param) ≠ μ (Q₂.evalAt An₁.param)) ∧

      (∀ f : ↥(modularFunctionFieldBar (N * q)), f ∈ C₁.integers ↔ f ∈ R.R₁.integers) ∧ (∀ f : ↥(modularFunctionFieldBar (N * q)), f ∈ C₂.integers ↔ f ∈ R.R₂.integers) ∧

      (∀ (f : ↥(modularFunctionFieldBar (N * q))) (hC : f ∈ C₁.integers) (h₁ : f ∈ R.R₁.integers),
        (C₁.residue ⟨f, hC⟩ ≠ 0 ↔ R.R₁.residue ⟨f, h₁⟩ ≠ 0) ∧
        x₁.ord (C₁.residue ⟨f, hC⟩) = w.ord (R.residue₁ ⟨f, h₁⟩)) ∧
      (∀ (f : ↥(modularFunctionFieldBar (N * q))) (hC : f ∈ C₂.integers) (h₂ : f ∈ R.R₂.integers),
        (C₂.residue ⟨f, hC⟩ ≠ 0 ↔ R.R₂.residue ⟨f, h₂⟩ ≠ 0) ∧
        x₂.ord (C₂.residue ⟨f, hC⟩) = (arithFrobC q k N • w).ord (R.residue₂ ⟨f, h₂⟩)) ∧

      (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V ∈ An₁.dom ↔ (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V)) ∧

      (∀ V ∈ An₁.dom, μ (V.evalAt An₁.param) = μ (V.evalAt (c.y : ↥(modularFunctionFieldBar (N * q))))) ∧

      μ (An₁.modulus : AlgebraicClosure ℚ) = μ ((q : ℕ) : AlgebraicClosure ℚ) ^ ew := by

  haveI : IsLocalRing ↥(R.nodeIntegersOver K w) := IsLocalRing.of_unique_max_ideal ⟨_, hmax.1, fun M hM => hmax.2 M hM⟩
  haveI : IsNoetherianRing ↥(R.nodeIntegersOver K w) := hnoeth

  obtain ⟨Wc, i1, i2, i3, i4, π, hπ, σ, hσπ, hσ⟩ :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.exists_completeDVR_ringHom_adicCompletion_nodeIntegersOver R hqN hker K w hres ϖ hϖ

  have hy₁ : R.nodeResidue₁ w ⟨(c.y : ↥(modularFunctionFieldBar (N * q))), c.y.2.1⟩ ≠ 0 ∧
      w.ord (R.nodeResidue₁ w ⟨(c.y : ↥(modularFunctionFieldBar (N * q))), c.y.2.1⟩) = 1 :=
    ⟨c.nodeResidue₁_y_ne_zero, c.y_fst⟩
  have hx₂ : R.nodeResidue₂ w ⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1⟩ ≠ 0 ∧
      (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1⟩) = 1 :=
    ⟨c.nodeResidue₂_x_ne_zero, c.x_snd⟩
  exact C4Skel.assemble P hqN hW R hR hRL hNV hO hker K w hw hVI ϖ hϖ eK heK ε hε hqϖ c ew hew u hu hxy hmax hbr hnoeth hres μ hμA
    π hπ σ hσπ hσ hy₁ hx₂

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_crossingPresentation
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_crossingPresentation (solution)
