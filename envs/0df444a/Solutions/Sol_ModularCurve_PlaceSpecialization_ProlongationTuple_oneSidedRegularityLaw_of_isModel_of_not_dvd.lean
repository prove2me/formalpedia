-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.oneSidedRegularityLaw_of_isModel_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/bd80a18d-6cb6-576f-a627-733297b95ad5

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ProlongationTuple_JumpLaw
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_arithmeticGalois_smul
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_geomAut
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_prolongationTuple_isModel_regularityLaw_nodeValueLaw
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_prolongationTuple_isModel_regularityLaw_nodeValueLaw_level_one
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_prolongationTuple_isModel_and_orderLawFixed_of_not_genusFF_pos
import Theorems.Thm_ModularCurve_PlaceSpecialization_red_surjective_of_level
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictFst_iff_and_isStrictSnd_iff_of_isModel_of_isModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_oneSidedRegularityLaw_of_isModel_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.numberField_of_finiteDimensional WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ValuationSubring.instIsAlgClosedResidueField instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC"
p2m_attr_erase "instance" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero"
p2m_attr_erase "simp" "compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁"
p2m_attr_erase "simp" "FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁"
p2m_attr_erase "simp" "TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.eisensteinNumerator_nineteen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.symPoly_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_levelPolynomialEquiv_apply ModularCurve.coe_levelBaseRingDescent_apply ModularCurve.levelConst_apply ModularCurve.coe_laurentDescent_apply ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk"
p2m_attr_erase "simp" "ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.coe_nodeConst ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₁_apply AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of"
p2m_attr_erase "simp" "AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of"
set_option Elab.async false
set_option autoImplicit false

p2m_open "AlgebraicCurve~genus IsLocalRing ModularCurve~period ModularCurve.PlaceSpecialization"

namespace InertialNormDescent

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private noncomputable def normPow (τ : SemilinearAut K F) (f : F) (n : ℕ) : F :=
  ∏ i ∈ Finset.range n, τ ^ i • f

private theorem pow_smul_ne_zero (τ : SemilinearAut K F) {f : F} (hf : f ≠ 0) (i : ℕ) : τ ^ i • f ≠ 0 := by
  intro h
  apply hf
  exact MulAction.injective (τ ^ i) (h.trans (smul_zero (τ ^ i)).symm)

private theorem ord_pow_smul (τ : SemilinearAut K F) (f : F) (i : ℕ) (V : Place K F) :
    V.ord (τ ^ i • f) = ((τ ^ i)⁻¹ • V).ord f := by
  have h := SemilinearAut.ord_smul (τ ^ i) ((τ ^ i)⁻¹ • V) f
  rwa [smul_inv_smul] at h

private theorem ord_normPow (τ : SemilinearAut K F) {f : F} (hf : f ≠ 0) (n : ℕ) (V : Place K F) :
    V.ord (normPow τ f n) = ∑ i ∈ Finset.range n, ((τ ^ i)⁻¹ • V).ord f := by
  induction n with
  | zero => simp [normPow]
  | succ n ih =>
    have hprod : normPow τ f n ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => pow_smul_ne_zero τ hf i
    rw [normPow, Finset.prod_range_succ, ← normPow, V.ord_mul hprod (pow_smul_ne_zero τ hf n), ih,
      Finset.sum_range_succ, ord_pow_smul]

private theorem ord_pow_nat (V : Place K F) (x : F) (n : ℕ) : V.ord (x ^ n) = n * V.ord x := by
  rw [← zpow_natCast, V.ord_zpow]

private theorem ord_normPow_eq_sub (τ : SemilinearAut K F) {f : F} (hf : f ≠ 0) (D E : Divisor K F)
    (hdiv : ∀ V : Place K F, D V + (τ • E - E) V = V.ord f) (V : Place K F)
    (hD : ∀ i : ℕ, D ((τ ^ i)⁻¹ • V) = 0) (m : ℕ) :
    V.ord (normPow τ f m) = E ((τ ^ m)⁻¹ • V) - E V := by
  have hterm : ∀ i : ℕ, ((τ ^ i)⁻¹ • V).ord f = E ((τ ^ (i + 1))⁻¹ • V) - E ((τ ^ i)⁻¹ • V) := by
    intro i
    rw [← hdiv, hD i, zero_add, Finsupp.sub_apply, SemilinearAut.divisor_smul_apply, pow_succ,
      mul_inv_rev, mul_smul]
  calc V.ord (normPow τ f m) = ∑ i ∈ Finset.range m, ((τ ^ i)⁻¹ • V).ord f := ord_normPow τ hf m V
    _ = ∑ i ∈ Finset.range m, (E ((τ ^ (i + 1))⁻¹ • V) - E ((τ ^ i)⁻¹ • V)) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = E ((τ ^ m)⁻¹ • V) - E ((τ ^ 0)⁻¹ • V) := Finset.sum_range_sub (fun j => E ((τ ^ j)⁻¹ • V)) m
    _ = E ((τ ^ m)⁻¹ • V) - E V := by rw [pow_zero, inv_one, one_smul]

private theorem pow_mul_smul_eq_self (τ : SemilinearAut K F) {f : F} {n : ℕ} (hper : τ ^ n • f = f) (m : ℕ) :
    τ ^ (n * m) • f = f := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, pow_add, mul_smul, hper, ih]

private theorem normPow_mul (τ : SemilinearAut K F) {f : F} {n : ℕ} (hper : τ ^ n • f = f) (m : ℕ) :
    normPow τ f (n * m) = normPow τ f n ^ m := by
  induction m with
  | zero => simp [normPow]
  | succ m ih =>
    rw [pow_succ, ← ih]
    simp only [normPow]
    rw [Nat.mul_succ, Finset.prod_range_add]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [add_comm, pow_add, mul_smul, pow_mul_smul_eq_self τ hper m]

private theorem exists_abs_apply_le (E : Divisor K F) : ∃ B : ℤ, ∀ X : Place K F, |E X| ≤ B := by
  refine ⟨∑ Y ∈ E.support, |E Y|, fun X => ?_⟩
  by_cases hX : X ∈ E.support
  · exact Finset.single_le_sum (f := fun Y => |E Y|) (fun Y _ => abs_nonneg (E Y)) hX
  · have h0 : E X = 0 := by
      by_contra h
      exact hX (Finsupp.mem_support_iff.mpr h)
    rw [h0, abs_zero]
    exact Finset.sum_nonneg fun Y _ => abs_nonneg (E Y)

private theorem ord_normPow_eq_zero (τ : SemilinearAut K F) {f : F} (hf : f ≠ 0) (D E : Divisor K F)
    (hdiv : ∀ V : Place K F, D V + (τ • E - E) V = V.ord f) {n : ℕ} (hper : τ ^ n • f = f)
    (V : Place K F) (hD : ∀ i : ℕ, D ((τ ^ i)⁻¹ • V) = 0) : V.ord (normPow τ f n) = 0 := by
  obtain ⟨B, hB⟩ := exists_abs_apply_le E
  by_contra ho
  have hone : 1 ≤ |V.ord (normPow τ f n)| := Int.one_le_abs ho
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 * B < (m : ℤ) :=
    ⟨(2 * B).toNat + 1, by push_cast; have := Int.self_le_toNat (2 * B); omega⟩
  have h1 := ord_normPow_eq_sub τ hf D E hdiv V hD (n * m)
  rw [normPow_mul τ hper m, ord_pow_nat] at h1
  have h2 : |E ((τ ^ (n * m))⁻¹ • V) - E V| ≤ 2 * B := by
    calc |E ((τ ^ (n * m))⁻¹ • V) - E V| ≤ |E ((τ ^ (n * m))⁻¹ • V)| + |E V| := abs_sub _ _
      _ ≤ B + B := add_le_add (hB _) (hB V)
      _ = 2 * B := by ring
  rw [← h1, abs_mul, Nat.abs_cast] at h2
  have h3 : (m : ℤ) ≤ (m : ℤ) * |V.ord (normPow τ f n)| :=
    le_mul_of_one_le_right (by positivity) hone
  linarith

private theorem pos_of_natCast_mul_pos {n : ℕ} {o : ℤ} (h : 0 < (n : ℤ) * o) : 0 < o := by
  nlinarith [h, (Nat.cast_nonneg n : (0 : ℤ) ≤ n)]

private theorem ord_pos_of_hasValue_zero {V : Place K F} {x : F} (h : V.HasValue x 0) (hx : x ≠ 0) :
    0 < V.ord x := by
  obtain ⟨hmem, hres⟩ := (Place.hasValue_iff V x 0).mp h
  rw [map_zero] at hres
  exact (V.mem_maximalIdeal_iff_ord_pos hx hmem).mp ((IsLocalRing.residue_eq_zero_iff _).mp hres)

private theorem ord_pos_of_hasValue_pow_of_eq_zero {V₁ V₂ : Place K F} {x y : F} {n : ℕ} (hn : 0 < n)
    {c : K} (hc₁ : V₁.HasValue (x ^ n) c) (hc₂ : V₂.HasValue (y ^ n) c) (hx : x ≠ 0) (hy : y = 0) :
    0 < V₁.ord x := by
  rw [hy, zero_pow hn.ne'] at hc₂
  have h00 : V₂.HasValue (0 : F) 0 := by simpa using V₂.hasValue_algebraMap 0
  rw [hc₂.unique h00] at hc₁
  have hpos := ord_pos_of_hasValue_zero hc₁ (pow_ne_zero n hx)
  rw [ord_pow_nat] at hpos
  exact pos_of_natCast_mul_pos hpos

end Generic

section Series

variable {L : Type*} [Field L] [Algebra ℚ L]

private theorem coeffMap_pow_eq_self (τ : L ≃ₐ[ℚ] L) {x : LaurentSeries L}
    (hx : coeffMap (τ : L →+* L) x = x) (m : ℕ) :
    coeffMap ((τ ^ m : L ≃ₐ[ℚ] L) : L →+* L) x = x := by
  induction m with
  | zero =>
      rw [show (((τ ^ 0 : L ≃ₐ[ℚ] L)) : L →+* L) = RingHom.id L from RingHom.ext fun _ => rfl, coeffMap_id]
  | succ m ih =>
      have h : coeffMap (((τ ^ (m + 1) : L ≃ₐ[ℚ] L)) : L →+* L) x
          = coeffMap ((τ ^ m : L ≃ₐ[ℚ] L) : L →+* L) (coeffMap (τ : L →+* L) x) := by
        rw [coeffMap_coeffMap]
        exact coeffMap_congr (RingHom.ext fun c => by simp [pow_succ, AlgEquiv.mul_apply]) x
      rw [h, hx, ih]

private theorem exists_pow_apply_eq_self [Algebra.IsAlgebraic ℚ L] (τ : L ≃ₐ[ℚ] L) (a : L) :
    ∃ n : ℕ, 0 < n ∧ (τ ^ n) a = a := by
  have hint : IsIntegral ℚ a := Algebra.IsIntegral.isIntegral a
  have hmem : ∀ i : ℕ, (τ ^ i) a ∈ (minpoly ℚ a).rootSet L := fun i => by
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [Polynomial.aeval_algEquiv, AlgHom.comp_apply, minpoly.aeval, map_zero]
  obtain ⟨i, j, hij, hfix⟩ := (Polynomial.rootSet_finite (minpoly ℚ a) L).exists_lt_map_eq_of_forall_mem hmem
  refine ⟨j - i, Nat.sub_pos_of_lt hij, (τ ^ i).injective ?_⟩
  rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' hij.le]
  exact hfix.symm

private theorem exists_pow_coeffMap_eq_self [Algebra.IsAlgebraic ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (τ : L ≃ₐ[ℚ] L) {x : LaurentSeries L}
    (hx : x ∈ laurentBaseChange L F₀) :
    ∃ n : ℕ, 0 < n ∧ coeffMap ((τ ^ n : L ≃ₐ[ℚ] L) : L →+* L) x = x := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, _, rfl⟩
      · obtain ⟨n, hn, ha⟩ := exists_pow_apply_eq_self τ a
        exact ⟨n, hn, by rw [coeffMap_algebraMap]; exact congrArg (algebraMap L (LaurentSeries L)) ha⟩
      · exact ⟨1, Nat.one_pos, coeffMap_coeffEmb (τ ^ 1) z⟩
  | one => exact ⟨1, Nat.one_pos, map_one _⟩
  | add x y _ _ hx hy =>
      obtain ⟨n, hn, hxn⟩ := hx
      obtain ⟨m, hm, hym⟩ := hy
      refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
      have hx' : coeffMap ((τ ^ (n * m) : L ≃ₐ[ℚ] L) : L →+* L) x = x := by
        rw [pow_mul]; exact coeffMap_pow_eq_self _ hxn m
      have hy' : coeffMap ((τ ^ (n * m) : L ≃ₐ[ℚ] L) : L →+* L) y = y := by
        rw [mul_comm, pow_mul]; exact coeffMap_pow_eq_self _ hym n
      rw [map_add, hx', hy']
  | neg x _ hx =>
      obtain ⟨n, hn, hxn⟩ := hx
      exact ⟨n, hn, by rw [map_neg, hxn]⟩
  | inv x _ hx =>
      obtain ⟨n, hn, hxn⟩ := hx
      exact ⟨n, hn, by rw [map_inv₀, hxn]⟩
  | mul x y _ _ hx hy =>
      obtain ⟨n, hn, hxn⟩ := hx
      obtain ⟨m, hm, hym⟩ := hy
      refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
      have hx' : coeffMap ((τ ^ (n * m) : L ≃ₐ[ℚ] L) : L →+* L) x = x := by
        rw [pow_mul]; exact coeffMap_pow_eq_self _ hxn m
      have hy' : coeffMap ((τ ^ (n * m) : L ≃ₐ[ℚ] L) : L →+* L) y = y := by
        rw [mul_comm, pow_mul]; exact coeffMap_pow_eq_self _ hym n
      rw [map_mul, hx', hy']

end Series

private theorem exists_pow_smul_eq_self {M : ℕ} (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (f : modularFunctionFieldBar M) :
    ∃ n : ℕ, 0 < n ∧ arithmeticGalois (modularFunctionFieldFull M) σ ^ n • f = f := by
  obtain ⟨n, hn, hfix⟩ := exists_pow_coeffMap_eq_self (modularFunctionFieldFull M) σ f.2
  refine ⟨n, hn, ?_⟩
  rw [← map_pow]
  exact Subtype.ext ((coe_arithmeticGalois_smul (modularFunctionFieldFull M) (σ ^ n) f).trans hfix)

section Modular

variable {q : ℕ} [Fact q.Prime]
  {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
  [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
  {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

private theorem reduceFst_inv_pow_smul (P : PlaceSpecialization A q N data hKr k red hα hβ)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (i : ℕ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.reduceFst ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ ^ i)⁻¹ • V) = P.reduceFst V := by
  rw [← map_pow, ← map_inv]
  exact reduceFst_arithmeticGalois_smul P _ (inv_mem (pow_mem hσ i)) V

private theorem divisor_apply_eq_zero_of_reduceFst_eq (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hD : ∀ V ∈ D.support, P.IsStrictFst V ∨ P.IsStrictSnd V)
    (hφ : Function.Injective (frobOnPlacesGeomLevel k N data hKr))
    {v : Place k (modularFunctionFieldC k N)}
    (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v)
    {V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hV : P.reduceFst V = v) :
    D V = 0 := by
  by_contra h
  rcases hD V (Finsupp.mem_support_iff.mpr h) with ⟨-, h₂⟩ | ⟨h₁, h₂⟩
  · apply h₂
    rw [hV]
    exact hv
  · apply h₂
    apply hφ
    have hvw : v = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd V) := hV.symm.trans h₁
    rw [hvw] at hv
    exact hv

section Nodes

variable [IsAlgClosed k] [DecidableEq k]

private theorem frob_frob_nodePair_fst (hqN : ¬ q ∣ N) {W : Finset (Place k (modularFunctionFieldC k N))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    {s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)}
    (hs : s ∈ nodePairsOfPlaces (arithFrobC q k N) W) :
    frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr s.1) = s.1 := by
  exact frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k N hqN data hKr s.1
    ((hW s.1).mp (fst_mem_of_mem_nodePairsOfPlaces hs))

end Nodes

private theorem red_smul_coeff (R : ProlongationTuple P)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (a : A) :
    red ⟨σ a, ValuationSubring.smul_mem_of_mem_decompositionSubgroup ℚ ((ValuationSubring.mem_inertiaSubgroupIn (K :=
        ℚ)).mp hσ).choose a.2⟩ = red a := by
  obtain ⟨hD, hI⟩ := (ValuationSubring.mem_inertiaSubgroupIn (K := ℚ)).mp hσ
  have hsm : (⟨σ a, ValuationSubring.smul_mem_of_mem_decompositionSubgroup ℚ ((ValuationSubring.mem_inertiaSubgroupIn
      (K
      := ℚ)).mp hσ).choose a.2⟩ : A)
      = (⟨σ, hD⟩ : A.decompositionSubgroup ℚ) • a := Subtype.ext rfl
  rw [hsm, ← R.redBar_residue, ValuationSubring.residue_smul_eq_of_mem_inertiaSubgroup hD hI a,
    R.redBar_residue]

private theorem coeffRed_coeffMap (R : ProlongationTuple P)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : x ∈ CharPReduction.integralCoeffs A.toSubring) :
    ∃ hx' : coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) x ∈ CharPReduction.integralCoeffs A.toSubring,
      CharPReduction.coeffRed A.toSubring red ⟨_, hx'⟩
        = CharPReduction.coeffRed A.toSubring red ⟨x, hx⟩ := by
  have hD := ((ValuationSubring.mem_inertiaSubgroupIn (K := ℚ)).mp hσ).choose
  have hx' : coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) x ∈ CharPReduction.integralCoeffs A.toSubring :=
      by
    intro n
    rw [coeffMap_coeff]
    exact ValuationSubring.smul_mem_of_mem_decompositionSubgroup ℚ hD (hx n)
  refine ⟨hx', ?_⟩
  ext n
  rw [CharPReduction.coeffRed_coeff, CharPReduction.coeffRed_coeff]
  exact red_smul_coeff R hσ ⟨x.coeff n, hx n⟩

private theorem coeffMap_mem_modularRing
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : x ∈ CharPReduction.modularRing (N * q) A.toSubring) :
    coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) x ∈ CharPReduction.modularRing (N * q) A.toSubring := by
  have hD := ((ValuationSubring.mem_inertiaSubgroupIn (K := ℚ)).mp hσ).choose
  have hle : CharPReduction.modularRing (N * q) A.toSubring ≤ (CharPReduction.modularRing (N * q) A.toSubring).comap
      (coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) := by
    refine Subring.closure_le.mpr ?_
    rintro y (⟨a, rfl⟩ | hy)
    · show coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) (CharPReduction.constSeries A.toSubring a) ∈
        CharPReduction.modularRing (N * q) A.toSubring
      have hconst : coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) (CharPReduction.constSeries A.toSubring a)
          = CharPReduction.constSeries A.toSubring
              ⟨σ a, ValuationSubring.smul_mem_of_mem_decompositionSubgroup ℚ hD a.2⟩ :=
        coeffMap_algebraMap _ _
      rw [hconst]
      exact CharPReduction.constSeries_mem_modularRing _ _ _
    · rcases hy with rfl | hy
      · show coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) (jqModC _) ∈ CharPReduction.modularRing (N * q)
          A.toSubring
        rw [coeffSemilinearAut.coeffMap_jqModC]
        exact CharPReduction.jqModC_mem_modularRing _ _
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        show coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) (jqNModC _ _) ∈ CharPReduction.modularRing (N *
            q) A.toSubring
        rw [coeffSemilinearAut.coeffMap_jqNModC]
        exact CharPReduction.jqNModC_mem_modularRing _ _
  exact hle hx

private theorem exists_coeffMap_mem_modularLocalized (R : ProlongationTuple P)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : x ∈ CharPReduction.modularLocalized (N * q) A.toSubring red) :
    ∃ hx' : coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) x ∈ CharPReduction.modularLocalized (N * q)
        A.toSubring red,
      CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨_, hx'⟩
        = CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨x, hx⟩ := by
  obtain ⟨r, s, hs, hxs⟩ := (CharPReduction.mem_localizedAtKer _ _ _ _).mp hx
  let r' : CharPReduction.modularRing (N * q) A.toSubring := ⟨_, coeffMap_mem_modularRing hσ r.2⟩
  let s' : CharPReduction.modularRing (N * q) A.toSubring := ⟨_, coeffMap_mem_modularRing hσ s.2⟩
  have hr' : CharPReduction.redRes A.toSubring red _ (CharPReduction.modularRing_le_integralCoeffs (N * q)
      A.toSubring) r'
      = CharPReduction.redRes A.toSubring red _ (CharPReduction.modularRing_le_integralCoeffs (N * q) A.toSubring) r
          := by
    rw [CharPReduction.redRes_apply, CharPReduction.redRes_apply]
    exact (coeffRed_coeffMap R hσ
      (CharPReduction.modularRing_le_integralCoeffs (N * q) A.toSubring r.2)).choose_spec
  have hs'' : CharPReduction.redRes A.toSubring red _ (CharPReduction.modularRing_le_integralCoeffs (N * q)
      A.toSubring) s'
      = CharPReduction.redRes A.toSubring red _ (CharPReduction.modularRing_le_integralCoeffs (N * q) A.toSubring) s
          := by
    rw [CharPReduction.redRes_apply, CharPReduction.redRes_apply]
    exact (coeffRed_coeffMap R hσ
      (CharPReduction.modularRing_le_integralCoeffs (N * q) A.toSubring s.2)).choose_spec
  have hxs' : coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) x * (s' : LaurentSeries (AlgebraicClosure ℚ)) =
      (r' : LaurentSeries (AlgebraicClosure ℚ)) := by
    show coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) x * coeffMap (σ : AlgebraicClosure ℚ →+*
        AlgebraicClosure ℚ) (s : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap (σ : AlgebraicClosure ℚ →+*
        AlgebraicClosure ℚ) (r : LaurentSeries (AlgebraicClosure ℚ))
    rw [← map_mul, hxs]
  have hsne : CharPReduction.redRes A.toSubring red _ (CharPReduction.modularRing_le_integralCoeffs (N * q)
      A.toSubring) s ≠ 0 :=
    (CharPReduction.notMem_redKer_iff _ _ _ _).mp hs
  have hs' : s' ∉ CharPReduction.redKer A.toSubring red _ (CharPReduction.modularRing_le_integralCoeffs (N * q)
      A.toSubring) := by
    rw [CharPReduction.notMem_redKer_iff, hs'']
    exact hsne
  have hx' : coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) x ∈ CharPReduction.modularLocalized (N * q)
      A.toSubring red := (CharPReduction.mem_localizedAtKer _ _ _ _).mpr ⟨r', s', hs', hxs'⟩
  refine ⟨hx', ?_⟩
  have h1 := CharPReduction.redLoc_spec (⟨_, hx'⟩ : CharPReduction.modularLocalized (N * q) A.toSubring red) hxs'
  have h2 := CharPReduction.redLoc_spec (⟨x, hx⟩ : CharPReduction.modularLocalized (N * q) A.toSubring red) hxs
  rw [hs'', hr'] at h1
  show CharPReduction.redLocHom _ = CharPReduction.redLocHom _
  rw [CharPReduction.redLocHom_apply, CharPReduction.redLocHom_apply]
  exact mul_right_cancel₀ hsne (h1.trans h2.symm)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem exists_smul_mem_integersFst (R : ProlongationTuple P)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) :
    ∃ h : arithmeticGalois (modularFunctionFieldFull (N * q)) σ • f ∈ R.R₁.integers,
      R.residue₁ ⟨_, h⟩ = R.residue₁ ⟨f, h₁⟩ := by
  have hf : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red :=
      (R.mem_integersFst_iff f).mp h₁
  obtain ⟨hf', hπ⟩ := exists_coeffMap_mem_modularLocalized R hσ hf
  have hsf : ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ • f : modularFunctionFieldBar (N * q)) :
      LaurentSeries (AlgebraicClosure ℚ))
      = coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) (f : LaurentSeries (AlgebraicClosure ℚ)) :=
    coe_arithmeticGalois_smul _ _ _
  have hmem : ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ • f : modularFunctionFieldBar (N * q)) :
      LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red := by
    rw [hsf]
    exact hf'
  obtain ⟨hA, eA⟩ := R.residue₁_eq_modularRedLocHom _ hmem
  obtain ⟨hB, eB⟩ := R.residue₁_eq_modularRedLocHom f hf
  refine ⟨hA, ?_⟩
  have hsub : (⟨_, hmem⟩ : CharPReduction.modularLocalized (N * q) A.toSubring red) = ⟨_, hf'⟩ := Subtype.ext hsf
  rw [hsub] at eA
  show R.residue₁ ⟨_, hA⟩ = R.residue₁ ⟨f, hB⟩
  rw [R.residue₁_apply, R.residue₁_apply]
  exact Subtype.ext (eA.trans (hπ.trans eB.symm))

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem exists_smul_mem_integersSnd (R : ProlongationTuple P)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (f : modularFunctionFieldBar (N * q)) (h₂ : f ∈ R.R₂.integers) :
    ∃ h : arithmeticGalois (modularFunctionFieldFull (N * q)) σ • f ∈ R.R₂.integers,
      R.residue₂ ⟨_, h⟩ = R.residue₂ ⟨f, h₂⟩ := by
  have hAL : ProlongationTuple.atkinLehnerBar N q (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • f)
      = arithmeticGalois (modularFunctionFieldFull (N * q)) σ • ProlongationTuple.atkinLehnerBar N q f :=
    (arithmeticGalois_smul_geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) σ
      (atkinLehnerInvolutionFull N q) f).symm
  have h₁' : ProlongationTuple.atkinLehnerBar N q f ∈ R.R₁.integers :=
    (R.mem_integersFst_iff _).mpr ((R.mem_integersSnd_iff f).mp h₂)
  obtain ⟨hσ₁, hres₁⟩ := exists_smul_mem_integersFst R hσ _ h₁'
  have hmem : arithmeticGalois (modularFunctionFieldFull (N * q)) σ • f ∈ R.R₂.integers := by
    rw [R.mem_integersSnd_iff, hAL]
    exact (R.mem_integersFst_iff _).mp hσ₁
  refine ⟨hmem, ?_⟩
  rw [R.residue₂_apply, R.residue₂_apply, R.residue₂_eq, R.residue₂_eq]
  have hsub : (⟨ProlongationTuple.atkinLehnerBar N q (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • f),
      (R.mem_integersFst_iff _).mpr ((R.mem_integersSnd_iff _).mp hmem)⟩ : R.R₁.integers) = ⟨_, hσ₁⟩ :=
    Subtype.ext hAL
  rw [hsub]
  exact hres₁

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem normPow_mem_integersFst (R : ProlongationTuple P)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (n : ℕ) :
    ∃ hg : normPow (arithmeticGalois (modularFunctionFieldFull (N * q)) σ) f n ∈ R.R₁.integers,
      R.residue₁ ⟨_, hg⟩ = R.residue₁ ⟨f, h₁⟩ ^ n := by
  induction n with
  | zero =>
    refine ⟨by simp [normPow], ?_⟩
    rw [pow_zero, ← map_one R.residue₁]
    exact congrArg R.residue₁ (Subtype.ext (by simp [normPow]))
  | succ n ih =>
    obtain ⟨hg, hres⟩ := ih
    have hσn : σ ^ n ∈ A.inertiaSubgroupIn ℚ := pow_mem hσ n
    have hstep := exists_smul_mem_integersFst R hσn f h₁
    rw [map_pow] at hstep
    obtain ⟨hi, hresi⟩ := hstep
    have hsucc : normPow (arithmeticGalois (modularFunctionFieldFull (N * q)) σ) f (n + 1)
        = normPow (arithmeticGalois (modularFunctionFieldFull (N * q)) σ) f n
          * (arithmeticGalois (modularFunctionFieldFull (N * q)) σ ^ n • f) := by
      simp only [normPow, Finset.prod_range_succ]
    have hmem : normPow (arithmeticGalois (modularFunctionFieldFull (N * q)) σ) f (n + 1) ∈ R.R₁.integers := by
      rw [hsucc]
      exact mul_mem hg hi
    refine ⟨hmem, ?_⟩
    have hmul : (⟨_, hmem⟩ : R.R₁.integers) = ⟨_, hg⟩ * ⟨_, hi⟩ := Subtype.ext hsucc
    rw [hmul, map_mul, hres, hresi, pow_succ]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem normPow_mem_integersSnd (R : ProlongationTuple P)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (f : modularFunctionFieldBar (N * q)) (h₂ : f ∈ R.R₂.integers) (n : ℕ) :
    ∃ hg : normPow (arithmeticGalois (modularFunctionFieldFull (N * q)) σ) f n ∈ R.R₂.integers,
      R.residue₂ ⟨_, hg⟩ = R.residue₂ ⟨f, h₂⟩ ^ n := by
  induction n with
  | zero =>
    refine ⟨by simp [normPow], ?_⟩
    rw [pow_zero, ← map_one R.residue₂]
    exact congrArg R.residue₂ (Subtype.ext (by simp [normPow]))
  | succ n ih =>
    obtain ⟨hg, hres⟩ := ih
    have hσn : σ ^ n ∈ A.inertiaSubgroupIn ℚ := pow_mem hσ n
    have hstep := exists_smul_mem_integersSnd R hσn f h₂
    rw [map_pow] at hstep
    obtain ⟨hi, hresi⟩ := hstep
    have hsucc : normPow (arithmeticGalois (modularFunctionFieldFull (N * q)) σ) f (n + 1)
        = normPow (arithmeticGalois (modularFunctionFieldFull (N * q)) σ) f n
          * (arithmeticGalois (modularFunctionFieldFull (N * q)) σ ^ n • f) := by
      simp only [normPow, Finset.prod_range_succ]
    have hmem : normPow (arithmeticGalois (modularFunctionFieldFull (N * q)) σ) f (n + 1) ∈ R.R₂.integers := by
      rw [hsucc]
      exact mul_mem hg hi
    refine ⟨hmem, ?_⟩
    have hmul : (⟨_, hmem⟩ : R.R₂.integers) = ⟨_, hg⟩ * ⟨_, hi⟩ := Subtype.ext hsucc
    rw [hmul, map_mul, hres, hresi, pow_succ]

section Clauses

variable [IsAlgClosed k]

private theorem ord_nonneg_of_ord_pow_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {x : F} {n : ℕ}
    (hn : 0 < n) (h : 0 ≤ v.ord (x ^ n)) : 0 ≤ v.ord x := by
  rw [← zpow_natCast, Place.ord_zpow] at h
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  nlinarith

set_option synthInstance.maxHeartbeats 1600000 in

private theorem first_clause (R : ProlongationTuple P) (W : Finset (Place k (modularFunctionFieldC k N)))
    (hRL : R.RegularityLaw W)
    (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (n : ℕ) (hn : 0 < n)
    (g : modularFunctionFieldBar (N * q)) (hg₁ : g ∈ R.R₁.integers) (hg₂ : g ∈ R.R₂.integers)
    (hres₁ : R.residue₁ ⟨g, hg₁⟩ = R.residue₁ ⟨f, h₁⟩ ^ n)
    (hres₂ : R.residue₂ ⟨g, hg₂⟩ = R.residue₂ ⟨f, h₂⟩ ^ n)
    (hg : ∀ v : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      IsAffineGeomPlace k N v →
      ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), P.reduceFst V = v → 0 ≤ V.ord g) :
      (∀ v : Place k (modularFunctionFieldC k N),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
        IsAffineGeomPlace k N v →
      (R.residue₁ ⟨f, h₁⟩ ≠ 0 → 0 ≤ v.ord (R.residue₁ ⟨f, h₁⟩)) ∧
      (R.residue₂ ⟨f, h₂⟩ ≠ 0 →
        0 ≤ (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨f, h₂⟩))) := by
  intro v hv hv'
  obtain ⟨c₁, c₂⟩ := hRL.1 g hg₁ hg₂ v hv hv' (hg v hv hv')
  rw [hres₁] at c₁
  rw [hres₂] at c₂
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · exact ord_nonneg_of_ord_pow_nonneg v hn (c₁ (pow_ne_zero n hf))
  · exact ord_nonneg_of_ord_pow_nonneg _ hn (c₂ (pow_ne_zero n hf))

end Clauses

end Modular

end InertialNormDescent

open InertialNormDescent in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem impl_of_regularityLaw
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} [IsAlgClosed k]
    [DecidableEq k] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hRL : R.RegularityLaw W) :
    R.OneSidedRegularityLaw W := by
  intro f h₁ h₂ σ hσ D E hD hdiv
  by_cases hf : f = 0
  · subst hf
    have e₁ : R.residue₁ ⟨0, h₁⟩ = 0 := by
      rw [show (⟨0, h₁⟩ : R.R₁.integers) = 0 from Subtype.ext rfl, map_zero]
    have e₂ : R.residue₂ ⟨0, h₂⟩ = 0 := by
      rw [show (⟨0, h₂⟩ : R.R₂.integers) = 0 from Subtype.ext rfl, map_zero]
    exact ⟨fun _ _ _ => ⟨fun h => absurd e₁ h, fun h => absurd e₂ h⟩,
      fun _ _ => ⟨fun h => absurd e₁ h, fun h => absurd e₂ h⟩⟩
  · obtain ⟨n, hn, hper⟩ := exists_pow_smul_eq_self σ f
    obtain ⟨hg₁, hres₁⟩ := normPow_mem_integersFst R hσ f h₁ n
    obtain ⟨hg₂, hres₂⟩ := normPow_mem_integersSnd R hσ f h₂ n
    have hg : ∀ v : Place k (modularFunctionFieldC k N),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
        ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), P.reduceFst V = v →
          0 ≤ V.ord (normPow (arithmeticGalois (modularFunctionFieldFull (N * q)) σ) f n) := by
      intro v hv V hV
      exact (ord_normPow_eq_zero (arithmeticGalois (modularFunctionFieldFull (N * q)) σ) hf D E hdiv hper V
        fun i => divisor_apply_eq_zero_of_reduceFst_eq P D hD (frobOnPlacesGeomLevel_injective k N data hKr)
          hv ((reduceFst_inv_pow_smul P hσ i V).trans hV)).ge
    refine ⟨first_clause R W hRL f h₁ h₂ n hn _ hg₁ hg₂ hres₁ hres₂ fun v hv _ V hV => hg v hv V hV, ?_⟩
    intro s hs
    have hfix := frob_frob_nodePair_fst (data := data) (hKr := hKr) hqN hW hs
    obtain ⟨c, hc₁, hc₂⟩ := hRL.2 _ hg₁ hg₂ s hs fun V hV => hg s.1 hfix V hV
    rw [hres₁] at hc₁
    rw [hres₂] at hc₂
    exact ⟨fun hr₁ hr₂ => ord_pos_of_hasValue_pow_of_eq_zero hn hc₁ hc₂ hr₁ hr₂,
      fun hr₂ hr₁ => ord_pos_of_hasValue_pow_of_eq_zero hn hc₂ hc₁ hr₂ hr₁⟩

section Transfer

variable {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P P' : PlaceSpecialization A q N data hKr k red hα hβ}

set_option synthInstance.maxHeartbeats 1600000 in

private theorem residue₁_indep (R : ProlongationTuple P) (R' : ProlongationTuple P')
    (f : modularFunctionFieldBar (N * q)) (h : f ∈ R.R₁.integers) (h' : f ∈ R'.R₁.integers) :
    R.residue₁ ⟨f, h⟩ = R'.residue₁ ⟨f, h'⟩ := by
  have hf : (f : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized (N * q) A.toSubring red := (R.mem_integersFst_iff f).mp h
  obtain ⟨_, e⟩ := R.residue₁_eq_modularRedLocHom f hf
  obtain ⟨_, e'⟩ := R'.residue₁_eq_modularRedLocHom f hf
  apply Subtype.ext
  rw [ProlongationTuple.residue₁_apply, ProlongationTuple.residue₁_apply]
  exact e.trans e'.symm

set_option synthInstance.maxHeartbeats 1600000 in

private theorem residue₂_indep (R : ProlongationTuple P) (R' : ProlongationTuple P')
    (f : modularFunctionFieldBar (N * q)) (h : f ∈ R.R₂.integers) (h' : f ∈ R'.R₂.integers) :
    R.residue₂ ⟨f, h⟩ = R'.residue₂ ⟨f, h'⟩ := by
  have key := residue₁_indep R R' (ProlongationTuple.atkinLehnerBar N q f)
    ((R.mem_integers₂_iff f).mp h) ((R'.mem_integers₂_iff f).mp h')
  rw [ProlongationTuple.residue₁_apply, ProlongationTuple.residue₁_apply] at key
  rw [ProlongationTuple.residue₂_apply, ProlongationTuple.residue₂_apply, R.residue₂_eq f h, R'.residue₂_eq f h']
  exact key

set_option synthInstance.maxHeartbeats 1600000 in

private theorem oneSidedRegularityLaw_transfer [PerfectField k] (R : ProlongationTuple P)
    (R' : ProlongationTuple P') (W : Finset (Place k (modularFunctionFieldC k N)))
    (hlab : ∀ V, P.IsStrictFst V ∨ P.IsStrictSnd V → P'.IsStrictFst V ∨ P'.IsStrictSnd V)
    (h : R'.OneSidedRegularityLaw W) : R.OneSidedRegularityLaw W := by
  intro f h₁ h₂ σ hσ D E hD hdiv
  have h₁' : f ∈ R'.R₁.integers := (R'.mem_integersFst_iff f).mpr ((R.mem_integersFst_iff f).mp h₁)
  have h₂' : f ∈ R'.R₂.integers := (R'.mem_integersSnd_iff f).mpr ((R.mem_integersSnd_iff f).mp h₂)
  rw [residue₁_indep R R' f h₁ h₁', residue₂_indep R R' f h₂ h₂']
  exact h f h₁' h₂' σ hσ D E (fun V hV => hlab V (hD V hV)) hdiv

end Transfer

set_option synthInstance.maxHeartbeats 1600000 in

private theorem oneSidedRegularityLaw_core
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} [IsAlgClosed k]
    [DecidableEq k] (hqN : ¬ q ∣ N) (hred : Function.Surjective red)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hmodel : R.IsModel) :
    R.OneSidedRegularityLaw W := by
  rcases Nat.lt_or_ge 1 N with _ | hN
  · by_cases hg : 0 < genusFF k ↥(modularFunctionFieldC k N)
    · obtain ⟨R', -, hRL', -, -⟩ :=
        exists_prolongationTuple_isModel_regularityLaw_nodeValueLaw hg hqN hred P W hW
      exact oneSidedRegularityLaw_transfer R R' W (fun _ h => h) (impl_of_regularityLaw hqN P W hW R' hRL')
    · obtain ⟨P₀, R₀, hm₀, hRL₀, -, -⟩ :=
        exists_prolongationTuple_isModel_and_orderLawFixed_of_not_genusFF_pos hg hqN hred W hW
      have hlab := isStrictFst_iff_and_isStrictSnd_iff_of_isModel_of_isModel hg hqN P P₀ R hmodel R₀ hm₀
      exact oneSidedRegularityLaw_transfer R R₀ W (fun V h => h.imp (hlab.1 V).mp (hlab.2 V).mp)
        (impl_of_regularityLaw hqN P₀ W hW R₀ hRL₀)
  · obtain rfl : N = 1 := le_antisymm hN (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
    obtain ⟨R', -, hRL', -, -⟩ := exists_prolongationTuple_isModel_regularityLaw_nodeValueLaw_level_one P W hW
    exact oneSidedRegularityLaw_transfer R R' W (fun _ h => h) (impl_of_regularityLaw hqN P W hW R' hRL')

set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} [IsAlgClosed k]
    [DecidableEq k] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hmodel : R.IsModel) :
    R.OneSidedRegularityLaw W :=
  oneSidedRegularityLaw_core hqN (red_surjective_of_level P) P W hW R hmodel

#print axioms solution

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_oneSidedRegularityLaw_of_isModel_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_oneSidedRegularityLaw_of_isModel_of_not_dvd (solution)
