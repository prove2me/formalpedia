-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.nodeIntegersOver_isLocalRing_exists_isMaximal_of_regularityLaw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a1ca6b65-4be7-5466-ab01-ba2a7cac5916

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_NodeDescentTower
import Definitions.Def_ValuationSubring_ReduceAt
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isLocalRing_nodeIntegersOver_of_orderLawFixed_of_regularityLaw
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isUnit_of_not_hasValue_nodeResidue_zero_of_isLocalRing
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_place_forall_iff_mem_and_hasValue_of_height_one_of_natCast_notMem
import Theorems.Thm_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem_level
import Theorems.Thm_ModularCurve_PlaceSpecialization_red_surjective_of_level
import Theorems.Thm_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level
import Theorems.Thm_ModularCurve_exists_phiIrreducible
import Theorems.Thm_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_jIntegralClosure_ord_residues_pos_and_eq_zero_of_ne
import Theorems.Thm_ModularCurve_NodeLocalized_exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict
import Theorems.Thm_ModularCurve_PlaceSpecialization_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceFst_eq_or_eq_arithFrobC_smul_of_forall_hasValue_iff
import Theorems.Thm_ValuationSubring_exists_forall_apply_eq_and_isFrobeniusAt_natCard_of_liesOverPrime
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_and_reduceSnd_arithmeticGalois_smul_of_isFrobeniusAt_pow
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces_univ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeIntegersOver_isLocalRing_exists_isMaximal_of_regularityLaw
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one"
p2m_attr_erase "simp" "compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.eisensteinNumerator_nineteen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq"
p2m_attr_erase "simp" "ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk"
p2m_attr_erase "simp" "AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of"
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

noncomputable section

private theorem exists_mul_eq_of_forall_height_one_le_of_isIntegrallyClosed
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    {F : Type*} [Field F] (φ : R →+* F) (hinj : Function.Injective φ)
    (𝔪 : Ideal R) [𝔪.IsPrime] (x : F)
    (hfrac : ∃ r s : R, s ≠ 0 ∧ x * φ s = φ r)
    (hx : ∀ (𝔭 : Ideal R) [𝔭.IsPrime], 𝔭.height = 1 → 𝔭 ≤ 𝔪 → ∃ r s : R, s ∉ 𝔭 ∧ x * φ s = φ r) :
    ∃ r s : R, s ∉ 𝔪 ∧ x * φ s = φ r := by
  classical
  obtain ⟨r₀, s₀, hs₀, hx₀⟩ := hfrac
  have hφs₀ : φ s₀ ≠ 0 := fun h => hs₀ (hinj (h.trans (map_zero φ).symm))
  haveI hdom : IsDomain (Localization.AtPrime 𝔪) := IsLocalization.isDomain_of_local_atPrime ‹𝔪.IsPrime›
  haveI hnoeth : IsNoetherianRing (Localization.AtPrime 𝔪) :=
    IsLocalization.isNoetherianRing 𝔪.primeCompl (Localization.AtPrime 𝔪) ‹IsNoetherianRing R›
  haveI hic : IsIntegrallyClosed (Localization.AtPrime 𝔪) :=
    isIntegrallyClosed_of_isLocalization (S := Localization.AtPrime 𝔪) 𝔪.primeCompl 𝔪.primeCompl_le_nonZeroDivisors

  let K := FractionRing R
  let g : Localization.AtPrime 𝔪 →+* K :=
    IsLocalization.map _ (T := nonZeroDivisors R) (RingHom.id R) 𝔪.primeCompl_le_nonZeroDivisors
  letI : Algebra (Localization.AtPrime 𝔪) K := g.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime 𝔪) K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  haveI hfr : IsFractionRing (Localization.AtPrime 𝔪) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔪.primeCompl (Localization.AtPrime 𝔪) K
  let ψ : R →+* K := (algebraMap (Localization.AtPrime 𝔪) K).comp (algebraMap R (Localization.AtPrime 𝔪))
  have hψ : Function.Injective ψ :=
    (IsFractionRing.injective (Localization.AtPrime 𝔪) K).comp
      (IsLocalization.injective (Localization.AtPrime 𝔪) 𝔪.primeCompl_le_nonZeroDivisors)
  have hψs₀ : ψ s₀ ≠ 0 := fun h => hs₀ (hψ (h.trans (map_zero ψ).symm))
  set xm : K := ψ r₀ / ψ s₀ with hxm
  have hxm' : ∀ (Q : Ideal (Localization.AtPrime 𝔪)) [Q.IsPrime], Q.height = 1 →
      ∃ r s : Localization.AtPrime 𝔪, s ∉ Q ∧
        xm * algebraMap (Localization.AtPrime 𝔪) K s
          = algebraMap (Localization.AtPrime 𝔪) K r := by
    intro Q hQ hQ1
    have h𝔭1 : (Q.under R).height = 1 := by
      rw [IsLocalization.height_under 𝔪.primeCompl Q]; exact hQ1
    have h𝔭𝔪 : Q.under R ≤ 𝔪 :=
      (Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ.ne_top)).trans
        (IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime 𝔪) 𝔪).le
    obtain ⟨r, s, hs, hrs⟩ := hx (Q.under R) h𝔭1 h𝔭𝔪
    have hR : r₀ * s = r * s₀ := by
      apply hinj
      rw [map_mul, map_mul, ← hx₀, ← hrs]; ring
    refine ⟨algebraMap R (Localization.AtPrime 𝔪) r, algebraMap R (Localization.AtPrime 𝔪) s,
      fun h => hs (Ideal.mem_comap.mpr h), ?_⟩
    show xm * ψ s = ψ r
    rw [hxm, div_mul_eq_mul_div, div_eq_iff hψs₀, ← map_mul, ← map_mul, hR]
  have h0 := IsIntegrallyClosed.exists_algebraMap_eq_of_forall_height_eq_one (R := Localization.AtPrime 𝔪)
    K xm hxm'
  obtain ⟨y, hy⟩ := h0
  obtain ⟨p, hp⟩ := IsLocalization.mk'_surjective 𝔪.primeCompl y
  obtain ⟨r₁, s₁⟩ := p
  simp only at hp
  have h1 : ψ r₁ = xm * ψ s₁ := by
    rw [← hy, ← hp]
    show algebraMap (Localization.AtPrime 𝔪) K (algebraMap R _ r₁)
      = algebraMap (Localization.AtPrime 𝔪) K (IsLocalization.mk' _ r₁ s₁)
        * algebraMap (Localization.AtPrime 𝔪) K (algebraMap R _ (s₁ : R))
    rw [← map_mul, IsLocalization.mk'_spec]
  have hR' : r₁ * s₀ = r₀ * s₁ := by
    apply hψ
    rw [map_mul, map_mul, h1, hxm, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hψs₀]
  refine ⟨r₁, s₁, s₁.2, ?_⟩
  apply mul_right_cancel₀ hφs₀
  calc x * φ s₁ * φ s₀ = x * φ s₀ * φ s₁ := by ring
    _ = φ r₀ * φ s₁ := by rw [hx₀]
    _ = φ (r₀ * s₁) := (map_mul φ _ _).symm
    _ = φ (r₁ * s₀) := by rw [hR']
    _ = φ r₁ * φ s₀ := map_mul φ _ _

private theorem aeval_zmod_map' {q : ℕ} {S T : Type*} [CommRing S] [CommRing T] [Algebra (ZMod q) S]
    [Algebra (ZMod q) T] (f : S →+* T) (p : Polynomial (ZMod q)) (x : S) :
    f (Polynomial.aeval x p) = Polynomial.aeval (f x) p := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂,
    RingHom.ext_zmod (f.comp _) (algebraMap (ZMod q) T)]

section World

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data} {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} {P : PlaceSpecialization A q N data hKr k red hα hβ}

private theorem jRing_le_fieldOver_level (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    jRing A K ≤ (fieldOver (N * q) K).toSubring := by
  rw [jRing, Subring.closure_le]
  rintro x (⟨c, rfl⟩ | rfl)
  · exact Subfield.subset_closure (Or.inl ⟨⟨(c : AlgebraicClosure ℚ), c.2.2⟩, rfl⟩)
  · exact Subfield.subset_closure (Or.inr (Set.mem_insert _ _))

private theorem jRing_le_jIntegralClosure_level (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    jRing A K ≤ jIntegralClosure (N * q) A K :=
  fun x hx => ⟨jRing_le_fieldOver_level (q := q) K hx, isIntegral_algebraMap (x := (⟨x, hx⟩ : ↥(jRing A K)))⟩

private def iotaC' (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    ↥(jIntegralClosure (N * q) A K) →+* ↥(modularFunctionFieldBar (N * q)) :=
  (Subring.inclusion (fieldOver_le_modularFunctionFieldBar (N * q) K)).comp
    (Subring.inclusion (show jIntegralClosure (N * q) A K ≤ (fieldOver (N * q) K).toSubring from fun _ hx => hx.1))

private theorem coe_iotaC' (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (c : ↥(jIntegralClosure (N * q) A K)) :
    ((iotaC' (q := q) K c : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = c := rfl

private theorem iotaC'_injective (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    Function.Injective (iotaC' (q := q) (A := A) (N := N) K) :=
  fun c₁ c₂ h => Subtype.ext (by rw [← coe_iotaC' K c₁, ← coe_iotaC' K c₂, h])

variable (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hws : w ∈ ssPlaces q N k)

set_option synthInstance.maxHeartbeats 1600000 in
include hqN hws in

private theorem iotaC'_mem_integersFst (c : ↥(jIntegralClosure (N * q) A K)) : iotaC' K c ∈ R.R₁.integers :=
  (R.mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure hqN K w hws (iotaC' K c) c.2).1.1

include hqN hws in

private theorem residue₁_iotaC'_mem (c : ↥(jIntegralClosure (N * q) A K)) :
    (R.residue₁ ⟨iotaC' K c, iotaC'_mem_integersFst R hqN K w hws c⟩ : ↥(modularFunctionFieldC k N))
      ∈ w.toValuationSubring :=
  (R.mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure hqN K w hws (iotaC' K c) c.2).2.1 _

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

private def resC' : ↥(jIntegralClosure (N * q) A K) →+* ↥w.toValuationSubring where
  toFun c := ⟨R.residue₁ ⟨iotaC' K c, iotaC'_mem_integersFst R hqN K w hws c⟩, residue₁_iotaC'_mem R hqN K w hws c⟩
  map_one' := by
    apply Subtype.ext
    show R.residue₁ ⟨iotaC' K 1, _⟩ = 1
    have : (⟨iotaC' K 1, iotaC'_mem_integersFst R hqN K w hws 1⟩ : ↥R.R₁.integers) = 1 := Subtype.ext (map_one _)
    rw [this, map_one]
  map_mul' x y := by
    apply Subtype.ext
    show R.residue₁ ⟨iotaC' K (x * y), _⟩ = R.residue₁ ⟨iotaC' K x, _⟩ * R.residue₁ ⟨iotaC' K y, _⟩
    rw [← map_mul]
    exact congrArg R.residue₁ (Subtype.ext (map_mul _ x y))
  map_zero' := by
    apply Subtype.ext
    show R.residue₁ ⟨iotaC' K 0, _⟩ = 0
    have : (⟨iotaC' K 0, iotaC'_mem_integersFst R hqN K w hws 0⟩ : ↥R.R₁.integers) = 0 := Subtype.ext (map_zero _)
    rw [this, map_zero]
  map_add' x y := by
    apply Subtype.ext
    show R.residue₁ ⟨iotaC' K (x + y), _⟩ = R.residue₁ ⟨iotaC' K x, _⟩ + R.residue₁ ⟨iotaC' K y, _⟩
    rw [← map_add]
    exact congrArg R.residue₁ (Subtype.ext (map_add _ x y))

private def nodeKer' : Ideal ↥(jIntegralClosure (N * q) A K) :=
  (IsLocalRing.maximalIdeal ↥w.toValuationSubring).comap (resC' R hqN K w hws)

set_option synthInstance.maxHeartbeats 1600000 in
private theorem mem_nodeKer'_iff (c : ↥(jIntegralClosure (N * q) A K)) :
    c ∈ nodeKer' R hqN K w hws ↔
      ∃ h₁ : iotaC' K c ∈ R.R₁.integers,
        w.HasValue (R.residue₁ ⟨iotaC' K c, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k) := by
  rw [nodeKer', Ideal.mem_comap, ← IsLocalRing.residue_eq_zero_iff]
  constructor
  · intro h
    exact ⟨iotaC'_mem_integersFst R hqN K w hws c, residue₁_iotaC'_mem R hqN K w hws c, by rw [map_zero]; exact h⟩
  · rintro ⟨h₁, hmem, hres⟩
    rw [map_zero] at hres
    exact hres

omit [Fact q.Prime] [IsAlgClosed k] [DecidableEq k] in
include red in

private theorem not_isUnit_natCast_of_red' : ¬ IsUnit ((q : ℕ) : A) := by
  intro h
  have := h.map red
  rw [map_natCast, CharP.cast_eq_zero] at this
  exact not_isUnit_zero this

private theorem nodeKer'_isMaximal (hred : Function.Surjective red) : (nodeKer' R hqN K w hws).IsMaximal := by
  classical
  have hqprime : q.Prime := Fact.out
  let θ : ↥(jIntegralClosure (N * q) A K) →+* w.ResidueField := (IsLocalRing.residue _).comp (resC' R hqN K w hws)
  have hker : RingHom.ker θ = nodeKer' R hqN K w hws := by
    ext c
    rw [RingHom.mem_ker, nodeKer', Ideal.mem_comap, ← IsLocalRing.residue_eq_zero_iff]
    rfl
  haveI hprime : (nodeKer' R hqN K w hws).IsPrime := by rw [← hker]; exact RingHom.ker_isPrime θ
  apply Ideal.Quotient.maximal_of_isField

  let θbar : (↥(jIntegralClosure (N * q) A K) ⧸ nodeKer' R hqN K w hws) →+* w.ResidueField :=
    Ideal.Quotient.lift (nodeKer' R hqN K w hws) θ (fun c hc => by rw [← RingHom.mem_ker, hker]; exact hc)
  have hθbar : Function.Injective θbar := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.lift_mk] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [← hker]; exact hx)

  haveI : CharP w.ResidueField q := charP_of_injective_algebraMap (algebraMap k w.ResidueField).injective q
  haveI : CharP (↥(jIntegralClosure (N * q) A K) ⧸ nodeKer' R hqN K w hws) q := θbar.charP hθbar q
  have hqA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
    exact ⟨(q : A).2, by
      have : (⟨((q : ℕ) : AlgebraicClosure ℚ), (q : A).2⟩ : A) = (q : A) := Subtype.ext rfl
      rw [this]; exact not_isUnit_natCast_of_red' (red := red)⟩
  haveI : CharP (ResidueField ↥A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hqprime hqA
  letI : Algebra (ZMod q) (↥(jIntegralClosure (N * q) A K) ⧸ nodeKer' R hqN K w hws) := ZMod.algebra _ q
  letI : Algebra (ZMod q) w.ResidueField := ZMod.algebra _ q
  letI : Algebra (ZMod q) k := ZMod.algebra _ q
  letI : Algebra (ZMod q) (ResidueField ↥A) := ZMod.algebra _ q

  have halgQ : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by convert AlgebraicClosure.isAlgebraic ℚ; rfl; rfl
  haveI := halgQ
  have halgA : Algebra.IsAlgebraic (ZMod q) (ResidueField ↥A) :=
    (ValuationSubring.isAlgClosure_residueField (ℓ := q) A).isAlgebraic

  haveI : Algebra.IsIntegral (ZMod q) (↥(jIntegralClosure (N * q) A K) ⧸ nodeKer' R hqN K w hws) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, hy⟩ := hws.1 (θ c)
    obtain ⟨a, rfl⟩ := hred y
    obtain ⟨p, hp0, hpa⟩ : IsAlgebraic (ZMod q) (IsLocalRing.residue ↥A a) := halgA.isAlgebraic _
    have h1 : Polynomial.aeval (θ c) p = 0 := by
      rw [← hy, show red a = R.redBar (IsLocalRing.residue ↥A a) from (R.redBar_residue a).symm,
        ← aeval_zmod_map' (algebraMap k w.ResidueField), ← aeval_zmod_map' R.redBar, hpa, map_zero, map_zero]
    have h2 : θbar (Polynomial.aeval (Ideal.Quotient.mk (nodeKer' R hqN K w hws) c) p) = 0 := by
      rw [aeval_zmod_map' θbar, Ideal.Quotient.lift_mk]; exact h1
    have h3 : Polynomial.aeval (Ideal.Quotient.mk (nodeKer' R hqN K w hws) c) p = 0 :=
      hθbar (h2.trans (map_zero θbar).symm)
    exact IsAlgebraic.isIntegral ⟨p, hp0, h3⟩
  exact isField_of_isIntegral_of_isField' (Field.toIsField (ZMod q))

private theorem ord_pos_of_hasValue_zero {K₁ F₁ : Type*} [Field K₁] [Field F₁] [Algebra K₁ F₁] (v : Place K₁ F₁)
    {r : F₁} (hr : r ≠ 0) (h : v.HasValue r 0) : 0 < v.ord r := by
  refine lt_of_le_of_ne (v.ord_nonneg_of_mem h.mem) fun h0 => ?_
  obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hr h0.symm
  have hres := h.residue_eq
  rw [map_zero] at hres
  exact (hu.map (IsLocalRing.residue v.toValuationSubring)).ne_zero hres

private theorem hasValue_zero_of_ord_pos {K₁ F₁ : Type*} [Field K₁] [Field F₁] [Algebra K₁ F₁] (v : Place K₁ F₁)
    {r : F₁} (h : 0 < v.ord r) : v.HasValue r 0 := by
  have hr : r ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at h
    exact lt_irrefl _ h
  have hm : r ∈ v.toValuationSubring := v.mem_of_ord_nonneg hr h.le
  refine ⟨hm, ?_⟩
  rw [map_zero]
  by_contra hne
  have hu : IsUnit (⟨r, hm⟩ : v.toValuationSubring) := (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hne
  have h0 := v.ord_coe_unit hu.unit
  rw [IsUnit.unit_spec] at h0
  exact h.ne' h0

private theorem hasValue_sub_algebraMap {K₁ F₁ : Type*} [Field K₁] [Field F₁] [Algebra K₁ F₁] (v : Place K₁ F₁)
    {r : F₁} {b : K₁} (h : v.HasValue r b) (c : K₁) : v.HasValue (r - algebraMap K₁ F₁ c) (b - c) := by
  have hc : v.HasValue (algebraMap K₁ F₁ c) c := Place.hasValue_algebraMap (v := v) c
  refine ⟨sub_mem h.mem hc.mem, ?_⟩
  have hsub : (⟨r - algebraMap K₁ F₁ c, sub_mem h.mem hc.mem⟩ : v.toValuationSubring) =
      ⟨r, h.mem⟩ - ⟨algebraMap K₁ F₁ c, hc.mem⟩ := rfl
  rw [hsub, map_sub, h.residue_eq, hc.residue_eq, map_sub]

omit [IsAlgClosed k] in

private theorem exists_large_field :
    ∃ K'' : IntermediateField ℚ (AlgebraicClosure ℚ), K ≤ K'' ∧ FiniteDimensional ℚ K'' ∧
      ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K'') := by
  classical
  obtain ⟨K₀, hK₀fd, -, hK₀⟩ :=
    ModularCurve.NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict q A k red
      ((Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots.toFinset) (by
        intro a ha
        have hroot := Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp ha)
        simpa [sub_eq_zero] using hroot)
  haveI := hK₀fd
  refine ⟨K ⊔ K₀, le_sup_left, IntermediateField.finiteDimensional_sup K K₀, fun a ha => ?_⟩
  have haS : a ∈ (Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots.toFinset := by
    refine Multiset.mem_toFinset.mpr ((Polynomial.mem_roots ?_).mpr (by simp [ha]))
    exact FiniteField.X_pow_card_sub_X_ne_zero _ (Nat.one_lt_pow two_ne_zero (Fact.out : q.Prime).one_lt)
  obtain ⟨z, rfl⟩ := hK₀ a haS
  exact ⟨⟨(z : AlgebraicClosure ℚ), z.2.1, (le_sup_right : K₀ ≤ K ⊔ K₀) z.2.2⟩, rfl⟩

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
include hqN hws in

private theorem reduceFst_eq_of_dict (hO : R.OrderLawFixed)
    (K'' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K'']
    (hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K''))
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hw₂ : P.reduceFst W ∈ ssPlaces q N k)
    (hdict : ∀ (t : ↥(modularFunctionFieldBar (N * q)))
        (_ : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K''),
        ∃ a : A, W.HasValue t (a : AlgebraicClosure ℚ) ∧
          ((∃ h₁ : t ∈ R.R₁.integers, w.HasValue (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k)) ↔
            a ∈ IsLocalRing.maximalIdeal A)) :
    P.reduceFst W = w := by
  classical
  set w₂ := P.reduceFst W with hw₂def

  have hι : ∀ x : IsLocalRing.ResidueField A,
      R.ι (algebraMap (IsLocalRing.ResidueField A) (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) x) =
        algebraMap k ↥(modularFunctionFieldC k N) (R.redBar x) := by
    intro x
    apply Subtype.ext
    rw [R.ι_coe]
    change coeffMap R.redBar (algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) x) =
      algebraMap k (LaurentSeries k) (R.redBar x)
    rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

  haveI hPD : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  by_contra hne
  obtain ⟨g, hgC, hg₁, hg₂, hpos₁, hpos₂, hzero₁, hzero₂⟩ :=
    R.exists_mem_jIntegralClosure_ord_residues_pos_and_eq_zero_of_ne hqN K'' hk₀ w₂ w hw₂ hws hne
  rw [ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr w₂] at hpos₂
  obtain ⟨a, haW, hiff⟩ := hdict g hgC

  have ha : a ∉ IsLocalRing.maximalIdeal A := fun hm => by
    obtain ⟨h₁', hval⟩ := hiff.2 hm
    have hne0 : (R.residue₁ ⟨g, hg₁⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := fun h0 => by
      rw [h0, Place.ord_zero] at hpos₁
      exact lt_irrefl _ hpos₁
    exact (ord_pos_of_hasValue_zero w hne0 hval).ne' hzero₁
  have hared : red a ≠ 0 := ((IsLocalRing.notMem_maximalIdeal.1 ha).map red).ne_zero
  have hneg : -(red a) ≠ 0 := neg_ne_zero.mpr hared

  have hc₁ : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈
      R.R₁.integers := (R.R₁.algebraMap_mem_iff _).mpr a.2
  have hc₂ : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈
      R.R₂.integers := (R.R₂.algebraMap_mem_iff _).mpr a.2
  set f : ↥(modularFunctionFieldBar (N * q)) :=
    g - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) with hfdef
  have hf₁ : f ∈ R.R₁.integers := sub_mem hg₁ hc₁
  have hf₂ : f ∈ R.R₂.integers := sub_mem hg₂ hc₂
  have hres₁ : (R.residue₁ ⟨f, hf₁⟩ : ↥(modularFunctionFieldC k N)) =
      R.residue₁ ⟨g, hg₁⟩ - algebraMap k ↥(modularFunctionFieldC k N) (red a) := by
    have hsub : (⟨f, hf₁⟩ : R.R₁.integers) = ⟨g, hg₁⟩ - ⟨_, hc₁⟩ := rfl
    rw [hsub, map_sub, residue₁_apply (f := ⟨_, hc₁⟩), R.R₁.residue_algebraMap a, hι, R.redBar_residue a]
  have hres₂ : (R.residue₂ ⟨f, hf₂⟩ : ↥(modularFunctionFieldC k N)) =
      R.residue₂ ⟨g, hg₂⟩ - algebraMap k ↥(modularFunctionFieldC k N) (red a) := by
    have hsub : (⟨f, hf₂⟩ : R.R₂.integers) = ⟨g, hg₂⟩ - ⟨_, hc₂⟩ := rfl
    rw [hsub, map_sub, residue₂_apply (f := ⟨_, hc₂⟩), R.R₂.residue_algebraMap a, hι, R.redBar_residue a]
  have hval₁ : w₂.HasValue (R.residue₁ ⟨f, hf₁⟩ : ↥(modularFunctionFieldC k N)) (-(red a)) := by
    rw [hres₁]
    have h := hasValue_sub_algebraMap w₂ (hasValue_zero_of_ord_pos w₂ hpos₁) (red a)
    rwa [zero_sub] at h
  have hval₂ : (frobOnPlacesGeomLevel k N data hKr w₂).HasValue
      (R.residue₂ ⟨f, hf₂⟩ : ↥(modularFunctionFieldC k N)) (-(red a)) := by
    rw [hres₂]
    have h := hasValue_sub_algebraMap _ (hasValue_zero_of_ord_pos _ hpos₂) (red a)
    rwa [zero_sub] at h
  have hR₁ : R.R₁.residue ⟨f, hf₁⟩ ≠ 0 := fun h0 => hval₁.ne_zero hneg (by rw [residue₁_apply, h0, map_zero])
  have hR₂ : R.R₂.residue ⟨f, hf₂⟩ ≠ 0 := fun h0 => hval₂.ne_zero hneg (by rw [residue₂_apply, h0, map_zero])
  have hf0 : f ≠ 0 := fun h => hR₁ (by rw [show (⟨f, hf₁⟩ : R.R₁.integers) = 0 from Subtype.ext h, map_zero])

  obtain ⟨D, hD, -⟩ := hPD.exists_divisor f hf0
  have hfix := PlaceSpecialization.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces hqN P w₂ hw₂
  have haff : IsAffineGeomPlace k N w₂ := ((mem_ssPlaces_iff q N k).mp hw₂).2.1
  have hlaw := hO f hf₁ hf₂ hR₁ hR₂ D hD w₂ hfix haff
  rw [hval₁.ord_eq_zero hneg, hval₂.ord_eq_zero hneg, add_zero] at hlaw

  have hW : 1 ≤ D W := by
    have h := hasValue_sub_algebraMap W haW (a : AlgebraicClosure ℚ)
    rw [sub_self] at h
    have hpos := ord_pos_of_hasValue_zero W hf0 h
    rw [hD]
    omega
  have hnonneg : ∀ V, P.reduceFst V = w₂ → 0 ≤ D V := fun V hV => by
    have hgV : g ∈ V.toValuationSubring :=
      (R.mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure hqN K'' w₂ hw₂ g hgC).1.2.2 V hV
    rw [hD]
    exact V.ord_nonneg_of_mem (sub_mem hgV (Place.hasValue_algebraMap (v := V) (a : AlgebraicClosure ℚ)).mem)
  have hshape : Finsupp.mapDomain P.reduceFst D w₂ =
      D.support.sum fun V => Finsupp.single (P.reduceFst V) (D V) w₂ := by
    rw [Finsupp.mapDomain, Finsupp.sum_apply]
    rfl
  have hWs : W ∈ D.support := by
    rw [Finsupp.mem_support_iff]
    omega
  have hterm : ∀ V ∈ D.support, (0 : ℤ) ≤ Finsupp.single (P.reduceFst V) (D V) w₂ := fun V _ => by
    rw [Finsupp.single_apply]
    split_ifs with hV
    · exact hnonneg V hV
    · exact le_rfl
  have hsum : Finsupp.single (P.reduceFst W) (D W) w₂ ≤
      D.support.sum fun V => Finsupp.single (P.reduceFst V) (D V) w₂ := Finset.single_le_sum hterm hWs
  rw [Finsupp.single_apply, if_pos hw₂def.symm] at hsum
  omega

omit [IsAlgClosed k] [FiniteDimensional ℚ K] in
include R in

private theorem mem_range_redRestrict_of_even (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (d : ℕ) (hd : 0 < d)
    (hcard : Nat.card (Set.range fun a : {a : A // (a : AlgebraicClosure ℚ) ∈ K} => IsLocalRing.residue A a.1) = q ^ d)
    (hσK : ∀ z ∈ K, σ z = z) (hσF : A.IsFrobeniusAt σ (q ^ d)) (hev : Even d) (b : k) (hb : b ^ (q ^ 2) = b) :
    b ∈ Set.range (NodeLocalized.redRestrict red K) := by
  set S := Set.range fun a : {a : A // (a : AlgebraicClosure ℚ) ∈ K} => IsLocalRing.residue A a.1 with hS
  haveI : Finite S := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (Fact.out : q.Prime).ne_zero)
  haveI : Fintype S := Fintype.ofFinite S

  have hpow : ∀ y : S, (y : IsLocalRing.ResidueField A) ^ (q ^ d) = y := by
    rintro ⟨y, a, rfl⟩
    have hmem : σ (a.1 : AlgebraicClosure ℚ) ∈ A := by
      rw [hσK _ a.2]
      exact a.1.2
    have e : IsLocalRing.residue A ⟨σ (a.1 : AlgebraicClosure ℚ), hmem⟩ = IsLocalRing.residue A a.1 ^ (q ^ d) :=
      hσF.smul_residue_eq (IsLocalRing.residue A a.1)
    have e2 : (⟨σ (a.1 : AlgebraicClosure ℚ), hmem⟩ : A) = a.1 := Subtype.ext (hσK _ a.2)
    rw [e2] at e
    exact e.symm
  have hd1 : 1 < q ^ d := Nat.one_lt_pow hd.ne' (Fact.out : q.Prime).one_lt

  set F := (Polynomial.X ^ (q ^ d) - Polynomial.X : Polynomial k).roots.toFinset with hF
  have hFcard : F.card ≤ q ^ d := by
    refine (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans ?_)
    rw [FiniteField.X_pow_card_sub_X_natDegree_eq k hd1]
  set img : Finset k := Finset.univ.image fun y : S => R.redBar (y : IsLocalRing.ResidueField A) with himg
  have hinj : Function.Injective fun y : S => R.redBar (y : IsLocalRing.ResidueField A) :=
    fun y₁ y₂ h => Subtype.ext (R.redBar.injective h)
  have himg_card : img.card = q ^ d := by
    rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_eq_nat_card, hcard]
  have hsub : img ⊆ F := by
    intro x hx
    rw [himg, Finset.mem_image] at hx
    obtain ⟨y, -, rfl⟩ := hx
    have hy : R.redBar (y : IsLocalRing.ResidueField A) ^ (q ^ d) = R.redBar y := by rw [← map_pow, hpow y]
    rw [hF, Multiset.mem_toFinset, Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero _ hd1)]
    simp [hy]
  have hEq : img = F := Finset.eq_of_subset_of_card_le hsub (hFcard.trans himg_card.ge)

  have hb' : b ^ (q ^ d) = b := by
    obtain ⟨m, hm⟩ := hev
    have h2 : ∀ n : ℕ, b ^ (q ^ 2) ^ n = b := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, pow_mul, ih, hb]
    rw [hm, ← two_mul, pow_mul, h2]
  have hbF : b ∈ F := by
    rw [hF, Multiset.mem_toFinset, Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero _ hd1)]
    simp [hb']
  rw [← hEq, himg, Finset.mem_image] at hbF
  obtain ⟨⟨y, a, rfl⟩, -, rfl⟩ := hbF
  refine ⟨⟨(a.1 : AlgebraicClosure ℚ), a.1.2, a.2⟩, ?_⟩
  show red a.1 = R.redBar (IsLocalRing.residue A a.1)
  rw [R.redBar_residue]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
include hqN hws in

private theorem mem_toValuationSubring_of_forall_hasValue_iff (hO : R.OrderLawFixed)
    (g : ↥(modularFunctionFieldBar (N * q)))
    (hg3 : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.reduceFst V = w → g ∈ V.toValuationSubring)
    (hgK : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (N * q) K)
    (W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hWb : ∀ (t : ↥(modularFunctionFieldBar (N * q)))
        (_ : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K),
        ∃ a : A, W'.HasValue t (a : AlgebraicClosure ℚ) ∧
          ((∃ h₁ : t ∈ R.R₁.integers, w.HasValue (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k)) ↔
            a ∈ IsLocalRing.maximalIdeal A)) :
    g ∈ W'.toValuationSubring := by
  rcases R.reduceFst_eq_or_eq_arithFrobC_smul_of_forall_hasValue_iff hqN K w hws hO W' hWb with hW | hW
  · exact hg3 W' hW

  have hA : A.LiesOverPrime q := by
    show ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits
    have hq : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalRing.residue_eq_zero_iff]
      apply R.redBar.injective
      rw [R.redBar_residue, map_natCast, map_zero, CharP.cast_eq_zero]
    simpa using A.coe_mem_nonunits_iff.mpr hq
  obtain ⟨d, σ, hd, hcard, hσK, hσF⟩ :=
    ValuationSubring.exists_forall_apply_eq_and_isFrobeniusAt_natCard_of_liesOverPrime q A hA K
  rcases Nat.even_or_odd d with hev | hodd
  ·
    have hk₀ : ∀ b : k, b ^ (q ^ 2) = b → b ∈ Set.range (NodeLocalized.redRestrict red K) :=
      fun b hb => mem_range_redRestrict_of_even R K σ d hd hcard hσK hσF hev b hb
    have hw₂ : P.reduceFst W' ∈ ssPlaces q N k := by
      rw [hW]
      exact ModularCurve.arithFrobC_smul_mem_ssPlaces_univ q N k w hws
    exact hg3 W' (reduceFst_eq_of_dict R hqN w hws hO K hk₀ W' hw₂ hWb)
  ·
    have hφφ : arithFrobC q k N • (arithFrobC q k N • w) = w := by
      rw [ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr (arithFrobC q k N • w),
        ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr w]
      exact PlaceSpecialization.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces hqN P w hws
    have hφ2w : arithFrobC q k N ^ 2 • w = w := by rw [pow_two, mul_smul, hφφ]
    have hφ2 : ∀ n : ℕ, (arithFrobC q k N ^ 2) ^ n • w = w := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, mul_smul, hφ2w, ih]
    obtain ⟨m, hm⟩ := hodd
    set W₂ := arithmeticGalois (modularFunctionFieldFull (N * q)) σ • W' with hW₂
    have hred : P.reduceFst W₂ = w := by
      rw [hW₂, (P.reduceFst_and_reduceSnd_arithmeticGalois_smul_of_isFrobeniusAt_pow σ d hσF W').1, hW, ← mul_smul,
        ← pow_succ, hm, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, pow_mul]
      exact hφ2 (m + 1)
    have hgW₂ : g ∈ W₂.toValuationSubring := hg3 W₂ hred
    have hσg :=
      (ModularCurve.arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver (N * q) K σ hσK g hgK).1
    rcases eq_or_ne g 0 with rfl | hg0
    · exact zero_mem _
    · apply W'.mem_of_ord_nonneg hg0
      have h := W₂.ord_nonneg_of_mem hgW₂
      rwa [← hσg, hW₂, SemilinearAut.ord_smul] at h

set_option synthInstance.maxHeartbeats 1600000 in
private theorem exists_mul_eq_of_mem_nodeIntegersOver' (hO : R.OrderLawFixed) (g : ↥(modularFunctionFieldBar (N * q)))
    (hg : g ∈ R.nodeIntegersOver K w) :
    ∃ r s : ↥(jIntegralClosure (N * q) A K), s ∉ nodeKer' R hqN K w hws ∧
      (g : LaurentSeries (AlgebraicClosure ℚ)) * (s : LaurentSeries (AlgebraicClosure ℚ))
        = (r : LaurentSeries (AlgebraicClosure ℚ)) := by
  classical
  have hred : Function.Surjective red := PlaceSpecialization.red_surjective_of_level P
  haveI : (nodeKer' R hqN K w hws).IsPrime := (nodeKer'_isMaximal R hqN K w hws hred).isPrime
  obtain ⟨hgI, hgK⟩ := (R.mem_nodeIntegersOver_iff K w g).1 hg
  obtain ⟨hg₁, hg₂, hg3⟩ := hgI
  obtain ⟨dataNq, -⟩ := ModularCurve.exists_phiIrreducible (N * q)
  obtain ⟨hCnoeth, hCic, hCfrac, -⟩ :=
    ModularCurve.jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level A N dataNq K
  haveI := hCnoeth
  haveI := hCic
  have hfrac : ∃ r s : ↥(jIntegralClosure (N * q) A K), s ≠ 0 ∧
      (g : LaurentSeries (AlgebraicClosure ℚ)) * (jIntegralClosure (N * q) A K).subtype s
        = (jIntegralClosure (N * q) A K).subtype r := by
    obtain ⟨c, s, hc, hs, hs0, hgs⟩ := hCfrac (g : LaurentSeries (AlgebraicClosure ℚ)) hgK
    exact ⟨⟨c, hc⟩, ⟨s, jRing_le_jIntegralClosure_level (q := q) K hs⟩, fun h => hs0 (congrArg Subtype.val h), hgs⟩
  have hx : ∀ (𝔭 : Ideal ↥(jIntegralClosure (N * q) A K)) [𝔭.IsPrime], 𝔭.height = 1 → 𝔭 ≤ nodeKer' R hqN K w hws →
      ∃ r s : ↥(jIntegralClosure (N * q) A K), s ∉ 𝔭 ∧
        (g : LaurentSeries (AlgebraicClosure ℚ)) * (jIntegralClosure (N * q) A K).subtype s
          = (jIntegralClosure (N * q) A K).subtype r := by
    intro 𝔭 h𝔭prime h𝔭1 h𝔭𝔫
    by_cases hq : ((q : ℕ) : ↥(jIntegralClosure (N * q) A K)) ∈ 𝔭
    · exact ModularCurve.exists_mul_eq_of_height_one_of_natCast_mem_level N hqN red K 𝔭 h𝔭1 hq g hgK
        ((R.mem_integersFst_iff g).1 hg₁) ((R.mem_integersSnd_iff g).1 hg₂)
    · have h𝔭w : ∀ (t : ↥(modularFunctionFieldBar (N * q)))
          (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K),
          (⟨(t : LaurentSeries (AlgebraicClosure ℚ)), ht⟩ : ↥(jIntegralClosure (N * q) A K)) ∈ 𝔭 →
            ∃ h₁ : t ∈ R.R₁.integers, w.HasValue (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k) := by
        intro t ht hmem

        exact (mem_nodeKer'_iff R hqN K w hws _).1 (h𝔭𝔫 hmem)
      obtain ⟨W', hW', hWb⟩ :=
        R.exists_place_forall_iff_mem_and_hasValue_of_height_one_of_natCast_notMem hqN hred K w hws 𝔭 h𝔭1 hq h𝔭w
      have hgW' : g ∈ W'.toValuationSubring :=
        mem_toValuationSubring_of_forall_hasValue_iff R hqN K w hws hO g hg3 hgK W' hWb
      exact (hW' g hgK).2 hgW'
  exact exists_mul_eq_of_forall_height_one_le_of_isIntegrallyClosed (jIntegralClosure (N * q) A K).subtype
    Subtype.val_injective (nodeKer' R hqN K w hws) (g : LaurentSeries (AlgebraicClosure ℚ)) hfrac hx

end World

end

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data} {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) :
    IsLocalRing ↥(R.nodeIntegersOver K w) ∧ IsNoetherianRing ↥(R.nodeIntegersOver K w) ∧
    ∃ 𝔪 : Ideal ↥(jIntegralClosure (N * q) A K), 𝔪.IsMaximal ∧
      ∀ g : ↥(modularFunctionFieldBar (N * q)), g ∈ R.nodeIntegersOver K w ↔
        ∃ r s : ↥(jIntegralClosure (N * q) A K), s ∉ 𝔪 ∧
          (g : LaurentSeries (AlgebraicClosure ℚ)) * (s : LaurentSeries (AlgebraicClosure ℚ))
            = (r : LaurentSeries (AlgebraicClosure ℚ)) := by
  classical
  have hws : w ∈ ssPlaces q N k := hW w hw
  have hred : Function.Surjective red := PlaceSpecialization.red_surjective_of_level P

  haveI hloc : IsLocalRing ↥(R.nodeIntegersOver K w) :=
    R.isLocalRing_nodeIntegersOver_of_orderLawFixed_of_regularityLaw hqN hO W hW hreg K w hw

  have h𝔫max := nodeKer'_isMaximal R hqN K w hws hred
  haveI h𝔫prime : (nodeKer' R hqN K w hws).IsPrime := h𝔫max.isPrime

  have hmemS : ∀ c : ↥(jIntegralClosure (N * q) A K), iotaC' K c ∈ R.nodeIntegersOver K w := fun c =>
    (R.mem_nodeIntegersOver_iff K w _).2
      ⟨(R.mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure hqN K w hws (iotaC' K c) c.2).1, c.2.1⟩
  let ι : ↥(jIntegralClosure (N * q) A K) →+* ↥(R.nodeIntegersOver K w) :=
    (iotaC' K).codRestrict (R.nodeIntegersOver K w) hmemS
  have hι_coe : ∀ c, ((ι c : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) = iotaC' K c :=
    fun _ => rfl
  have hι_inj : Function.Injective ι := fun c₁ c₂ h =>
    iotaC'_injective K (by rw [← hι_coe c₁, ← hι_coe c₂, h])

  have hunit : ∀ s : ↥(jIntegralClosure (N * q) A K), s ∉ nodeKer' R hqN K w hws → IsUnit (ι s) := by
    intro s hs
    apply R.isUnit_of_not_hasValue_nodeResidue_zero_of_isLocalRing hqN W hW hreg K w hw (ι s)
    left
    intro hv
    apply hs
    rw [mem_nodeKer'_iff]
    refine ⟨iotaC'_mem_integersFst R hqN K w hws s, ?_⟩
    rw [nodeResidue₁_apply] at hv
    exact hv

  have hiff : ∀ g : ↥(modularFunctionFieldBar (N * q)), g ∈ R.nodeIntegersOver K w ↔
      ∃ r s : ↥(jIntegralClosure (N * q) A K), s ∉ nodeKer' R hqN K w hws ∧
        (g : LaurentSeries (AlgebraicClosure ℚ)) * (s : LaurentSeries (AlgebraicClosure ℚ))
          = (r : LaurentSeries (AlgebraicClosure ℚ)) := by
    intro g
    constructor
    · exact exists_mul_eq_of_mem_nodeIntegersOver' R hqN K w hws hO g
    · rintro ⟨r, s, hs, hgs⟩
      obtain ⟨u, hu⟩ := hunit s hs

      have hBar : g * iotaC' K s = iotaC' K r := Subtype.ext hgs
      have hu' : ((u : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) = iotaC' K s :=
        (congrArg (fun t : ↥(R.nodeIntegersOver K w) => (t : ↥(modularFunctionFieldBar (N * q)))) hu).trans (hι_coe s)
      have hinv : ((↑u⁻¹ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) * iotaC' K s = 1 := by
        rw [← hu']
        exact_mod_cast congrArg Subtype.val u.inv_mul
      have hg : g = ((ι r * ↑u⁻¹ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) := by
        rw [Subring.coe_mul, hι_coe, ← hBar]
        calc g = g * (((↑u⁻¹ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) * iotaC' K s) := by
              rw [hinv, mul_one]
          _ = g * iotaC' K s * ((↑u⁻¹ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) := by ring
      rw [hg]
      exact SetLike.coe_mem _

  have hnoeth : IsNoetherianRing ↥(R.nodeIntegersOver K w) := by
    obtain ⟨dataNq, -⟩ := ModularCurve.exists_phiIrreducible (N * q)
    obtain ⟨hCnoeth, -, -, -⟩ :=
      ModularCurve.jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level A N dataNq K
    letI : Algebra ↥(jIntegralClosure (N * q) A K) ↥(R.nodeIntegersOver K w) := ι.toAlgebra
    haveI : IsLocalization (nodeKer' R hqN K w hws).primeCompl ↥(R.nodeIntegersOver K w) :=
      ⟨{ map_units := fun y => hunit y.1 y.2
         surj := fun z => by
           obtain ⟨r, s, hs, hzs⟩ := (hiff (z : ↥(modularFunctionFieldBar (N * q)))).1 z.2
           exact ⟨(r, ⟨s, hs⟩), Subtype.ext (Subtype.ext hzs)⟩
         exists_of_eq := fun {x y} h => ⟨1, by rw [hι_inj h]⟩ }⟩
    exact IsLocalization.isNoetherianRing (nodeKer' R hqN K w hws).primeCompl ↥(R.nodeIntegersOver K w) hCnoeth
  exact ⟨hloc, hnoeth, nodeKer' R hqN K w hws, h𝔫max, hiff⟩

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeIntegersOver_isLocalRing_exists_isMaximal_of_regularityLaw
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeIntegersOver_isLocalRing_exists_isMaximal_of_regularityLaw (solution)
