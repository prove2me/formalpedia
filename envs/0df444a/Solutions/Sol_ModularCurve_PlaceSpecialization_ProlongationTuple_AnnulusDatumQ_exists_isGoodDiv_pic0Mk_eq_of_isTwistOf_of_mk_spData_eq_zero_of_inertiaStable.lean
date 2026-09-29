-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/69b588fc-cd9f-5e98-a033-5d9d4ef0f8c9

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_LevelOneAnnulusSpecializationOrbit
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_exists_weilCanonical_riemannRoch
import Theorems.Thm_Finsupp_exists_eq_sum_single_of_mapDomain_eq_sum_single
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_oneSided_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawZero_oneSided_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_divisorLawFst_oneSided_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_divisorLawSnd_oneSided_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawFst_oneSided_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_not_fixed_reduceFst_of_isStrictSnd
import Theorems.Thm_ModularCurve_arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_exists_effective_pic0Mk_sub_eq_of_genusFF_le_degree
import Theorems.Thm_ModularCurve_exists_eq_algebraMap_of_hasValue_smul_of_generalPosition
import Theorems.Thm_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceOfPoint
import Theorems.Thm_ModularCurve_genusFF_modularFunctionFieldBar_mul_add_one_eq_of_ssPlaces
import Theorems.Thm_ModularCurve_isAffineGeomPlace_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff_of_perfectField
import Theorems.Thm_ModularCurve_ssPlaces_nonempty
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable
import Theorems.Thm_ModularCurve_genusFF_modularFunctionFieldC_one_eq_zero
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_two
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_three
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ValuationSubring.instIsAlgClosedResidueField ModularCurve.TatePoint.instIsElliptic_nearCurve WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.B3.instIsElliptic_goodModel ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.numberField_of_finiteDimensional AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase"
p2m_attr_erase "instance" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar AlgebraicCurve.GaussReduction.isLocalHom_constToGauss"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe ModularCurve.cuspCount_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero"
p2m_attr_erase "simp" "FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero ModularCurve.symPoly_zero AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_integers ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_nodes ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_residue ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_dom ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_placeMap AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers"
set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve"

namespace ModularCurve p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple PlaceSpecialization.fstDiv PlaceSpecialization.sndDiv PlaceSpecialization.glueData arithmeticGalois modularFunctionFieldBar ModularPolynomialData modularFunctionFieldFull modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence nodePairsOfPlaces mem_nodePairsOfPlaces_iff ssPlaces jGeomGen jNGeomGen jNGeomGen_one IsCentreOf IsAffineGeomPlace arithFrobC PlaceSpecialization.ProlongationTuple.AnnulusDatumQ NodeLocalized.coeffSubring NodeLocalized.redRestrict PlaceSpecialization.ProlongationTuple.AnnulusDatum jWidth PlaceSpecialization.ProlongationTuple.cuspLawInfty_oneSided_levelOne PlaceSpecialization.ProlongationTuple.cuspLawZero_oneSided_levelOne PlaceSpecialization.ProlongationTuple.divisorLawFst_oneSided_levelOne PlaceSpecialization.ProlongationTuple.divisorLawSnd_oneSided_levelOne PlaceSpecialization.ProlongationTuple.regularityLawFst_oneSided_levelOne PlaceSpecialization.ProlongationTuple.regularityLawSnd_oneSided_levelOne PlaceSpecialization.exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace PlaceSpecialization.exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq PlaceSpecialization.not_fixed_reduceFst_of_isStrictSnd arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces arithFrobC_smul_eq_frobOnPlacesGeomLevel deg_eq_one_modularFunctionFieldBar essFiniteType_modularFunctionFieldFullC exists_effective_pic0Mk_sub_eq_of_genusFF_le_degree exists_eq_algebraMap_of_hasValue_smul_of_generalPosition finite_setOf_ord_jGeomGen_sub_pos frobOnPlacesGeomLevel_charLGeomPlaceOfPoint genusFF_modularFunctionFieldBar_mul_add_one_eq_of_ssPlaces isAffineGeomPlace_frobOnPlacesGeomLevel isCurveOver_modularFunctionFieldBar isCurveOver_modularFunctionFieldC_of_perfectField isSeparable_jqNModC_of_natCast_ne_zero mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq modularFunctionFieldC_eq_modularFunctionFieldFullC pow_mem_ssJSet_iff_of_perfectField ssPlaces_nonempty PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable" namespace PlaceSpecialization p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple ProlongationTuple.residue₁_apply ProlongationTuple.residue₂_apply reduceFst reduceSnd IsStrictFst IsStrictSnd IsGoodDiv fstDiv sndDiv glueData sp mk d1 ProlongationTuple.AnnulusDatumQ ProlongationTuple.AnnulusDatum ProlongationTuple.TwistVector ProlongationTuple.cuspLawInfty_oneSided_levelOne ProlongationTuple.cuspLawZero_oneSided_levelOne ProlongationTuple.divisorLawFst_oneSided_levelOne ProlongationTuple.divisorLawSnd_oneSided_levelOne ProlongationTuple.regularityLawFst_oneSided_levelOne ProlongationTuple.regularityLawSnd_oneSided_levelOne exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq not_fixed_reduceFst_of_isStrictSnd ProlongationTuple.AnnulusDatumQ.exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable" namespace ProlongationTuple p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "residue₁ residue₂ residue₁_apply residue₂_apply OrderLawFixed IsModel NodeValueLaw RegularityLaw R₁ mk ι redBar_residue R₂ redBar AnnulusDatumQ AnnulusDatumQ.chainVal AnnulusDatumQ.endSlopeFst AnnulusDatumQ.endSlopeSnd ValueIntegralityLaw nodeResidue₁ nodeResidue₂ nodeIntegersOver nodeConst AnnulusDatum TwistVector cuspLawInfty_oneSided_levelOne cuspLawZero_oneSided_levelOne divisorLawFst_oneSided_levelOne divisorLawSnd_oneSided_levelOne regularityLawFst_oneSided_levelOne regularityLawSnd_oneSided_levelOne AnnulusDatumQ.exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable" end ModularCurve.PlaceSpecialization.ProlongationTuple
p2m_open_scoped "ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple" in
open _root_.ModularCurve.PlaceSpecialization in
theorem ModularCurve.PlaceSpecialization.ProlongationTuple.residue_bounds_offNodes_of_adm_oneSided
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.ProlongationTuple} (hR : R.IsModel)
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (hRL : R.RegularityLaw W)
    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
    (hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
    {T₁ T₂ : Finset (Place k ↥(modularFunctionFieldC k 1))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v)
    (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v)
    (E D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hE : 0 ≤ E)
    (hD : ∀ V ∈ D.support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)
    (G : ↥(modularFunctionFieldBar (1 * q)))
    (hdiv : ∀ V, (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - D) V
      = V.ord G) :
    (∀ (h₁ : G ∈ R.R₁.integers), R.residue₁ ⟨G, h₁⟩ ≠ 0 → ∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ W →
      -Finsupp.mapDomain P.reduceFst (∑ i, Finsupp.single (Q₁ i) (1 : ℤ)) v
        - Finsupp.mapDomain P.reduceFst (P.fstDiv D) v ≤ v.ord (R.residue₁ ⟨G, h₁⟩)) ∧
    (∀ (h₂ : G ∈ R.R₂.integers), R.residue₂ ⟨G, h₂⟩ ≠ 0 → ∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ W →
      -Finsupp.mapDomain P.reduceSnd (∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) v
        - Finsupp.mapDomain P.reduceSnd (P.sndDiv D) v ≤ v.ord (R.residue₂ ⟨G, h₂⟩)) := by
  classical
  have hqN : ¬ q ∣ 1 := fun h => (Fact.out : q.Prime).ne_one (Nat.dvd_one.mp h)

  set E₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) :=
    ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) with hE₁
  set E₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) :=
    ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) with hE₂
  have hE' : ∀ W, 0 ≤ E W := fun W => by simpa using Finsupp.le_def.mp hE W
  have hphiσ : ∀ w : Place k ↥(modularFunctionFieldC k 1), arithFrobC q k 1 • w = frobOnPlacesGeomLevel k 1 data hKr w :=
    fun w => ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr w
  have hphiinj : Function.Injective (frobOnPlacesGeomLevel k 1 data hKr) := by
    intro a b h
    rw [← hphiσ, ← hphiσ] at h
    exact smul_left_cancel _ h
  have hWfix : ∀ w ∈ W, frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr w) = w := by
    intro w hw
    have h := ModularCurve.arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces q 1 hqN k w
      ((hW w).mp hw)
    rwa [hphiσ, hphiσ] at h

  have hnf₁ : ∀ V, P.IsStrictFst V ∨ P.IsStrictSnd V → frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst V)) ≠ P.reduceFst V := by
    rintro V (hV | hV)
    · exact hV.2
    · exact ModularCurve.PlaceSpecialization.not_fixed_reduceFst_of_isStrictSnd P V hV
  have hnf₂ : ∀ V, P.IsStrictFst V ∨ P.IsStrictSnd V → frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceSnd V)) ≠ P.reduceSnd V := by
    rintro V (hV | hV)
    · intro hfix
      apply hV.2
      have h1 : frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst V) = P.reduceSnd V := hV.1
      apply hphiinj
      rw [h1]
      exact hfix
    · exact hV.2
  have hexcl : ∀ V, P.IsStrictFst V → P.IsStrictSnd V → False := by
    intro V h1 h2
    apply h1.2
    have e1 : frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst V) = P.reduceSnd V := h1.1
    have e2 : P.reduceFst V = frobOnPlacesGeomLevel k 1 data hKr (P.reduceSnd V) := h2.1
    conv_rhs => rw [e2]
    rw [e1]

  have hE₁apply : ∀ V, E₁ V = ∑ i, if Q₁ i = V then (1 : ℤ) else 0 := fun V => by
    rw [hE₁, Finsupp.finsetSum_apply]; simp only [Finsupp.single_apply]
  have hE₂apply : ∀ V, E₂ V = ∑ j, if Q₂ j = V then (1 : ℤ) else 0 := fun V => by
    rw [hE₂, Finsupp.finsetSum_apply]; simp only [Finsupp.single_apply]
  have hE₁zero : ∀ V, (∀ i, Q₁ i ≠ V) → E₁ V = 0 := fun V h => by
    rw [hE₁apply]; exact Finset.sum_eq_zero fun i _ => if_neg (h i)
  have hE₂zero : ∀ V, (∀ j, Q₂ j ≠ V) → E₂ V = 0 := fun V h => by
    rw [hE₂apply]; exact Finset.sum_eq_zero fun j _ => if_neg (h j)
  have hE₁strict : ∀ V, E₁ V ≠ 0 → P.IsStrictFst V := fun V hV => by
    by_contra h; exact hV (hE₁zero V fun i hi => h (hi ▸ hQ₁ i))
  have hE₂strict : ∀ V, E₂ V ≠ 0 → P.IsStrictSnd V := fun V hV => by
    by_contra h; exact hV (hE₂zero V fun j hj => h (hj ▸ hQ₂ j))
  have hE₀strict : ∀ V, (E₁ + E₂) V ≠ 0 → P.IsStrictFst V ∨ P.IsStrictSnd V := by
    intro V hV
    rw [Finsupp.add_apply] at hV
    by_cases h1 : E₁ V = 0
    · rw [h1, zero_add] at hV; exact Or.inr (hE₂strict V hV)
    · exact Or.inl (hE₁strict V h1)
  have hDadm : ∀ V, D V ≠ 0 → P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W :=
    fun V hV => hD V (Finsupp.mem_support_iff.mpr hV)

  have hWstab : ∀ v : Place k ↥(modularFunctionFieldC k 1),
      frobOnPlacesGeomLevel k 1 data hKr v ∈ ssPlaces q 1 k ↔ v ∈ ssPlaces q 1 k := by
    haveI : PerfectField k := inferInstance
    intro v
    constructor
    · intro h
      obtain ⟨a, ha, hav⟩ := (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k _).mp h
      obtain ⟨b, rfl⟩ := IsAlgClosed.exists_pow_nat_eq a (Fact.out : q.Prime).pos
      rw [← ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceOfPoint k data hKr b] at hav
      have hv := hphiinj hav
      rw [← hv]
      exact (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k _).mpr
        ⟨b, (ModularCurve.pow_mem_ssJSet_iff_of_perfectField q b).mp ha, rfl⟩
    · intro h
      obtain ⟨a, ha, rfl⟩ := (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k _).mp h
      rw [ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceOfPoint]
      exact (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k _).mpr
        ⟨a ^ q, (ModularCurve.pow_mem_ssJSet_iff_of_perfectField q a).mpr ha, rfl⟩
  have hWφ : ∀ v, frobOnPlacesGeomLevel k 1 data hKr v ∈ W → v ∈ W := fun v hv =>
    (hW v).mpr ((hWstab v).mp ((hW _).mp hv))
  have hWφ' : ∀ v, v ∈ W → frobOnPlacesGeomLevel k 1 data hKr v ∈ W := fun v hv =>
    (hW _).mpr ((hWstab v).mpr ((hW v).mp hv))

  have hDsnd : ∀ V, D V ≠ 0 → P.reduceFst V ∈ W → P.reduceSnd V ∈ W := by
    intro V _ hV
    rcases P.d1 V with h | h
    · change P.reduceFst V = frobOnPlacesGeomLevel k 1 data hKr (P.reduceSnd V) at h
      exact hWφ _ (by rw [← h]; exact hV)
    · change frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst V) = P.reduceSnd V at h
      rw [← h]
      exact hWφ' _ hV

  have hDnf₁ : ∀ V v, D V ≠ 0 → v ∉ W → P.reduceFst V = v →
      frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) ≠ v := by
    intro V v hV hv hVv
    rcases hDadm V hV with h | h | h
    · rw [← hVv]; exact hnf₁ V (Or.inl h)
    · rw [← hVv]; exact hnf₁ V (Or.inr h)
    · exact absurd (hVv ▸ h) hv
  have hDnf₂ : ∀ V v, D V ≠ 0 → v ∉ W → P.reduceSnd V = v →
      frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) ≠ v := by
    intro V v hV hv hVv
    rcases hDadm V hV with h | h | h
    · rw [← hVv]; exact hnf₂ V (Or.inl h)
    · rw [← hVv]; exact hnf₂ V (Or.inr h)
    · exact absurd (hVv ▸ hDsnd V hV h) hv
  have hE₁T1 : E₁.filter P.IsStrictFst = E₁ := by
    rw [Finsupp.filter_eq_self_iff]; exact hE₁strict
  have hE₂T2 : E₂.filter P.IsStrictSnd = E₂ := by
    rw [Finsupp.filter_eq_self_iff]; exact hE₂strict
  have hE₂T1 : E₂.filter P.IsStrictFst = 0 := by
    rw [Finsupp.filter_eq_zero_iff]
    intro V hV; by_contra h; exact hexcl V hV (hE₂strict V h)
  have hE₁T2 : E₁.filter P.IsStrictSnd = 0 := by
    rw [Finsupp.filter_eq_zero_iff]
    intro V hV; by_contra h; exact hexcl V (hE₁strict V h) hV

  have hfix₁ : ∀ V, frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst V)) = P.reduceFst V → P.reduceFst V ∉ W → (E₁ + E₂) V = 0 ∧ D V = 0 := by
    intro V hV hVW
    exact ⟨by_contra fun h => hnf₁ V (hE₀strict V h) hV, by_contra fun h => hDnf₁ V _ h hVW rfl hV⟩
  have hfix₂ : ∀ V, frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceSnd V)) = P.reduceSnd V → P.reduceSnd V ∉ W → (E₁ + E₂) V = 0 ∧ D V = 0 := by
    intro V hV hVW
    exact ⟨by_contra fun h => hnf₂ V (hE₀strict V h) hV, by_contra fun h => hDnf₂ V _ h hVW rfl hV⟩
  have hGreg₁ : ∀ V, frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst V)) = P.reduceFst V → P.reduceFst V ∉ W → 0 ≤ V.ord G := by
    intro V hV hVW
    rw [← hdiv V, Finsupp.sub_apply, Finsupp.sub_apply, (hfix₁ V hV hVW).1, (hfix₁ V hV hVW).2,
      sub_zero, sub_zero]
    exact hE' V

  have mapDomain_nonneg : ∀ (g : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) →
        Place k ↥(modularFunctionFieldC k 1))
      (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))), (∀ V, 0 ≤ X V) →
      ∀ v, 0 ≤ Finsupp.mapDomain g X v := by
    intro g X hX v
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
    exact Finset.sum_nonneg fun V _ => by
      simp only [Finsupp.single_apply]
      split_ifs
      · exact hX V
      · exact le_rfl
  have mapDomain_eq_zero : ∀ (g : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) →
        Place k ↥(modularFunctionFieldC k 1))
      (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
      (v : Place k ↥(modularFunctionFieldC k 1)),
      (∀ V, X V ≠ 0 → g V ≠ v) → Finsupp.mapDomain g X v = 0 := by
    intro g X v h
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
    exact Finset.sum_eq_zero fun V hV => by
      simp only [Finsupp.single_apply]
      exact if_neg (h V (Finsupp.mem_support_iff.mp hV))
  have hfilter_nonneg : ∀ (p : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → Prop)
      [DecidablePred p] (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
      0 ≤ (E.filter p) V := by
    intro p _ V
    rw [Finsupp.filter_apply]
    split_ifs
    · exact hE' V
    · exact le_rfl
  have filter_ne_zero : ∀ (p : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → Prop)
      [DecidablePred p] (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (V),
      (X.filter p) V ≠ 0 → X V ≠ 0 := by
    intro p _ X V h hX
    apply h
    rw [Finsupp.filter_apply, hX, ite_self]

  have hEbar₁ : ∀ v, Finsupp.mapDomain P.reduceFst E₁ v =
      ∑ i, if P.reduceFst (Q₁ i) = v then (1 : ℤ) else 0 := by
    intro v
    rw [hE₁, Finsupp.mapDomain_finsetSum, Finsupp.finsetSum_apply]
    simp only [Finsupp.mapDomain_single, Finsupp.single_apply]
  have hEbar₂ : ∀ v, Finsupp.mapDomain P.reduceSnd E₂ v =
      ∑ j, if P.reduceSnd (Q₂ j) = v then (1 : ℤ) else 0 := by
    intro v
    rw [hE₂, Finsupp.mapDomain_finsetSum, Finsupp.finsetSum_apply]
    simp only [Finsupp.mapDomain_single, Finsupp.single_apply]
  have hEbar₁_nn : ∀ v, 0 ≤ Finsupp.mapDomain P.reduceFst E₁ v := fun v => by
    rw [hEbar₁]; exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
  have hEbar₂_nn : ∀ v, 0 ≤ Finsupp.mapDomain P.reduceSnd E₂ v := fun v => by
    rw [hEbar₂]; exact Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num
  have hEbar₁_off : ∀ v, v ∉ T₁ → Finsupp.mapDomain P.reduceFst E₁ v = 0 := fun v hv => by
    rw [hEbar₁]; exact Finset.sum_eq_zero fun i _ => if_neg fun h => hv ((hT₁ v).mpr ⟨i, h⟩)
  have hEbar₂_off : ∀ v, v ∉ T₂ → Finsupp.mapDomain P.reduceSnd E₂ v = 0 := fun v hv => by
    rw [hEbar₂]; exact Finset.sum_eq_zero fun j _ => if_neg fun h => hv ((hT₂ v).mpr ⟨j, h⟩)
  have hEbar₁_le : ∀ v, Finsupp.mapDomain P.reduceFst E₁ v ≤ 1 := by
    intro v
    rw [hEbar₁]
    by_cases hv : ∃ i, P.reduceFst (Q₁ i) = v
    · obtain ⟨i, hi⟩ := hv
      rw [Finset.sum_eq_single i (fun j _ hji => if_neg fun h => hji (hinj₁ (h.trans hi.symm)))
        (fun h => absurd (Finset.mem_univ i) h), if_pos hi]
    · push Not at hv
      rw [Finset.sum_eq_zero fun i _ => if_neg (hv i)]; norm_num
  have hEbar₂_le : ∀ v, Finsupp.mapDomain P.reduceSnd E₂ v ≤ 1 := by
    intro v
    rw [hEbar₂]
    by_cases hv : ∃ j, P.reduceSnd (Q₂ j) = v
    · obtain ⟨j, hj⟩ := hv
      rw [Finset.sum_eq_single j (fun i _ hij => if_neg fun h => hij (hinj₂ (h.trans hj.symm)))
        (fun h => absurd (Finset.mem_univ j) h), if_pos hj]
    · push Not at hv
      rw [Finset.sum_eq_zero fun j _ => if_neg (hv j)]; norm_num

  have hfst0 : ∀ v, frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v → Finsupp.mapDomain P.reduceFst (P.fstDiv D) v = 0 := by
    intro v hv
    apply mapDomain_eq_zero
    intro V hV hVv
    rw [ModularCurve.PlaceSpecialization.fstDiv, Finsupp.filter_apply] at hV
    split_ifs at hV with hT
    · exact hT.2 (by rw [hVv]; exact hv)
    · exact hV rfl
  have hsnd0 : ∀ v, frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v → Finsupp.mapDomain P.reduceSnd (P.sndDiv D) v = 0 := by
    intro v hv
    apply mapDomain_eq_zero
    intro V hV hVv
    rw [ModularCurve.PlaceSpecialization.sndDiv, Finsupp.filter_apply] at hV
    split_ifs at hV with hT
    · exact hT.2 (by rw [hVv]; exact hv)
    · exact hV rfl

  have hf₁ : ∀ (h₁ : G ∈ R.R₁.integers), R.residue₁ ⟨G, h₁⟩ ≠ 0 → R.R₁.residue ⟨G, h₁⟩ ≠ 0 := fun h₁ hr h =>
    hr (by rw [ProlongationTuple.residue₁_apply, h, map_zero])
  have hf₂ : ∀ (h₂ : G ∈ R.R₂.integers), R.residue₂ ⟨G, h₂⟩ ≠ 0 → R.R₂.residue ⟨G, h₂⟩ ≠ 0 := fun h₂ hr h =>
    hr (by rw [ProlongationTuple.residue₂_apply, h, map_zero])

  have hdiv' : ∀ V, (E - (E₁ + E₂) - D) V = V.ord G := hdiv

  have key₁ : ∀ (h₁ : G ∈ R.R₁.integers), R.residue₁ ⟨G, h₁⟩ ≠ 0 → ∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ W →
      -Finsupp.mapDomain P.reduceFst E₁ v - Finsupp.mapDomain P.reduceFst (P.fstDiv D) v ≤
        v.ord (R.residue₁ ⟨G, h₁⟩) := by
    intro h₁ hr v hvW
    by_cases hv : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v
    ·
      rw [hfst0 v hv, sub_zero]
      refine le_trans (neg_nonpos.mpr (hEbar₁_nn v)) ?_
      by_cases haff : IsAffineGeomPlace k 1 v
      ·
        exact ModularCurve.PlaceSpecialization.ProlongationTuple.regularityLawFst_oneSided_levelOne P W hW R hRL
          G h₁ (hf₁ h₁ hr) v hv haff hvW (fun V hV => hGreg₁ V (by rw [hV]; exact hv) (by rw [hV]; exact hvW))
      ·
        obtain ⟨⟨C, hC, hCv⟩, -⟩ :=
          ModularCurve.PlaceSpecialization.exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
            hqN P v haff
        have hlaw := ModularCurve.PlaceSpecialization.ProlongationTuple.cuspLawInfty_oneSided_levelOne P R hR
          G h₁ (hf₁ h₁ hr) (E - (E₁ + E₂) - D) hdiv' C hC
        rw [hCv] at hlaw
        rw [← hlaw, Finsupp.filter_sub, Finsupp.filter_sub, Finsupp.mapDomain_sub,
          Finsupp.mapDomain_sub, Finsupp.sub_apply, Finsupp.sub_apply,
          mapDomain_eq_zero P.reduceFst ((E₁ + E₂).filter _) v
            (fun V hV hVv => hnf₁ V (hE₀strict V (filter_ne_zero _ _ V hV)) (by rw [hVv]; exact hv)),
          mapDomain_eq_zero P.reduceFst (D.filter _) v
            (fun V hV hVv => hDnf₁ V v (filter_ne_zero _ _ V hV) hvW hVv hv),
          sub_zero, sub_zero]
        exact mapDomain_nonneg _ _ (hfilter_nonneg _) _
    ·
      have hlaw := ModularCurve.PlaceSpecialization.ProlongationTuple.divisorLawFst_oneSided_levelOne P R hR
        G h₁ (hf₁ h₁ hr) (E - (E₁ + E₂) - D) hdiv' v hv
      rw [← hlaw, Finsupp.filter_sub, Finsupp.filter_sub, Finsupp.filter_add, hE₁T1, hE₂T1, add_zero,
        Finsupp.mapDomain_sub, Finsupp.mapDomain_sub, Finsupp.sub_apply, Finsupp.sub_apply]
      change -Finsupp.mapDomain P.reduceFst E₁ v - Finsupp.mapDomain P.reduceFst (D.filter P.IsStrictFst) v ≤ _
      linarith [mapDomain_nonneg P.reduceFst (E.filter P.IsStrictFst) (hfilter_nonneg _) v]

  have key₂ : ∀ (h₂ : G ∈ R.R₂.integers), R.residue₂ ⟨G, h₂⟩ ≠ 0 → ∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ W →
      -Finsupp.mapDomain P.reduceSnd E₂ v - Finsupp.mapDomain P.reduceSnd (P.sndDiv D) v ≤
        v.ord (R.residue₂ ⟨G, h₂⟩) := by
    intro h₂ hr v hvW
    by_cases hv : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v
    · rw [hsnd0 v hv, sub_zero]
      refine le_trans (neg_nonpos.mpr (hEbar₂_nn v)) ?_
      by_cases haff : IsAffineGeomPlace k 1 v
      ·
        have hu : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v)) = frobOnPlacesGeomLevel k 1 data hKr v := by rw [hv]
        have huaff : IsAffineGeomPlace k 1 (frobOnPlacesGeomLevel k 1 data hKr v) :=
          ModularCurve.isAffineGeomPlace_frobOnPlacesGeomLevel k 1 data hKr v haff
        have huW : frobOnPlacesGeomLevel k 1 data hKr v ∉ W := fun h => hvW (hWφ v h)
        have h := ModularCurve.PlaceSpecialization.ProlongationTuple.regularityLawSnd_oneSided_levelOne P W hW R hRL
          G h₂ (hf₂ h₂ hr) (frobOnPlacesGeomLevel k 1 data hKr v) hu huaff huW
          (fun V hV => hGreg₁ V (by rw [hV]; exact hu) (by rw [hV]; exact huW))
        rwa [hv] at h
      ·
        obtain ⟨-, ⟨C, hC, hCv⟩⟩ :=
          ModularCurve.PlaceSpecialization.exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
            hqN P v haff
        have hlaw := ModularCurve.PlaceSpecialization.ProlongationTuple.cuspLawZero_oneSided_levelOne P R hR
          G h₂ (hf₂ h₂ hr) (E - (E₁ + E₂) - D) hdiv' C hC
        rw [hCv] at hlaw
        rw [← hlaw, Finsupp.filter_sub, Finsupp.filter_sub, Finsupp.mapDomain_sub,
          Finsupp.mapDomain_sub, Finsupp.sub_apply, Finsupp.sub_apply,
          mapDomain_eq_zero P.reduceSnd ((E₁ + E₂).filter _) v
            (fun V hV hVv => hnf₂ V (hE₀strict V (filter_ne_zero _ _ V hV)) (by rw [hVv]; exact hv)),
          mapDomain_eq_zero P.reduceSnd (D.filter _) v
            (fun V hV hVv => hDnf₂ V v (filter_ne_zero _ _ V hV) hvW hVv hv),
          sub_zero, sub_zero]
        exact mapDomain_nonneg _ _ (hfilter_nonneg _) _
    · have hlaw := ModularCurve.PlaceSpecialization.ProlongationTuple.divisorLawSnd_oneSided_levelOne P R hR
        G h₂ (hf₂ h₂ hr) (E - (E₁ + E₂) - D) hdiv' v hv
      rw [← hlaw, Finsupp.filter_sub, Finsupp.filter_sub, Finsupp.filter_add, hE₁T2, hE₂T2, zero_add,
        Finsupp.mapDomain_sub, Finsupp.mapDomain_sub, Finsupp.sub_apply, Finsupp.sub_apply]
      change -Finsupp.mapDomain P.reduceSnd E₂ v - Finsupp.mapDomain P.reduceSnd (D.filter P.IsStrictSnd) v ≤ _
      linarith [mapDomain_nonneg P.reduceSnd (E.filter P.IsStrictSnd) (hfilter_nonneg _) v]

  exact ⟨key₁, key₂⟩

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false
set_option linter.unusedVariables false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve"

namespace ChainMP

theorem slope_antitone (e : ℕ) (y : ℕ → ℤ)
    (hconc : ∀ d : ℕ, 1 ≤ d → d + 1 ≤ e → y (d + 1) - y d ≤ y d - y (d - 1))
    (d d' : ℕ) (hd : 1 ≤ d) (hdd' : d ≤ d') (hd' : d' ≤ e) :
    y d' - y (d' - 1) ≤ y d - y (d - 1) := by
  induction d', hdd' using Nat.le_induction with
  | base => exact le_rfl
  | succ n hdn ih =>
    have h1 := hconc n (le_trans hd hdn) hd'
    have h2 := ih (by omega)
    rw [Nat.add_sub_cancel]
    linarith

theorem sub_le_mul_first_slope (e : ℕ) (y : ℕ → ℤ)
    (hconc : ∀ d : ℕ, 1 ≤ d → d + 1 ≤ e → y (d + 1) - y d ≤ y d - y (d - 1))
    (d : ℕ) (hd : d ≤ e) : y d - y 0 ≤ (d : ℤ) * (y 1 - y 0) := by
  induction d with
  | zero => simp
  | succ n ih =>
    have h1 := slope_antitone e y hconc 1 (n + 1) le_rfl (by omega) hd
    simp only [Nat.add_sub_cancel, Nat.sub_self] at h1
    have h2 := ih (by omega)
    push_cast
    linarith

theorem mul_last_slope_le_sub (e : ℕ) (y : ℕ → ℤ)
    (hconc : ∀ d : ℕ, 1 ≤ d → d + 1 ≤ e → y (d + 1) - y d ≤ y d - y (d - 1)) :
    ∀ d : ℕ, d ≤ e → (d : ℤ) * (y e - y (e - 1)) ≤ y d - y 0 := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have h1 := slope_antitone e y hconc (n + 1) e (by omega) hn le_rfl
    rw [Nat.add_sub_cancel] at h1
    have h2 := ih (by omega)
    push_cast
    linarith

theorem chain_const_of_concave_of_ends_eq (e : ℕ) (y : ℕ → ℤ)
    (hconc : ∀ d : ℕ, 1 ≤ d → d + 1 ≤ e → y (d + 1) - y d ≤ y d - y (d - 1))
    (hends : y e = y 0) (hlast : 0 ≤ y e - y (e - 1)) :
    ∀ d : ℕ, d ≤ e → y d = y 0 := by

  have hslope : ∀ d : ℕ, 1 ≤ d → d ≤ e → 0 ≤ y d - y (d - 1) := fun d hd hde =>
    hlast.trans (slope_antitone e y hconc d e hd hde le_rfl)
  have hmono : ∀ d d' : ℕ, d ≤ d' → d' ≤ e → y d ≤ y d' := by
    intro d d' hdd' hd'
    induction d', hdd' using Nat.le_induction with
    | base => exact le_rfl
    | succ n hdn ih =>
      have h1 := hslope (n + 1) (by omega) hd'
      rw [Nat.add_sub_cancel] at h1
      have h2 := ih (by omega)
      linarith
  intro d hd
  have h1 := hmono 0 d (Nat.zero_le _) hd
  have h2 := hmono d e hd le_rfl
  rw [hends] at h2
  exact le_antisymm h2 h1

theorem one_le_first_slope_of_lt (e : ℕ) (y : ℕ → ℤ)
    (hconc : ∀ d : ℕ, 1 ≤ d → d + 1 ≤ e → y (d + 1) - y d ≤ y d - y (d - 1))
    (hlt : y 0 < y e) : 1 ≤ y 1 - y 0 := by
  have h := sub_le_mul_first_slope e y hconc e le_rfl
  by_contra hc
  push Not at hc
  have : (e : ℤ) * (y 1 - y 0) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
  linarith

theorem one_le_neg_last_slope_of_lt (e : ℕ) (y : ℕ → ℤ)
    (hconc : ∀ d : ℕ, 1 ≤ d → d + 1 ≤ e → y (d + 1) - y d ≤ y d - y (d - 1))
    (hlt : y e < y 0) : 1 ≤ y (e - 1) - y e := by
  have h := mul_last_slope_le_sub e y hconc e le_rfl
  by_contra hc
  push Not at hc
  have : 0 ≤ (e : ℤ) * (y e - y (e - 1)) := mul_nonneg (by positivity) (by omega)
  linarith

end ChainMP

namespace ChartOkA2

def D2 (f : ℕ → ℤ) (d : ℕ) : ℤ := f (d - 1) - 2 * f d + f (d + 1)

theorem D2_add (f g : ℕ → ℤ) (d : ℕ) : D2 (fun i => f i + g i) d = D2 f d + D2 g d := by
  unfold D2; ring

theorem D2_profile_add_twist_eq_neg (γ a : ℕ → ℤ) (Ecirc Dcirc : ℕ → ℤ) (d : ℕ)
    (hslope : D2 γ d = -(Ecirc d - Dcirc d)) (htwist : Dcirc d = -(D2 a d)) :
    D2 (fun i => γ i + a i) d = -Ecirc d := by
  rw [D2_add, hslope, htwist]; ring

theorem hconc_of_D2_nonpos (y : ℕ → ℤ) (e : ℕ)
    (h : ∀ d, 1 ≤ d → d + 1 ≤ e → D2 y d ≤ 0) :
    ∀ d, 1 ≤ d → d + 1 ≤ e → y (d + 1) - y d ≤ y d - y (d - 1) := by
  intro d hd hde
  have := h d hd hde
  unfold D2 at this
  linarith

theorem concave_profile_add_twist (γ a : ℕ → ℤ) (Ecirc Dcirc : ℕ → ℤ) (e : ℕ)
    (hslope : ∀ d, 1 ≤ d → d + 1 ≤ e → D2 γ d = -(Ecirc d - Dcirc d))
    (htwist : ∀ d, 1 ≤ d → d + 1 ≤ e → Dcirc d = -(D2 a d))
    (hE : ∀ d, 0 ≤ Ecirc d) :
    ∀ d, 1 ≤ d → d + 1 ≤ e → (γ (d + 1) + a (d + 1)) - (γ d + a d) ≤ (γ d + a d) - (γ (d - 1) + a (d - 1)) := by
  refine hconc_of_D2_nonpos (fun i => γ i + a i) e fun d hd hde => ?_
  rw [D2_profile_add_twist_eq_neg γ a Ecirc Dcirc d (hslope d hd hde) (htwist d hd hde)]
  linarith [hE d]

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

theorem hasValue_zero_of_ord_pos (v : Place k F) {g : F} (hg : g ≠ 0) (h : 0 < v.ord g) : v.HasValue g 0 := by
  have hmem : g ∈ v.toValuationSubring := v.mem_of_ord_nonneg hg h.le
  refine ⟨hmem, ?_⟩
  rw [map_zero]
  have : (⟨g, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [IsLocalRing.mem_maximalIdeal]
    intro hu
    have h0 := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at h0
    change v.ord g = 0 at h0
    omega
  rwa [← IsLocalRing.residue_eq_zero_iff] at this

theorem eq_zero_of_hasValue_algebraMap_zero (v : Place k F) {c : k} (h : v.HasValue (algebraMap k F c) 0) : c = 0 :=
  (v.hasValue_algebraMap c).unique h

open Classical in

theorem carrier_hypotheses_of_endSlopes
    (φ : Place k F → Place k F) (hφ : Function.Injective φ)
    (W T₁ T₂ : Finset (Place k F)) (hWne : W.Nonempty)
    (hWfix : ∀ w ∈ W, φ (φ w) = w) (hWφ : ∀ w ∈ W, φ w ∈ W)
    (hT₁ : ∀ v ∈ T₁, φ (φ v) ≠ v) (hT₂ : ∀ v ∈ T₂, φ (φ v) ≠ v)
    (Ebar₁ Ebar₂ EE₁ EE₂ : Place k F → ℤ)
    (hEbar₁ : ∀ v, Ebar₁ v = if v ∈ T₁ then 1 else 0) (hEbar₂ : ∀ v, Ebar₂ v = if v ∈ T₂ then 1 else 0)
    (hEE₁ : ∀ v, 0 ≤ EE₁ v) (hEE₂ : ∀ v, 0 ≤ EE₂ v)
    (u₁ u₂ : F) (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (O1₁ : ∀ v, φ (φ v) ≠ v → (v.ord u₁ : ℤ) = EE₁ v - Ebar₁ v)
    (O1₂ : ∀ v, φ (φ v) ≠ v → (v.ord u₂ : ℤ) = EE₂ v - Ebar₂ v)
    (O2₁ : ∀ v, φ (φ v) = v → v ∉ W → 0 ≤ v.ord u₁) (O2₂ : ∀ v, φ (φ v) = v → v ∉ W → 0 ≤ v.ord u₂)
    (e : Place k F → ℕ) (he : ∀ w ∈ W, 1 ≤ e w) (δ : ℚ)
    (A₁ : ∀ w ∈ W, δ ≤ (e w : ℚ) * ((w.ord u₁ : ℤ) : ℚ))
    (A₂ : ∀ w ∈ W, -((e w : ℚ) * (((φ w).ord u₂ : ℤ) : ℚ)) ≤ δ)
    (B : ∀ w ∈ W, δ = 0 → (φ w).ord u₂ = 0 → w.ord u₁ = 0 ∧ ∃ c : k, w.HasValue u₁ c ∧ (φ w).HasValue u₂ c)
    (hgp₁ : ∀ h : F, (∀ v, v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) → (∀ w ∈ W, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : F, (∀ v, v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) → ∃ c : k, h = algebraMap k F c) :
    (∀ v, v ∉ T₁ → 0 ≤ v.ord u₁) ∧ (∀ v ∈ T₁, -1 ≤ v.ord u₁) ∧
    (∀ v, v ∉ T₂ → 0 ≤ v.ord u₂) ∧ (∀ v ∈ T₂, -1 ≤ v.ord u₂) ∧
    (∀ w ∈ W, ∃ c : k, w.HasValue u₁ c ∧ (φ w).HasValue u₂ c) := by
  classical
  have hWT₁ : ∀ w ∈ W, w ∉ T₁ := fun w hw h => hT₁ w h (hWfix w hw)
  have hWT₂ : ∀ w ∈ W, w ∉ T₂ := fun w hw h => hT₂ w h (hWfix w hw)
  have hWsurj : ∀ v ∈ W, ∃ w ∈ W, φ w = v := fun v hv => ⟨φ v, hWφ v hv, hWfix v hv⟩
  have he' : ∀ w ∈ W, (0 : ℚ) < e w := fun w hw => by exact_mod_cast he w hw
  have B₁ : ∀ v, v ∉ W → (v ∉ T₁ → 0 ≤ v.ord u₁) ∧ (v ∈ T₁ → -1 ≤ v.ord u₁) := by
    intro v hvW
    by_cases hv : φ (φ v) = v
    · exact ⟨fun _ => O2₁ v hv hvW, fun h => absurd hv (hT₁ v h)⟩
    · have h := O1₁ v hv
      constructor
      · intro hvT; rw [hEbar₁, if_neg hvT] at h; have := hEE₁ v; omega
      · intro hvT; rw [hEbar₁, if_pos hvT] at h; have := hEE₁ v; omega
  have B₂ : ∀ v, v ∉ W → (v ∉ T₂ → 0 ≤ v.ord u₂) ∧ (v ∈ T₂ → -1 ≤ v.ord u₂) := by
    intro v hvW
    by_cases hv : φ (φ v) = v
    · exact ⟨fun _ => O2₂ v hv hvW, fun h => absurd hv (hT₂ v h)⟩
    · have h := O1₂ v hv
      constructor
      · intro hvT; rw [hEbar₂, if_neg hvT] at h; have := hEE₂ v; omega
      · intro hvT; rw [hEbar₂, if_pos hvT] at h; have := hEE₂ v; omega

  have hi : ¬ 0 < δ := by
    intro hlt
    have hpos : ∀ w ∈ W, 1 ≤ w.ord u₁ := fun w hw => by
      have h1 := A₁ w hw
      have h2 : (0 : ℚ) < (e w : ℚ) * ((w.ord u₁ : ℤ) : ℚ) := lt_of_lt_of_le hlt h1
      have h3 : (0 : ℚ) < ((w.ord u₁ : ℤ) : ℚ) := (pos_iff_pos_of_mul_pos h2).mp (he' w hw)
      have h4 : (0 : ℤ) < w.ord u₁ := by exact_mod_cast h3
      omega
    have hb : ∀ v, v ∉ T₁ → 0 ≤ v.ord u₁ := fun v hvT => by
      by_cases hvW : v ∈ W
      · exact le_trans (by norm_num) (hpos v hvW)
      · exact (B₁ v hvW).1 hvT
    have hb' : ∀ v ∈ T₁, -1 ≤ v.ord u₁ := fun v hvT => (B₁ v (fun h => hWT₁ v h hvT)).2 hvT
    have hz : ∀ w ∈ W, w.HasValue u₁ 0 := fun w hw =>
      hasValue_zero_of_ord_pos w hu₁ (by have := hpos w hw; omega)
    exact hu₁ (hgp₁ u₁ hb hb' hz)

  have hii : ¬ δ < 0 := by
    intro hlt
    have hpos : ∀ w ∈ W, 1 ≤ (φ w).ord u₂ := fun w hw => by
      have h1 := A₂ w hw
      have h2 : -((e w : ℚ) * (((φ w).ord u₂ : ℤ) : ℚ)) < 0 := lt_of_le_of_lt h1 hlt
      have h3 : (0 : ℚ) < (e w : ℚ) * (((φ w).ord u₂ : ℤ) : ℚ) := by linarith
      have h4 : (0 : ℚ) < (((φ w).ord u₂ : ℤ) : ℚ) := (pos_iff_pos_of_mul_pos h3).mp (he' w hw)
      have h5 : (0 : ℤ) < (φ w).ord u₂ := by exact_mod_cast h4
      omega
    have hpos' : ∀ v ∈ W, 1 ≤ v.ord u₂ := fun v hv => by
      obtain ⟨w, hw, rfl⟩ := hWsurj v hv; exact hpos w hw
    have hb : ∀ v, v ∉ T₂ → 0 ≤ v.ord u₂ := fun v hvT => by
      by_cases hvW : v ∈ W
      · exact le_trans (by norm_num) (hpos' v hvW)
      · exact (B₂ v hvW).1 hvT
    have hb' : ∀ v ∈ T₂, -1 ≤ v.ord u₂ := fun v hvT => (B₂ v (fun h => hWT₂ v h hvT)).2 hvT
    obtain ⟨c, hc⟩ := hgp₂ u₂ hb hb'
    obtain ⟨w₀, hw₀⟩ := hWne
    have hval0 : w₀.HasValue u₂ 0 := hasValue_zero_of_ord_pos w₀ hu₂ (by have := hpos' w₀ hw₀; omega)
    rw [hc] at hval0
    have hc0 := eq_zero_of_hasValue_algebraMap_zero w₀ hval0
    apply hu₂; rw [hc, hc0, map_zero]
  have hδ : δ = 0 := le_antisymm (not_lt.mp hi) (not_lt.mp hii)

  have hn₁ : ∀ w ∈ W, 0 ≤ w.ord u₁ := fun w hw => by
    have h1 := A₁ w hw; rw [hδ] at h1
    have h2 : (0 : ℚ) ≤ ((w.ord u₁ : ℤ) : ℚ) := nonneg_of_mul_nonneg_right (by linarith) (he' w hw) |> fun h => by
      rcases (mul_nonneg_iff_of_pos_left (he' w hw)).mp h1 with h'; exact h'
    exact_mod_cast h2
  have hn₂ : ∀ w ∈ W, 0 ≤ (φ w).ord u₂ := fun w hw => by
    have h1 := A₂ w hw; rw [hδ] at h1
    have h2 : (0 : ℚ) ≤ (e w : ℚ) * (((φ w).ord u₂ : ℤ) : ℚ) := by linarith
    have h3 : (0 : ℚ) ≤ (((φ w).ord u₂ : ℤ) : ℚ) := (mul_nonneg_iff_of_pos_left (he' w hw)).mp h2
    exact_mod_cast h3
  have hn₂' : ∀ v ∈ W, 0 ≤ v.ord u₂ := fun v hv => by obtain ⟨w, hw, rfl⟩ := hWsurj v hv; exact hn₂ w hw
  have C₁ : ∀ v, v ∉ T₁ → 0 ≤ v.ord u₁ := fun v hvT => by
    by_cases hvW : v ∈ W
    · exact hn₁ v hvW
    · exact (B₁ v hvW).1 hvT
  have C₁' : ∀ v ∈ T₁, -1 ≤ v.ord u₁ := fun v hvT => (B₁ v (fun h => hWT₁ v h hvT)).2 hvT
  have C₂ : ∀ v, v ∉ T₂ → 0 ≤ v.ord u₂ := fun v hvT => by
    by_cases hvW : v ∈ W
    · exact hn₂' v hvW
    · exact (B₂ v hvW).1 hvT
  have C₂' : ∀ v ∈ T₂, -1 ≤ v.ord u₂ := fun v hvT => (B₂ v (fun h => hWT₂ v h hvT)).2 hvT

  obtain ⟨c₂, hc₂⟩ := hgp₂ u₂ C₂ C₂'
  have hc₂0 : c₂ ≠ 0 := by rintro rfl; apply hu₂; rw [hc₂, map_zero]
  have hord₂ : ∀ v : Place k F, v.ord u₂ = 0 := fun v => by
    rw [hc₂]; exact (v.hasValue_algebraMap c₂).ord_eq_zero hc₂0

  exact ⟨C₁, C₁', C₂, C₂', fun w hw => (B w hw hδ (hord₂ (φ w))).2⟩

end ChartOkA2

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve"

namespace ModularCurve p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple PlaceSpecialization.fstDiv PlaceSpecialization.sndDiv PlaceSpecialization.glueData arithmeticGalois modularFunctionFieldBar ModularPolynomialData modularFunctionFieldFull modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence nodePairsOfPlaces mem_nodePairsOfPlaces_iff ssPlaces jGeomGen jNGeomGen jNGeomGen_one IsCentreOf IsAffineGeomPlace arithFrobC PlaceSpecialization.ProlongationTuple.AnnulusDatumQ NodeLocalized.coeffSubring NodeLocalized.redRestrict PlaceSpecialization.ProlongationTuple.AnnulusDatum jWidth PlaceSpecialization.ProlongationTuple.cuspLawInfty_oneSided_levelOne PlaceSpecialization.ProlongationTuple.cuspLawZero_oneSided_levelOne PlaceSpecialization.ProlongationTuple.divisorLawFst_oneSided_levelOne PlaceSpecialization.ProlongationTuple.divisorLawSnd_oneSided_levelOne PlaceSpecialization.ProlongationTuple.regularityLawFst_oneSided_levelOne PlaceSpecialization.ProlongationTuple.regularityLawSnd_oneSided_levelOne PlaceSpecialization.exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace PlaceSpecialization.exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq PlaceSpecialization.not_fixed_reduceFst_of_isStrictSnd arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces arithFrobC_smul_eq_frobOnPlacesGeomLevel deg_eq_one_modularFunctionFieldBar essFiniteType_modularFunctionFieldFullC exists_effective_pic0Mk_sub_eq_of_genusFF_le_degree exists_eq_algebraMap_of_hasValue_smul_of_generalPosition finite_setOf_ord_jGeomGen_sub_pos frobOnPlacesGeomLevel_charLGeomPlaceOfPoint genusFF_modularFunctionFieldBar_mul_add_one_eq_of_ssPlaces isAffineGeomPlace_frobOnPlacesGeomLevel isCurveOver_modularFunctionFieldBar isCurveOver_modularFunctionFieldC_of_perfectField isSeparable_jqNModC_of_natCast_ne_zero mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq modularFunctionFieldC_eq_modularFunctionFieldFullC pow_mem_ssJSet_iff_of_perfectField ssPlaces_nonempty PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable" namespace PlaceSpecialization p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple ProlongationTuple.residue₁_apply ProlongationTuple.residue₂_apply reduceFst reduceSnd IsStrictFst IsStrictSnd IsGoodDiv fstDiv sndDiv glueData sp mk d1 ProlongationTuple.AnnulusDatumQ ProlongationTuple.AnnulusDatum ProlongationTuple.TwistVector ProlongationTuple.cuspLawInfty_oneSided_levelOne ProlongationTuple.cuspLawZero_oneSided_levelOne ProlongationTuple.divisorLawFst_oneSided_levelOne ProlongationTuple.divisorLawSnd_oneSided_levelOne ProlongationTuple.regularityLawFst_oneSided_levelOne ProlongationTuple.regularityLawSnd_oneSided_levelOne exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq not_fixed_reduceFst_of_isStrictSnd ProlongationTuple.AnnulusDatumQ.exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable" end ModularCurve.PlaceSpecialization
p2m_open_scoped "ModularCurve ModularCurve.PlaceSpecialization" in
theorem ModularCurve.PlaceSpecialization.mapDomain_fstDiv_eq_and_mapDomain_sndDiv_eq_of_reducedPair
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k 1)))
    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    {T₁ T₂ : Finset (Place k ↥(modularFunctionFieldC k 1))}
    (hgp₁ : ∀ h : ↥(modularFunctionFieldC k 1),
      (∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
      (∀ w ∈ W, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : ↥(modularFunctionFieldC k 1),
      (∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
      ∃ c : k, h = algebraMap k ↥(modularFunctionFieldC k 1) c)
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))

    (u₁ u₂ : ↥(modularFunctionFieldC k 1)) (hu₁0 : u₁ ≠ 0) (hu₂0 : u₂ ≠ 0)
    (hh₁ : ∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₁ → 0 ≤ v.ord u₁) (hh₁' : ∀ v ∈ T₁, -1 ≤ v.ord u₁)
    (hh₂ : ∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₂ → 0 ≤ v.ord u₂) (hh₂' : ∀ v ∈ T₂, -1 ≤ v.ord u₂)
    (hval : ∀ w ∈ W, ∃ c : k, w.HasValue u₁ c ∧ (arithFrobC q k 1 • w).HasValue u₂ c)
    (hlink₁ : ∀ v : Place k ↥(modularFunctionFieldC k 1),
      frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) ≠ v →
      v.ord u₁ = Finsupp.mapDomain P.reduceFst (P.fstDiv E) v
        - Finsupp.mapDomain P.reduceFst (∑ i, Finsupp.single (Q₁ i) (1 : ℤ)) v)
    (hlink₂ : ∀ v : Place k ↥(modularFunctionFieldC k 1),
      frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) ≠ v →
      v.ord u₂ = Finsupp.mapDomain P.reduceSnd (P.sndDiv E) v
        - Finsupp.mapDomain P.reduceSnd (∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) v) :
    Finsupp.mapDomain P.reduceFst (P.fstDiv E) = ∑ i, Finsupp.single (P.reduceFst (Q₁ i)) (1 : ℤ) ∧
    Finsupp.mapDomain P.reduceSnd (P.sndDiv E) = ∑ j, Finsupp.single (P.reduceSnd (Q₂ j)) (1 : ℤ) := by
  classical
  set φ := frobOnPlacesGeomLevel k 1 data hKr with hφ

  obtain ⟨c, hc₁, hc₂⟩ := ModularCurve.exists_eq_algebraMap_of_hasValue_smul_of_generalPosition
    (arithFrobC q k 1) W T₁ T₂ hgp₁ hgp₂ u₁ u₂ hh₁ hh₁' hh₂ hh₂' hval
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hu₁0 (by rw [hc₁, map_zero])
  have hordu₁ : ∀ v : Place k ↥(modularFunctionFieldC k 1), v.ord u₁ = 0 := fun v => by
    rw [hc₁]; exact (v.hasValue_algebraMap c).ord_eq_zero hc0
  have hordu₂ : ∀ v : Place k ↥(modularFunctionFieldC k 1), v.ord u₂ = 0 := fun v => by
    rw [hc₂]; exact (v.hasValue_algebraMap c).ord_eq_zero hc0

  have mapDomain_apply_eq_sum : ∀ (g : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) →
        Place k ↥(modularFunctionFieldC k 1)) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (v),
      Finsupp.mapDomain g D v = ∑ V ∈ D.support, if g V = v then D V else 0 := by
    intro g D v
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun V _ => ?_
    rw [Finsupp.single_apply]

  have hbase₁ : Finsupp.mapDomain P.reduceFst (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) :
      Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) =
      ∑ i, Finsupp.single (P.reduceFst (Q₁ i)) (1 : ℤ) := by
    rw [Finsupp.mapDomain_finset_sum]; simp only [Finsupp.mapDomain_single]
  have hbase₂ : Finsupp.mapDomain P.reduceSnd (∑ j, Finsupp.single (Q₂ j) (1 : ℤ) :
      Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) =
      ∑ j, Finsupp.single (P.reduceSnd (Q₂ j)) (1 : ℤ) := by
    rw [Finsupp.mapDomain_finset_sum]; simp only [Finsupp.mapDomain_single]
  refine ⟨?_, ?_⟩
  · ext v
    by_cases hv : φ (φ v) = v
    ·
      have lhs : Finsupp.mapDomain P.reduceFst (P.fstDiv E) v = 0 := by
        rw [mapDomain_apply_eq_sum]
        refine Finset.sum_eq_zero fun V hV => ?_
        rw [if_neg]
        rintro rfl
        rw [ModularCurve.PlaceSpecialization.fstDiv, Finsupp.support_filter, Finset.mem_filter] at hV
        exact hV.2.2 hv
      have rhs : (∑ i, Finsupp.single (P.reduceFst (Q₁ i)) (1 : ℤ)) v = 0 := by
        rw [Finsupp.finset_sum_apply]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [Finsupp.single_apply, if_neg]
        rintro rfl
        exact (hQ₁ i).2 hv
      rw [lhs, rhs]
    · have h := hlink₁ v hv
      rw [hordu₁ v, hbase₁] at h
      omega
  · ext v
    by_cases hv : φ (φ v) = v
    · have lhs : Finsupp.mapDomain P.reduceSnd (P.sndDiv E) v = 0 := by
        rw [mapDomain_apply_eq_sum]
        refine Finset.sum_eq_zero fun V hV => ?_
        rw [if_neg]
        rintro rfl
        rw [ModularCurve.PlaceSpecialization.sndDiv, Finsupp.support_filter, Finset.mem_filter] at hV
        exact hV.2.2 hv
      have rhs : (∑ j, Finsupp.single (P.reduceSnd (Q₂ j)) (1 : ℤ)) v = 0 := by
        rw [Finsupp.finset_sum_apply]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [Finsupp.single_apply, if_neg]
        rintro rfl
        exact (hQ₂ j).2 hv
      rw [lhs, rhs]
    · have h := hlink₂ v hv
      rw [hordu₂ v, hbase₂] at h
      omega

namespace ChartOkO4

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve"
open Classical

set_option autoImplicit false

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_zpow' (v : Place K F) (f : F) (n : ℤ) : v.ord (f ^ n) = n * v.ord f := v.ord_zpow f n

theorem ord_prod_zpow {ι : Type*} (v : Place K F) (s : Finset ι) (f : ι → F) (n : ι → ℤ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    v.ord (∏ i ∈ s, f i ^ n i) = ∑ i ∈ s, n i * v.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Place.ord_one]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    have hfi : f i ≠ 0 := hf i (Finset.mem_insert_self i s)
    have hrest : ∀ j ∈ s, f j ≠ 0 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hprod : ∏ j ∈ s, f j ^ n j ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j hj => zpow_ne_zero _ (hrest j hj)
    rw [v.ord_mul (zpow_ne_zero _ hfi) hprod, v.ord_zpow, ih hrest]

theorem ord_mul_mul_prod_zpow {ι : Type*} (v : Place K F) (ρ g : F) (hρ : ρ ≠ 0) (hg : g ≠ 0)
    (s : Finset ι) (f : ι → F) (n : ι → ℤ) (hf : ∀ i ∈ s, f i ≠ 0) :
    v.ord (ρ * g * ∏ i ∈ s, f i ^ n i) = v.ord ρ + v.ord g + ∑ i ∈ s, n i * v.ord (f i) := by
  have hprod : ∏ i ∈ s, f i ^ n i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i hi => zpow_ne_zero _ (hf i hi)
  rw [v.ord_mul (mul_ne_zero hρ hg) hprod, v.ord_mul hρ hg, ord_prod_zpow v s f n hf]

theorem sum_mul_ord_unif (W : Finset (Place K F)) (f : Place K F → F) (n : Place K F → ℤ)
    (w : Place K F) (hw : w ∈ W)
    (hunif : ∀ w' ∈ W, w.ord (f w') = if w' = w then 1 else 0) :
    ∑ w' ∈ W, n w' * w.ord (f w') = n w := by
  classical
  rw [Finset.sum_eq_single_of_mem w hw]
  · rw [hunif w hw, if_pos rfl, mul_one]
  · intro w' hw' hne
    rw [hunif w' hw', if_neg hne, mul_zero]

theorem ord_corrected_eq (W : Finset (Place K F)) (ρ g : F) (hρ : ρ ≠ 0) (hg : g ≠ 0)
    (f : Place K F → F) (n : Place K F → ℤ) (hf : ∀ w' ∈ W, f w' ≠ 0)
    (w : Place K F) (hw : w ∈ W) (hgw : w.ord g = 0)
    (hunif : ∀ w' ∈ W, w.ord (f w') = if w' = w then 1 else 0)
    (s_o : ℤ) (hEND : w.ord ρ = s_o) :
    w.ord (ρ * g * ∏ w' ∈ W, f w' ^ n w') = s_o + n w := by
  rw [ord_mul_mul_prod_zpow w ρ g hρ hg W f n hf, sum_mul_ord_unif W f n w hw hunif, hEND, hgw, add_zero]

end ChartOkO4

namespace ChartOkO4

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve"
open Classical

set_option autoImplicit false

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem sum_mul_ord_unif' (W : Finset (Place K F)) (f : Place K F → F) (n : Place K F → ℤ)
    (v : Place K F) (w : Place K F) (hw : w ∈ W)
    (hunif : ∀ w' ∈ W, v.ord (f w') = if w' = w then 1 else 0) :
    ∑ w' ∈ W, n w' * v.ord (f w') = n w := by
  rw [Finset.sum_eq_single_of_mem w hw]
  · rw [hunif w hw, if_pos rfl, mul_one]
  · intro w' hw' hne
    rw [hunif w' hw', if_neg hne, mul_zero]

theorem ord_corrected_eq' (W : Finset (Place K F)) (ρ g : F) (hρ : ρ ≠ 0) (hg : g ≠ 0)
    (f : Place K F → F) (n : Place K F → ℤ) (hf : ∀ w' ∈ W, f w' ≠ 0)
    (v : Place K F) (w : Place K F) (hw : w ∈ W) (hgv : v.ord g = 0)
    (hunif : ∀ w' ∈ W, v.ord (f w') = if w' = w then 1 else 0)
    (s_o : ℤ) (hEND : v.ord ρ = s_o) :
    v.ord (ρ * g * ∏ w' ∈ W, f w' ^ n w') = s_o + n w := by
  rw [ord_mul_mul_prod_zpow v ρ g hρ hg W f n hf, sum_mul_ord_unif' W f n v w hw hunif, hEND, hgv, add_zero]

end ChartOkO4

namespace ChartOkO4

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve"
open Classical

set_option autoImplicit false

theorem mapDomain_apply_eq_zero_of_forall_ne {α β : Type*} (E : α →₀ ℤ) (r : α → β) (b : β)
    (h : ∀ a ∈ E.support, r a ≠ b) : Finsupp.mapDomain r E b = 0 := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun a ha => ?_
  rw [Finsupp.single_apply, if_neg (h a ha)]

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
  {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

theorem mapDomain_reduceFst_fstDiv_apply_eq_zero_of_fixed
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (w : Place k ↥(modularFunctionFieldC k N))
    (hw : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w) :
    Finsupp.mapDomain P.reduceFst (P.fstDiv D) w = 0 := by
  apply mapDomain_apply_eq_zero_of_forall_ne
  intro V hV hVw
  have hmem : V ∈ (D.filter P.IsStrictFst).support := hV
  rw [Finsupp.support_filter, Finset.mem_filter] at hmem
  exact hmem.2.2 (by rw [hVw]; exact hw)

theorem mapDomain_reduceSnd_sndDiv_apply_eq_zero_of_fixed
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (w : Place k ↥(modularFunctionFieldC k N))
    (hw : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w) :
    Finsupp.mapDomain P.reduceSnd (P.sndDiv D) w = 0 := by
  apply mapDomain_apply_eq_zero_of_forall_ne
  intro V hV hVw
  have hmem : V ∈ (D.filter P.IsStrictSnd).support := hV
  rw [Finsupp.support_filter, Finset.mem_filter] at hmem
  exact hmem.2.2 (by rw [hVw]; exact hw)

theorem ord_eq_zero_of_div_eq_mapDomain_sub_smul_single
    (Dbar : (Place k ↥(modularFunctionFieldC k N)) →₀ ℤ) (m : ℤ)
    (cusp w : Place k ↥(modularFunctionFieldC k N)) (g : ↥(modularFunctionFieldC k N))
    (hdiv : ∀ v : Place k ↥(modularFunctionFieldC k N),
      (Dbar - m • Finsupp.single cusp 1 : (Place k ↥(modularFunctionFieldC k N)) →₀ ℤ) v = v.ord g)
    (hDbar : Dbar w = 0) (hwc : w ≠ cusp) :
    w.ord g = 0 := by
  rw [← hdiv w, Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_apply, if_neg hwc.symm, hDbar]
  simp

end ChartOkO4

namespace ChartOkO4

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve"
open Classical

set_option autoImplicit false

section Unif
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ne_zero_of_ord_ne_zero {v : Place K F} {g : F} (h : v.ord g ≠ 0) : g ≠ 0 := by
  rintro rfl; exact h (Place.ord_zero v)

theorem prod_zpow_ne_zero (W : Finset (Place K F)) (f : Place K F → F) (n : Place K F → ℤ)
    (hf : ∀ w ∈ W, f w ≠ 0) : ∏ w ∈ W, f w ^ n w ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun w hw => zpow_ne_zero _ (hf w hw)

theorem unifFst_facts (W : Finset (Place K F)) (cusp : Place K F) (hcusp : cusp ∉ W)
    (π : Place K F → F)
    (hunif : ∀ w' ∈ W, ∀ v : Place K F,
      v.ord (π w') = (Finsupp.single w' 1 - Finsupp.single cusp 1 : Place K F →₀ ℤ) v) :
    (∀ w' ∈ W, π w' ≠ 0) ∧
    (∀ w ∈ W, ∀ w' ∈ W, w.ord (π w') = if w' = w then 1 else 0) := by
  refine ⟨fun w' hw' => ne_zero_of_ord_ne_zero (v := w') ?_, fun w hw w' hw' => ?_⟩
  · rw [hunif w' hw' w', Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply, if_pos rfl,
      if_neg (fun h : cusp = w' => hcusp (by rw [h]; exact hw'))]
    norm_num
  · rw [hunif w' hw' w, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply,
      if_neg (fun h : cusp = w => hcusp (by rw [h]; exact hw))]
    simp

theorem unifSnd_facts (W : Finset (Place K F)) (cusp : Place K F) (hcusp : cusp ∉ W)
    (φ : Place K F → Place K F) (hφ : Function.Injective φ) (hφcusp : φ cusp = cusp)
    (π' : Place K F → F)
    (hunif : ∀ w' ∈ W, ∀ v : Place K F,
      v.ord (π' w') = (Finsupp.single (φ w') 1 - Finsupp.single cusp 1 : Place K F →₀ ℤ) v) :
    (∀ w' ∈ W, π' w' ≠ 0) ∧
    (∀ w ∈ W, ∀ w' ∈ W, (φ w).ord (π' w') = if w' = w then 1 else 0) := by
  have hne : ∀ w ∈ W, cusp ≠ φ w := by
    intro w hw h
    have : φ cusp = φ w := by rw [hφcusp]; exact h
    exact hcusp (hφ this ▸ hw)
  refine ⟨fun w' hw' => ne_zero_of_ord_ne_zero (v := φ w') ?_, fun w hw w' hw' => ?_⟩
  · rw [hunif w' hw' (φ w'), Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply, if_pos rfl,
      if_neg (hne w' hw')]
    norm_num
  · rw [hunif w' hw' (φ w), Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply, if_neg (hne w hw)]
    by_cases h : w' = w
    · subst h; simp
    · rw [if_neg (fun h' => h (hφ h')), if_neg h]; simp

end Unif

section Effective
variable {α β : Type*}

theorem mapDomain_apply_nonneg (E : α →₀ ℤ) (r : α → β) (hE : ∀ a, 0 ≤ E a) (b : β) :
    0 ≤ Finsupp.mapDomain r E b := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  exact Finset.sum_nonneg fun a _ => by
    rw [Finsupp.single_apply]; split_ifs <;> [exact hE a; exact le_rfl]

theorem filter_apply_nonneg (E : α →₀ ℤ) (p : α → Prop) [DecidablePred p] (hE : ∀ a, 0 ≤ E a) (a : α) :
    0 ≤ (E.filter p) a := by
  rw [Finsupp.filter_apply]; split_ifs <;> [exact hE a; exact le_rfl]

end Effective

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
  {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

theorem mapDomain_fstDiv_nonneg (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hE : 0 ≤ E)
    (v : Place k ↥(modularFunctionFieldC k N)) :
    0 ≤ Finsupp.mapDomain P.reduceFst (P.fstDiv E) v :=
  mapDomain_apply_nonneg _ _ (fun V => filter_apply_nonneg E _ (fun W => by simpa using Finsupp.le_def.mp hE W) V) v

theorem mapDomain_sndDiv_nonneg (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hE : 0 ≤ E)
    (v : Place k ↥(modularFunctionFieldC k N)) :
    0 ≤ Finsupp.mapDomain P.reduceSnd (P.sndDiv E) v :=
  mapDomain_apply_nonneg _ _ (fun V => filter_apply_nonneg E _ (fun W => by simpa using Finsupp.le_def.mp hE W) V) v

end ChartOkO4

namespace ChartOkO4

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve"
open Classical

set_option autoImplicit false

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem unifFst_facts' (W : Finset (Place K F)) (cusp : Place K F) (hcusp : cusp ∉ W)
    (π : Place K F → F)
    (hunif : ∀ w' ∈ W, ∀ v : Place K F,
      v.ord (π w') = (if v = w' then 1 else 0) - (if v = cusp then 1 else 0)) :
    (∀ w' ∈ W, π w' ≠ 0) ∧
    (∀ w ∈ W, ∀ w' ∈ W, w.ord (π w') = if w' = w then 1 else 0) := by
  refine ⟨fun w' hw' => ne_zero_of_ord_ne_zero (v := w') ?_, fun w hw w' hw' => ?_⟩
  · rw [hunif w' hw' w', if_pos rfl, if_neg (fun h : w' = cusp => hcusp (h ▸ hw'))]
    norm_num
  · rw [hunif w' hw' w, if_neg (fun h : w = cusp => hcusp (h ▸ hw))]
    by_cases h : w' = w
    · subst h; simp
    · rw [if_neg (fun h' => h h'.symm), if_neg h]; simp

theorem unifSnd_facts' (W : Finset (Place K F)) (cusp : Place K F) (hcusp : cusp ∉ W)
    (φ : Place K F → Place K F) (hφ : Function.Injective φ) (hφcusp : φ cusp = cusp)
    (π' : Place K F → F)
    (hunif : ∀ w' ∈ W, ∀ v : Place K F,
      v.ord (π' w') = (if v = φ w' then 1 else 0) - (if v = cusp then 1 else 0)) :
    (∀ w' ∈ W, π' w' ≠ 0) ∧
    (∀ w ∈ W, ∀ w' ∈ W, (φ w).ord (π' w') = if w' = w then 1 else 0) := by
  have hne : ∀ w ∈ W, φ w ≠ cusp := by
    intro w hw h
    have : φ w = φ cusp := by rw [hφcusp]; exact h
    exact hcusp (hφ this ▸ hw)
  refine ⟨fun w' hw' => ne_zero_of_ord_ne_zero (v := φ w') ?_, fun w hw w' hw' => ?_⟩
  · rw [hunif w' hw' (φ w'), if_pos rfl, if_neg (hne w' hw')]
    norm_num
  · rw [hunif w' hw' (φ w), if_neg (hne w hw)]
    by_cases h : w' = w
    · subst h; simp
    · rw [if_neg (fun h' => h (hφ h').symm), if_neg h]; simp

end ChartOkO4

namespace ChartOkO4

open Classical

set_option autoImplicit false

theorem mapDomain_sum_single_apply {ι α β : Type*} [Fintype ι] (Q : ι → α) (r : α → β)
    (hinj : Function.Injective fun i => r (Q i)) (v : β) :
    Finsupp.mapDomain r (∑ i, Finsupp.single (Q i) (1 : ℤ)) v = if (∃ i, r (Q i) = v) then 1 else 0 := by
  rw [Finsupp.mapDomain_finset_sum]
  simp only [Finsupp.mapDomain_single, Finsupp.finset_sum_apply, Finsupp.single_apply]
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single i]
    · rw [if_pos hi]
    · intro j _ hji
      rw [if_neg]
      intro hj
      exact hji (hinj (hj.trans hi.symm))
    · intro hi'; exact absurd (Finset.mem_univ i) hi'
  · push Not at h
    exact Finset.sum_eq_zero fun i _ => if_neg (h i)

theorem mapDomain_sum_single_eq_indicator {ι α β : Type*} [Fintype ι] (Q : ι → α) (r : α → β)
    (hinj : Function.Injective fun i => r (Q i)) (T : Finset β) (hT : ∀ v, v ∈ T ↔ ∃ i, r (Q i) = v) (v : β) :
    Finsupp.mapDomain r (∑ i, Finsupp.single (Q i) (1 : ℤ)) v = if v ∈ T then 1 else 0 := by
  rw [mapDomain_sum_single_apply Q r hinj v]
  by_cases h : v ∈ T
  · rw [if_pos ((hT v).mp h), if_pos h]
  · rw [if_neg (fun h' => h ((hT v).mpr h')), if_neg h]

end ChartOkO4

namespace ChartOkO4

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve.PlaceSpecialization.ProlongationTuple"
open Classical

set_option autoImplicit false

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ} {R : ProlongationTuple P}
  {W : Finset (Place k ↥(modularFunctionFieldC k 1))}

theorem chainVal_mk_eq (dat : R.AnnulusDatumQ W) (γ : Place k ↥(modularFunctionFieldC k 1) → ℕ → ℤ) (oZ oZ' : ℤ)
    (w : Place k ↥(modularFunctionFieldC k 1))
    (h0 : γ w 0 = oZ) (h1 : ∀ d : ℕ, dat.width w ≤ d → γ w d = oZ') (d : ℕ) :
    dat.chainVal (⟨oZ, oZ', γ⟩ : TwistVector (k := k) W) w d = γ w d := by
  unfold AnnulusDatumQ.chainVal
  split_ifs with hd hwd
  · rw [hd, h0]
  · rw [h1 d hwd]
  · rfl

theorem O4O5_of_profile (dat : R.AnnulusDatumQ W)
    (φ : Place k ↥(modularFunctionFieldC k 1) → Place k ↥(modularFunctionFieldC k 1))
    (a : TwistVector (k := k) W)
    (u₁ u₂ ρ₁ ρ₂ g₁ g₂ : ↥(modularFunctionFieldC k 1))
    (hu₁ : u₁ = ρ₁ * g₁ * ∏ w ∈ W, dat.unifFst w ^ dat.endSlopeFst a w)
    (hu₂ : u₂ = ρ₂ * g₂ * ∏ w ∈ W, dat.unifSnd w ^ dat.endSlopeSnd a w)
    (hρ₁ : ρ₁ ≠ 0) (hρ₂ : ρ₂ ≠ 0) (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    (hπ₁ : ∀ w ∈ W, dat.unifFst w ≠ 0) (hπ₂ : ∀ w ∈ W, dat.unifSnd w ≠ 0)
    (hgw₁ : ∀ w ∈ W, w.ord g₁ = 0) (hgw₂ : ∀ w ∈ W, (φ w).ord g₂ = 0)
    (hunif₁ : ∀ w ∈ W, ∀ w' ∈ W, w.ord (dat.unifFst w') = if w' = w then 1 else 0)
    (hunif₂ : ∀ w ∈ W, ∀ w' ∈ W, (φ w).ord (dat.unifSnd w') = if w' = w then 1 else 0)
    (γ : Place k ↥(modularFunctionFieldC k 1) → ℕ → ℤ) (oZ oZ' : ℤ)
    (hends0 : ∀ w ∈ W, γ w 0 = oZ) (hends1 : ∀ w ∈ W, ∀ d : ℕ, dat.width w ≤ d → γ w d = oZ')
    (hconcγ : ∀ w ∈ W, ∀ d : ℕ, 1 ≤ d → d + 1 ≤ dat.width w →
      γ w (d + 1) + dat.chainVal a w (d + 1) - (γ w d + dat.chainVal a w d) ≤
        (γ w d + dat.chainVal a w d) - (γ w (d - 1) + dat.chainVal a w (d - 1)))
    (hEND₁ : ∀ w ∈ W, w.ord ρ₁ = γ w 1 - γ w 0)
    (hEND₂ : ∀ w ∈ W, (φ w).ord ρ₂ = γ w (dat.width w - 1) - γ w (dat.width w)) :
    ∃ o : TwistVector (k := k) W,
      (∀ w ∈ W, ∀ d : ℕ, 1 ≤ d → d + 1 ≤ dat.width w →
        dat.chainVal o w (d + 1) + dat.chainVal a w (d + 1) - (dat.chainVal o w d + dat.chainVal a w d) ≤
          (dat.chainVal o w d + dat.chainVal a w d) - (dat.chainVal o w (d - 1) + dat.chainVal a w (d - 1))) ∧
      (∀ w ∈ W, w.ord u₁ = (dat.chainVal o w 1 + dat.chainVal a w 1) - (dat.chainVal o w 0 + dat.chainVal a w 0)) ∧
      (∀ w ∈ W, (φ w).ord u₂ = (dat.chainVal o w (dat.width w - 1) + dat.chainVal a w (dat.width w - 1))
        - (dat.chainVal o w (dat.width w) + dat.chainVal a w (dat.width w))) := by
  refine ⟨⟨oZ, oZ', γ⟩, ?_, ?_, ?_⟩
  · intro w hw d hd hde
    simp only [chainVal_mk_eq dat γ oZ oZ' w (hends0 w hw) (hends1 w hw)]
    exact hconcγ w hw d hd hde
  · intro w hw
    simp only [chainVal_mk_eq dat γ oZ oZ' w (hends0 w hw) (hends1 w hw)]
    rw [hu₁, ord_corrected_eq' W ρ₁ g₁ hρ₁ hg₁ dat.unifFst (dat.endSlopeFst a) hπ₁ w w hw (hgw₁ w hw) (hunif₁ w hw)
      _ (hEND₁ w hw)]
    unfold AnnulusDatumQ.endSlopeFst
    ring
  · intro w hw
    simp only [chainVal_mk_eq dat γ oZ oZ' w (hends0 w hw) (hends1 w hw)]
    rw [hu₂, ord_corrected_eq' W ρ₂ g₂ hρ₂ hg₂ dat.unifSnd (dat.endSlopeSnd a) hπ₂ (φ w) w hw (hgw₂ w hw) (hunif₂ w hw)
      _ (hEND₂ w hw)]
    unfold AnnulusDatumQ.endSlopeSnd
    ring

end ChartOkO4

namespace ChartOkO4

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve.PlaceSpecialization.ProlongationTuple"
open Classical

set_option autoImplicit false

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ} {R : ProlongationTuple P}
  {W : Finset (Place k ↥(modularFunctionFieldC k 1))}

theorem O4O5_of_profile' (dat : R.AnnulusDatumQ W)
    (φ : Place k ↥(modularFunctionFieldC k 1) → Place k ↥(modularFunctionFieldC k 1))
    (a : TwistVector (k := k) W)
    (u₁ u₂ ρ₁ ρ₂ g₁ g₂ : ↥(modularFunctionFieldC k 1))
    (hu₁ : u₁ = ρ₁ * g₁ * ∏ w ∈ W, dat.unifFst w ^ dat.endSlopeFst a w)
    (hu₂ : u₂ = ρ₂ * g₂ * ∏ w ∈ W, dat.unifSnd w ^ dat.endSlopeSnd a w)
    (hρ₁ : ρ₁ ≠ 0) (hρ₂ : ρ₂ ≠ 0) (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    (hπ₁ : ∀ w ∈ W, dat.unifFst w ≠ 0) (hπ₂ : ∀ w ∈ W, dat.unifSnd w ≠ 0)
    (hgw₁ : ∀ w ∈ W, w.ord g₁ = 0) (hgw₂ : ∀ w ∈ W, (φ w).ord g₂ = 0)
    (hunif₁ : ∀ w ∈ W, ∀ w' ∈ W, w.ord (dat.unifFst w') = if w' = w then 1 else 0)
    (hunif₂ : ∀ w ∈ W, ∀ w' ∈ W, (φ w).ord (dat.unifSnd w') = if w' = w then 1 else 0)
    (γ : Place k ↥(modularFunctionFieldC k 1) → ℕ → ℤ) (oZ oZ' : ℤ)
    (hends0 : ∀ w ∈ W, γ w 0 = oZ) (hends1 : ∀ w ∈ W, ∀ d : ℕ, dat.width w ≤ d → γ w d = oZ')
    (hconcγ : ∀ w ∈ W, ∀ d : ℕ, 1 ≤ d → d + 1 ≤ dat.width w →
      γ w (d + 1) + dat.chainVal a w (d + 1) - (γ w d + dat.chainVal a w d) ≤
        (γ w d + dat.chainVal a w d) - (γ w (d - 1) + dat.chainVal a w (d - 1)))
    (hEND₁ : ∀ w ∈ W, w.ord ρ₁ = γ w 1 - γ w 0)
    (hEND₂ : ∀ w ∈ W, (φ w).ord ρ₂ = γ w (dat.width w - 1) - γ w (dat.width w)) :
    (∀ w ∈ W, ∀ d : ℕ, dat.chainVal (⟨oZ, oZ', γ⟩ : TwistVector (k := k) W) w d = γ w d) ∧
    (∀ w ∈ W, ∀ d : ℕ, 1 ≤ d → d + 1 ≤ dat.width w →
      dat.chainVal (⟨oZ, oZ', γ⟩ : TwistVector (k := k) W) w (d + 1) + dat.chainVal a w (d + 1)
        - (dat.chainVal (⟨oZ, oZ', γ⟩ : TwistVector (k := k) W) w d + dat.chainVal a w d) ≤
        (dat.chainVal (⟨oZ, oZ', γ⟩ : TwistVector (k := k) W) w d + dat.chainVal a w d)
        - (dat.chainVal (⟨oZ, oZ', γ⟩ : TwistVector (k := k) W) w (d - 1) + dat.chainVal a w (d - 1))) ∧
    (∀ w ∈ W, w.ord u₁ = (dat.chainVal (⟨oZ, oZ', γ⟩ : TwistVector (k := k) W) w 1 + dat.chainVal a w 1)
      - (dat.chainVal (⟨oZ, oZ', γ⟩ : TwistVector (k := k) W) w 0 + dat.chainVal a w 0)) ∧
    (∀ w ∈ W, (φ w).ord u₂ = (dat.chainVal (⟨oZ, oZ', γ⟩ : TwistVector (k := k) W) w (dat.width w - 1)
        + dat.chainVal a w (dat.width w - 1))
      - (dat.chainVal (⟨oZ, oZ', γ⟩ : TwistVector (k := k) W) w (dat.width w) + dat.chainVal a w (dat.width w))) := by
  refine ⟨fun w hw d => chainVal_mk_eq dat γ oZ oZ' w (hends0 w hw) (hends1 w hw) d, ?_, ?_, ?_⟩
  · intro w hw d hd hde
    simp only [chainVal_mk_eq dat γ oZ oZ' w (hends0 w hw) (hends1 w hw)]
    exact hconcγ w hw d hd hde
  · intro w hw
    simp only [chainVal_mk_eq dat γ oZ oZ' w (hends0 w hw) (hends1 w hw)]
    rw [hu₁, ord_corrected_eq' W ρ₁ g₁ hρ₁ hg₁ dat.unifFst (dat.endSlopeFst a) hπ₁ w w hw (hgw₁ w hw) (hunif₁ w hw)
      _ (hEND₁ w hw)]
    unfold AnnulusDatumQ.endSlopeFst
    ring
  · intro w hw
    simp only [chainVal_mk_eq dat γ oZ oZ' w (hends0 w hw) (hends1 w hw)]
    rw [hu₂, ord_corrected_eq' W ρ₂ g₂ hρ₂ hg₂ dat.unifSnd (dat.endSlopeSnd a) hπ₂ (φ w) w hw (hgw₂ w hw) (hunif₂ w hw)
      _ (hEND₂ w hw)]
    unfold AnnulusDatumQ.endSlopeSnd
    ring

end ChartOkO4

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "GluingData GluingData.admissible GluingData.IsGluedPrincipal GluedPic0 GluedPic0.mk GluedPic0.mk_eq_zero_iff Place Place.ord Place.ord_zero Place.ord_one Place.ord_mul Divisor Divisor.degree Divisor.degree_single Divisor.degZero Divisor.mem_degZero Divisor.principal HasPrincipalDivisors Pic0 Pic0.mk HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed H1 genusFF constantsAreBase_of_deg_eq_one ConstantsAreBase exists_weilCanonical_riemannRoch genus"
namespace Place
p2m_export "AlgebraicCurve.Place" "HasValue hasValue_algebraMap ext ord ord_zero ord_one ord_mul ord_coe_unit ord_zpow algebraMap_mem' toValuationSubring mk mem_of_ord_nonneg evalAt"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"
set_option autoImplicit false
private theorem _root_.AlgebraicCurve.Place.ord_algebraMap_mul'' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {c : K} (hc : c ≠ 0) (g : F) : v.ord (algebraMap K F c * g) = v.ord g := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [mul_zero]
  · rw [v.ord_mul ((map_ne_zero _).mpr hc) hg]
    have hu : IsUnit (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) :=
      (v.hasValue_algebraMap c).isUnit hc
    have h0 := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at h0
    change v.ord (algebraMap K F c) = 0 at h0
    rw [h0, zero_add]
p2m_export "AlgebraicCurve.Place" "ord_algebraMap_mul''"
end AlgebraicCurve.Place

namespace ChartOkO4

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve.PlaceSpecialization"
open Classical

set_option autoImplicit false

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

theorem fstDiv_baseDivisor (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {d₁ d₂ : ℕ} (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j)) :
    P.fstDiv (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
      = ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) := by
  unfold PlaceSpecialization.fstDiv
  rw [Finsupp.filter_add]
  have h1 : (∑ i, Finsupp.single (Q₁ i) (1 : ℤ)).filter P.IsStrictFst = ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) := by
    rw [Finsupp.filter_eq_self_iff]
    intro V hV
    rw [Finsupp.finset_sum_apply] at hV
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hV
    rw [Finsupp.single_apply] at hi
    split_ifs at hi with h
    · rw [← h]; exact hQ₁ i
    · exact absurd rfl hi
  have h2 : (∑ j, Finsupp.single (Q₂ j) (1 : ℤ)).filter P.IsStrictFst = 0 := by
    rw [Finsupp.filter_eq_zero_iff]
    intro V hV
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    rw [← h] at hV

    apply hV.2
    have e1 : frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst (Q₂ j)) = P.reduceSnd (Q₂ j) := hV.1
    have e2 : P.reduceFst (Q₂ j) = frobOnPlacesGeomLevel k 1 data hKr (P.reduceSnd (Q₂ j)) := (hQ₂ j).1
    conv_rhs => rw [e2]
    rw [e1]
  rw [h1, h2, add_zero]

theorem sndDiv_baseDivisor (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {d₁ d₂ : ℕ} (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j)) :
    P.sndDiv (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
      = ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) := by
  unfold PlaceSpecialization.sndDiv
  rw [Finsupp.filter_add]
  have h1 : (∑ i, Finsupp.single (Q₁ i) (1 : ℤ)).filter P.IsStrictSnd = 0 := by
    rw [Finsupp.filter_eq_zero_iff]
    intro V hV
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    rw [← h] at hV
    apply (hQ₁ i).2
    have e1 : frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst (Q₁ i)) = P.reduceSnd (Q₁ i) := (hQ₁ i).1
    have e2 : P.reduceFst (Q₁ i) = frobOnPlacesGeomLevel k 1 data hKr (P.reduceSnd (Q₁ i)) := hV.1
    conv_rhs => rw [e2]
    rw [e1]
  have h2 : (∑ j, Finsupp.single (Q₂ j) (1 : ℤ)).filter P.IsStrictSnd = ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) := by
    rw [Finsupp.filter_eq_self_iff]
    intro V hV
    rw [Finsupp.finset_sum_apply] at hV
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hV
    rw [Finsupp.single_apply] at hj
    split_ifs at hj with h
    · rw [← h]; exact hQ₂ j
    · exact absurd rfl hj
  rw [h1, h2, zero_add]

theorem O1_fst (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (R : ProlongationTuple P) (hR : R.IsModel)
    (W : Finset (Place k ↥(modularFunctionFieldC k 1)))
    (hWfix : ∀ w ∈ W, frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr w) = w)
    (cusp : Place k ↥(modularFunctionFieldC k 1))
    (hcuspfix : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr cusp) = cusp)
    {d₁ d₂ : ℕ} (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (T₁ : Finset (Place k ↥(modularFunctionFieldC k 1)))
    (hEbar₁eq : ∀ v, Finsupp.mapDomain P.reduceFst (∑ i, Finsupp.single (Q₁ i) (1 : ℤ)) v = if v ∈ T₁ then 1 else 0)
    (D E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (f : ↥(modularFunctionFieldBar (1 * q))) (c₁ : AlgebraicClosure ℚ)
    (h₁ : c₁ • f ∈ R.R₁.integers) (hr₁ : R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0)
    (hdivf : ∀ V, (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - D) V = V.ord f)
    (g₁ : ↥(modularFunctionFieldC k 1)) (m : ℤ)
    (hdivg₁ : ∀ v : Place k ↥(modularFunctionFieldC k 1),
      (Finsupp.mapDomain P.reduceFst (P.fstDiv D) - m • Finsupp.single cusp 1 :
        Place k ↥(modularFunctionFieldC k 1) →₀ ℤ) v = v.ord g₁)
    (π : Place k ↥(modularFunctionFieldC k 1) → ↥(modularFunctionFieldC k 1))
    (n : Place k ↥(modularFunctionFieldC k 1) → ℤ)
    (hunif : ∀ w' ∈ W, ∀ v : Place k ↥(modularFunctionFieldC k 1),
      v.ord (π w') = (if v = w' then 1 else 0) - (if v = cusp then 1 else 0))
    (hπ0 : ∀ w ∈ W, π w ≠ 0) (hg₁0 : g₁ ≠ 0)
    (ρ₁ u₁ : ↥(modularFunctionFieldC k 1)) (hρ₁ : ρ₁ = R.residue₁ ⟨c₁ • f, h₁⟩)
    (hu₁ : u₁ = ρ₁ * g₁ * ∏ w ∈ W, π w ^ n w) :
    ∀ v : Place k ↥(modularFunctionFieldC k 1),
      frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) ≠ v →
      v.ord u₁ = Finsupp.mapDomain P.reduceFst (P.fstDiv E) v - (if v ∈ T₁ then 1 else 0) := by
  intro v hv

  have hρ₁0 : ρ₁ ≠ 0 := by
    rw [hρ₁, ProlongationTuple.residue₁_apply]; exact (map_ne_zero R.ι).mpr hr₁
  have hc₁ : c₁ ≠ 0 := R.R₁.smul_const_ne_zero h₁ hr₁
  have hdivf' : ∀ V, (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - D) V
      = V.ord (c₁ • f) := by
    intro V
    rw [hdivf V, Algebra.smul_def, V.ord_algebraMap_mul'' hc₁]

  have hlaw := ProlongationTuple.divisorLawFst_oneSided_levelOne P R hR (c₁ • f) h₁ hr₁ _ hdivf' v hv

  have hordρ : v.ord ρ₁ = Finsupp.mapDomain P.reduceFst (P.fstDiv E) v - (if v ∈ T₁ then 1 else 0)
      - Finsupp.mapDomain P.reduceFst (P.fstDiv D) v := by
    rw [hρ₁, ← hlaw]
    change Finsupp.mapDomain P.reduceFst (P.fstDiv (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ)
      + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - D)) v = _
    unfold PlaceSpecialization.fstDiv
    rw [Finsupp.filter_sub, Finsupp.filter_sub, Finsupp.mapDomain_sub, Finsupp.mapDomain_sub, Finsupp.sub_apply,
      Finsupp.sub_apply]
    have hb := fstDiv_baseDivisor P Q₁ Q₂ hQ₁ hQ₂
    unfold PlaceSpecialization.fstDiv at hb
    rw [hb, hEbar₁eq v]

  have hvc : v ≠ cusp := by rintro rfl; exact hv hcuspfix
  have hordg : v.ord g₁ = Finsupp.mapDomain P.reduceFst (P.fstDiv D) v := by
    rw [← hdivg₁ v, Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hvc)]
    simp

  have hordπ : ∑ w ∈ W, n w * v.ord (π w) = 0 := by
    refine Finset.sum_eq_zero fun w hw => ?_
    have hvw : v ≠ w := by rintro rfl; exact hv (hWfix v hw)
    rw [hunif w hw v, if_neg hvw, if_neg hvc]; simp
  rw [hu₁, ord_mul_mul_prod_zpow v ρ₁ g₁ hρ₁0 hg₁0 W π n hπ0, hordρ, hordg, hordπ]
  ring

theorem O1_snd (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (R : ProlongationTuple P) (hR : R.IsModel)
    (W : Finset (Place k ↥(modularFunctionFieldC k 1)))
    (hWfix : ∀ w ∈ W, frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr w) = w)
    (cusp : Place k ↥(modularFunctionFieldC k 1))
    (hcuspfix : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr cusp) = cusp)
    {d₁ d₂ : ℕ} (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (T₂ : Finset (Place k ↥(modularFunctionFieldC k 1)))
    (hEbar₂eq : ∀ v, Finsupp.mapDomain P.reduceSnd (∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) v = if v ∈ T₂ then 1 else 0)
    (D E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (f : ↥(modularFunctionFieldBar (1 * q))) (c₂ : AlgebraicClosure ℚ)
    (h₂ : c₂ • f ∈ R.R₂.integers) (hr₂ : R.R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0)
    (hdivf : ∀ V, (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - D) V = V.ord f)
    (g₂ : ↥(modularFunctionFieldC k 1)) (m : ℤ)
    (hdivg₂ : ∀ v : Place k ↥(modularFunctionFieldC k 1),
      (Finsupp.mapDomain P.reduceSnd (P.sndDiv D) - m • Finsupp.single cusp 1 :
        Place k ↥(modularFunctionFieldC k 1) →₀ ℤ) v = v.ord g₂)
    (π : Place k ↥(modularFunctionFieldC k 1) → ↥(modularFunctionFieldC k 1))
    (n : Place k ↥(modularFunctionFieldC k 1) → ℤ)
    (hunif : ∀ w' ∈ W, ∀ v : Place k ↥(modularFunctionFieldC k 1),
      v.ord (π w') = (if v = frobOnPlacesGeomLevel k 1 data hKr w' then 1 else 0) - (if v = cusp then 1 else 0))
    (hπ0 : ∀ w ∈ W, π w ≠ 0) (hg₂0 : g₂ ≠ 0)
    (ρ₂ u₂ : ↥(modularFunctionFieldC k 1)) (hρ₂ : ρ₂ = R.residue₂ ⟨c₂ • f, h₂⟩)
    (hu₂ : u₂ = ρ₂ * g₂ * ∏ w ∈ W, π w ^ n w) :
    ∀ v : Place k ↥(modularFunctionFieldC k 1),
      frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) ≠ v →
      v.ord u₂ = Finsupp.mapDomain P.reduceSnd (P.sndDiv E) v - (if v ∈ T₂ then 1 else 0) := by
  intro v hv

  have hρ₂0 : ρ₂ ≠ 0 := by
    rw [hρ₂, ProlongationTuple.residue₂_apply]; exact (map_ne_zero R.ι).mpr hr₂
  have hc₂ : c₂ ≠ 0 := R.R₂.smul_const_ne_zero h₂ hr₂
  have hdivf' : ∀ V, (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - D) V
      = V.ord (c₂ • f) := by
    intro V
    rw [hdivf V, Algebra.smul_def, V.ord_algebraMap_mul'' hc₂]

  have hlaw := ProlongationTuple.divisorLawSnd_oneSided_levelOne P R hR (c₂ • f) h₂ hr₂ _ hdivf' v hv

  have hordρ : v.ord ρ₂ = Finsupp.mapDomain P.reduceSnd (P.sndDiv E) v - (if v ∈ T₂ then 1 else 0)
      - Finsupp.mapDomain P.reduceSnd (P.sndDiv D) v := by
    rw [hρ₂, ← hlaw]
    change Finsupp.mapDomain P.reduceSnd (P.sndDiv (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ)
      + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - D)) v = _
    unfold PlaceSpecialization.sndDiv
    rw [Finsupp.filter_sub, Finsupp.filter_sub, Finsupp.mapDomain_sub, Finsupp.mapDomain_sub, Finsupp.sub_apply,
      Finsupp.sub_apply]
    have hb := sndDiv_baseDivisor P Q₁ Q₂ hQ₁ hQ₂
    unfold PlaceSpecialization.sndDiv at hb
    rw [hb, hEbar₂eq v]

  have hvc : v ≠ cusp := by rintro rfl; exact hv hcuspfix
  have hordg : v.ord g₂ = Finsupp.mapDomain P.reduceSnd (P.sndDiv D) v := by
    rw [← hdivg₂ v, Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hvc)]
    simp

  have hordπ : ∑ w ∈ W, n w * v.ord (π w) = 0 := by
    refine Finset.sum_eq_zero fun w hw => ?_
    have hvw : v ≠ frobOnPlacesGeomLevel k 1 data hKr w := by
      rintro rfl; exact hv (by rw [hWfix w hw])
    rw [hunif w hw v, if_neg hvw, if_neg hvc]; simp
  rw [hu₂, ord_mul_mul_prod_zpow v ρ₂ g₂ hρ₂0 hg₂0 W π n hπ0, hordρ, hordg, hordπ]
  ring

end ChartOkO4

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve.PlaceSpecialization.ProlongationTuple"

p2m_open_scoped "ModularCurve ModularCurve.PlaceSpecialization" in
set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in
open Classical in
theorem ModularCurve.PlaceSpecialization.chartOk_pin_harness
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {W : Finset (Place k (modularFunctionFieldC k 1))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (dat : R.AnnulusDatumQ W)
    (hcusp : dat.cusp ∉ W) (hwidth : ∀ w ∈ W, 1 ≤ dat.width w)
    (hcuspfix : frobOnPlacesGeomLevel k 1 data hKr dat.cusp = dat.cusp)
    (hunif₁ : ∀ w ∈ W, ∀ v : Place k ↥(modularFunctionFieldC k 1),
      v.ord (dat.unifFst w) = (if v = w then (1 : ℤ) else 0) - (if v = dat.cusp then (1 : ℤ) else 0))
    (hunif₂ : ∀ w ∈ W, ∀ v : Place k ↥(modularFunctionFieldC k 1),
      v.ord (dat.unifSnd w) = (if v = arithFrobC q k 1 • w then (1 : ℤ) else 0) - (if v = dat.cusp then (1 : ℤ) else 0))
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
    (hD : ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support,
      P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)
    (a : ProlongationTuple.TwistVector (k := k) W) (ha : dat.IsTwistOf a D)
    (hadm : dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
        ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W))
    (hsp : GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k 1) W)
        ⟨dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))), hadm⟩ = 0)
    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
    (hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
    {T₁ T₂ : Finset (Place k ↥(modularFunctionFieldC k 1))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v)
    (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v)
    (hT₁W : Disjoint T₁ W)
    (hT₁aff : ∀ v ∈ T₁, IsAffineGeomPlace k 1 v) (hT₂aff : ∀ v ∈ T₂, IsAffineGeomPlace k 1 v)
    (hT₁sm : ∀ v ∈ T₁, ∃ c : k × k, IsCentreOf k 1 c v ∧
      (∀ v' : Place k ↥(modularFunctionFieldC k 1), IsCentreOf k 1 c v' → v' = v) ∧
      (v.ord (jGeomGen k 1 - algebraMap k ↥(modularFunctionFieldC k 1) c.1) = 1 ∨
        v.ord (jNGeomGen k 1 - algebraMap k ↥(modularFunctionFieldC k 1) c.2) = 1))
    (hT₂sm : ∀ v ∈ T₂, ∃ c : k × k, IsCentreOf k 1 c v ∧
      (∀ v' : Place k ↥(modularFunctionFieldC k 1), IsCentreOf k 1 c v' → v' = v) ∧
      (v.ord (jGeomGen k 1 - algebraMap k ↥(modularFunctionFieldC k 1) c.1) = 1 ∨
        v.ord (jNGeomGen k 1 - algebraMap k ↥(modularFunctionFieldC k 1) c.2) = 1))
    (hT₁gen : ∀ i, (P.reduceFst (Q₁ i)).evalAt (jGeomGen k 1) ^ (q ^ 2) ≠ (P.reduceFst (Q₁ i)).evalAt (jGeomGen k 1) ∧
      (P.reduceFst (Q₁ i)).evalAt (jNGeomGen k 1) ^ (q ^ 2) ≠ (P.reduceFst (Q₁ i)).evalAt (jNGeomGen k 1))
    (hT₂gen : ∀ j, (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k 1) ^ (q ^ 2) ≠ (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k 1) ∧
      (P.reduceSnd (Q₂ j)).evalAt (jNGeomGen k 1) ^ (q ^ 2) ≠ (P.reduceSnd (Q₂ j)).evalAt (jNGeomGen k 1))
    (hgp₁ : ∀ h : ↥(modularFunctionFieldC k 1),
      (∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
      (∀ w ∈ W, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : ↥(modularFunctionFieldC k 1),
      (∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
      ∃ c : k, h = algebraMap k ↥(modularFunctionFieldC k 1) c)
    (hdeg : d₁ + d₂ = genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Qs : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hQs : P.IsStrictFst Qs)
    (hQs' : ∀ i, P.reduceFst Qs ≠ P.reduceFst (Q₁ i))
    (hQ₁I : ∀ i, ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₁ i = Q₁ i)
    (hQ₂I : ∀ j, ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₂ j = Q₂ j)
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hE0 : 0 ≤ E)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf0 : f ≠ 0)
    (hdivf : ∀ V, (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
      - (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))) V = V.ord f)

    (δ : ℚ)
    (hA₁ : ∀ (c : AlgebraicClosure ℚ) (h : c • f ∈ R.R₁.integers), R.R₁.residue ⟨c • f, h⟩ ≠ 0 →
      ∀ w ∈ W, δ ≤ (dat.width w : ℚ) * ((w.ord (R.residue₁ ⟨c • f, h⟩) : ℚ) + (dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w : ℚ)))
    (hA₂ : ∀ (c : AlgebraicClosure ℚ) (h : c • f ∈ R.R₂.integers), R.R₂.residue ⟨c • f, h⟩ ≠ 0 →
      ∀ w ∈ W, -((dat.width w : ℚ) * (((arithFrobC q k 1 • w).ord (R.residue₂ ⟨c • f, h⟩) : ℚ)
        + (dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w : ℚ))) ≤ δ)
    (hB : ∃ (c₁ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ R.R₁.integers) (c₂ : AlgebraicClosure ℚ) (h₂ : c₂ • f ∈ R.R₂.integers),
        R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0 ∧
        ∀ (g₁ g₂ : ↥(modularFunctionFieldC k 1))
          (av bv : ↥(nodePairsOfPlaces (arithFrobC q k 1) W) → kˣ),
          (∀ v, (dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))).1 v = v.ord g₁) →
          (∀ v, (dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))).2.1 v = v.ord g₂) →
          (∀ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W),
            (s : Place k ↥(modularFunctionFieldC k 1) × Place k ↥(modularFunctionFieldC k 1)).1.HasValue g₁ (av s) ∧
            (s : Place k ↥(modularFunctionFieldC k 1) × Place k ↥(modularFunctionFieldC k 1)).2.HasValue g₂ (bv s)) →
          ((dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))).2.2 = fun s => Additive.ofMul (av s / bv s)) →
          ∀ w ∈ W, δ = 0 →
            (arithFrobC q k 1 • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩) + dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w = 0 →
            (w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w = 0 ∧
             ∃ c : kˣ, w.HasValue (R.residue₁ ⟨c₁ • f, h₁⟩ * g₁ * ∏ w' ∈ W, dat.unifFst w' ^ dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w') (c : k) ∧
               (arithFrobC q k 1 • w).HasValue
                 (R.residue₂ ⟨c₂ • f, h₂⟩ * g₂ * ∏ w' ∈ W, dat.unifSnd w' ^ dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w') (c : k))) :
    Finsupp.mapDomain P.reduceFst (P.fstDiv E) = ∑ i, Finsupp.single (P.reduceFst (Q₁ i)) (1 : ℤ) ∧
    Finsupp.mapDomain P.reduceSnd (P.sndDiv E) = ∑ j, Finsupp.single (P.reduceSnd (Q₂ j)) (1 : ℤ) := by
  classical
  set S := nodePairsOfPlaces (arithFrobC q k 1) W with hSdef
  have hqN : ¬ q ∣ 1 := fun h => (Fact.out : q.Prime).ne_one (Nat.dvd_one.mp h)

  have hphiσ : ∀ w : Place k ↥(modularFunctionFieldC k 1), arithFrobC q k 1 • w = (frobOnPlacesGeomLevel k 1 data hKr) w :=
    fun w => ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr w
  have hφinj : Function.Injective (frobOnPlacesGeomLevel k 1 data hKr) := by
    intro x y h; rw [← hphiσ, ← hphiσ] at h; exact smul_left_cancel _ h
  have hWfix : ∀ w ∈ W, (frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) w) = w := by
    intro w hw
    have h := ModularCurve.arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces q 1 hqN k w ((hW w).mp hw)
    rwa [hphiσ, hphiσ] at h
  have hWstab : ∀ v : Place k ↥(modularFunctionFieldC k 1), (frobOnPlacesGeomLevel k 1 data hKr) v ∈ ssPlaces q 1 k ↔ v ∈ ssPlaces q 1 k := by
    intro v
    constructor
    · intro h
      obtain ⟨b, hb, hbv⟩ := (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k _).mp h
      obtain ⟨c, rfl⟩ := IsAlgClosed.exists_pow_nat_eq b (Fact.out : q.Prime).pos
      rw [← ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceOfPoint k data hKr c] at hbv
      have hv := hφinj hbv
      rw [← hv]
      exact (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k _).mpr
        ⟨c, (ModularCurve.pow_mem_ssJSet_iff_of_perfectField q c).mp hb, rfl⟩
    · intro h
      obtain ⟨b, hb, rfl⟩ := (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k _).mp h
      rw [ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceOfPoint]
      exact (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k _).mpr
        ⟨b ^ q, (ModularCurve.pow_mem_ssJSet_iff_of_perfectField q b).mpr hb, rfl⟩
  have hWφ : ∀ w ∈ W, (frobOnPlacesGeomLevel k 1 data hKr) w ∈ W := fun w hw => (hW _).mpr ((hWstab w).mpr ((hW w).mp hw))
  have hWne : W.Nonempty := by
    obtain ⟨w, hw⟩ := ModularCurve.ssPlaces_nonempty q 1 hqN k
    exact ⟨w, (hW w).mpr hw⟩
  have hT₁nf : ∀ v ∈ T₁, (frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) ≠ v := by
    intro v hv; obtain ⟨i, rfl⟩ := (hT₁ v).mp hv; exact (hQ₁ i).2
  have hT₂nf : ∀ v ∈ T₂, (frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) ≠ v := by
    intro v hv; obtain ⟨j, rfl⟩ := (hT₂ v).mp hv; exact (hQ₂ j).2

  have hgpD : GluingData.IsGluedPrincipal S (dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))) :=
    (GluedPic0.mk_eq_zero_iff S ⟨_, hadm⟩).mp hsp
  obtain ⟨g₁, g₂, av, bv, hg₁0, hg₂0, hdivg₁, hdivg₂, hgvals, hgratio⟩ := hgpD

  obtain ⟨c₁, h₁, c₂, h₂, hr₁, hr₂, hB'⟩ := hB
  set ρ₁ : ↥(modularFunctionFieldC k 1) := R.residue₁ ⟨c₁ • f, h₁⟩ with hρ₁
  set ρ₂ : ↥(modularFunctionFieldC k 1) := R.residue₂ ⟨c₂ • f, h₂⟩ with hρ₂
  have hρ₁0 : ρ₁ ≠ 0 := fun h => hr₁ ((map_eq_zero_iff _ R.ι.injective).mp (by rw [← residue₁_apply]; exact h))
  have hρ₂0 : ρ₂ ≠ 0 := fun h => hr₂ ((map_eq_zero_iff _ R.ι.injective).mp (by rw [← residue₂_apply]; exact h))

  set π₁ : ↥(modularFunctionFieldC k 1) := ∏ w ∈ W, dat.unifFst w ^ dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w with hπ₁
  set π₂ : ↥(modularFunctionFieldC k 1) := ∏ w ∈ W, dat.unifSnd w ^ dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w with hπ₂
  set u₁ : ↥(modularFunctionFieldC k 1) := ρ₁ * g₁ * π₁ with hu₁def
  set u₂ : ↥(modularFunctionFieldC k 1) := ρ₂ * g₂ * π₂ with hu₂def
  have hcuspfix' : (frobOnPlacesGeomLevel k 1 data hKr) dat.cusp = dat.cusp := hcuspfix
  have hunif₂' : ∀ w' ∈ W, ∀ v : Place k ↥(modularFunctionFieldC k 1),
      v.ord (dat.unifSnd w') = (if v = (frobOnPlacesGeomLevel k 1 data hKr) w' then (1 : ℤ) else 0)
        - (if v = dat.cusp then (1 : ℤ) else 0) := by
    intro w' hw' v; rw [hunif₂ w' hw' v, hphiσ]
  obtain ⟨hπw₁, hunifW₁⟩ := ChartOkO4.unifFst_facts' W dat.cusp hcusp dat.unifFst hunif₁
  obtain ⟨hπw₂, hunifW₂⟩ := ChartOkO4.unifSnd_facts' W dat.cusp hcusp (frobOnPlacesGeomLevel k 1 data hKr) hφinj hcuspfix'
    dat.unifSnd hunif₂'
  have hπ₁0 : π₁ ≠ 0 := ChartOkO4.prod_zpow_ne_zero W dat.unifFst _ hπw₁
  have hπ₂0 : π₂ ≠ 0 := ChartOkO4.prod_zpow_ne_zero W dat.unifSnd _ hπw₂
  have hu₁0 : u₁ ≠ 0 := mul_ne_zero (mul_ne_zero hρ₁0 hg₁0) hπ₁0
  have hu₂0 : u₂ ≠ 0 := mul_ne_zero (mul_ne_zero hρ₂0 hg₂0) hπ₂0

  let Ebar₁ : Place k ↥(modularFunctionFieldC k 1) → ℤ := fun v => if v ∈ T₁ then 1 else 0
  let Ebar₂ : Place k ↥(modularFunctionFieldC k 1) → ℤ := fun v => if v ∈ T₂ then 1 else 0
  let EE₁ : Place k ↥(modularFunctionFieldC k 1) → ℤ := fun v => Finsupp.mapDomain P.reduceFst (P.fstDiv E) v
  let EE₂ : Place k ↥(modularFunctionFieldC k 1) → ℤ := fun v => Finsupp.mapDomain P.reduceSnd (P.sndDiv E) v
  have hE' : ∀ V, 0 ≤ E V := fun V => by simpa using Finsupp.le_def.mp hE0 V
  have mapDomain_nonneg : ∀ (r : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) →
        Place k ↥(modularFunctionFieldC k 1))
      (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))), (∀ V, 0 ≤ X V) →
      ∀ v, 0 ≤ Finsupp.mapDomain r X v := by
    intro r X hX v
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
    exact Finset.sum_nonneg fun V _ => by
      simp only [Finsupp.single_apply]
      split_ifs
      · exact hX V
      · exact le_rfl
  have hfilter_nonneg : ∀ (p : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → Prop)
      [DecidablePred p] (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))), 0 ≤ (E.filter p) V := by
    intro p _ V
    rw [Finsupp.filter_apply]
    split_ifs
    · exact hE' V
    · exact le_rfl
  have hEE₁ : ∀ v, 0 ≤ EE₁ v := fun v => mapDomain_nonneg P.reduceFst _ (hfilter_nonneg _) v
  have hEE₂ : ∀ v, 0 ≤ EE₂ v := fun v => mapDomain_nonneg P.reduceSnd _ (hfilter_nonneg _) v
  have hEbar₁eq : ∀ v, Finsupp.mapDomain P.reduceFst (∑ i, Finsupp.single (Q₁ i) (1 : ℤ)) v = Ebar₁ v := by
    intro v
    rw [Finsupp.mapDomain_finsetSum, Finsupp.finsetSum_apply]
    simp only [Finsupp.mapDomain_single, Finsupp.single_apply]
    by_cases hv : v ∈ T₁
    · obtain ⟨i, hi⟩ := (hT₁ v).mp hv
      rw [Finset.sum_eq_single i (fun j _ hji => if_neg fun h => hji (hinj₁ (h.trans hi.symm)))
        (fun h => absurd (Finset.mem_univ i) h), if_pos hi]
      exact (if_pos hv).symm
    · rw [Finset.sum_eq_zero fun i _ => if_neg fun h => hv ((hT₁ v).mpr ⟨i, h⟩)]
      exact (if_neg hv).symm
  have hEbar₂eq : ∀ v, Finsupp.mapDomain P.reduceSnd (∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) v = Ebar₂ v := by
    intro v
    rw [Finsupp.mapDomain_finsetSum, Finsupp.finsetSum_apply]
    simp only [Finsupp.mapDomain_single, Finsupp.single_apply]
    by_cases hv : v ∈ T₂
    · obtain ⟨j, hj⟩ := (hT₂ v).mp hv
      rw [Finset.sum_eq_single j (fun i _ hij => if_neg fun h => hij (hinj₂ (h.trans hj.symm)))
        (fun h => absurd (Finset.mem_univ j) h), if_pos hj]
      exact (if_pos hv).symm
    · rw [Finset.sum_eq_zero fun j _ => if_neg fun h => hv ((hT₂ v).mpr ⟨j, h⟩)]
      exact (if_neg hv).symm

  have hcuspfix2 : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr dat.cusp) = dat.cusp := by
    rw [hcuspfix, hcuspfix]
  have hdivg₁' : ∀ v : Place k ↥(modularFunctionFieldC k 1),
      (Finsupp.mapDomain P.reduceFst (P.fstDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))))
        - Divisor.degree (Finsupp.mapDomain P.reduceFst (P.fstDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))))) • Finsupp.single dat.cusp 1 :
        Place k ↥(modularFunctionFieldC k 1) →₀ ℤ) v = v.ord g₁ := fun v => hdivg₁ v
  have hdivg₂' : ∀ v : Place k ↥(modularFunctionFieldC k 1),
      (Finsupp.mapDomain P.reduceSnd (P.sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))))
        - Divisor.degree (Finsupp.mapDomain P.reduceSnd (P.sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))))) • Finsupp.single dat.cusp 1 :
        Place k ↥(modularFunctionFieldC k 1) →₀ ℤ) v = v.ord g₂ := fun v => hdivg₂ v
  have hπw₁' : ∀ w ∈ W, dat.unifFst w ≠ 0 := (ChartOkO4.unifFst_facts' W dat.cusp hcusp dat.unifFst hunif₁).1
  have hunif₂'' : ∀ w' ∈ W, ∀ v : Place k ↥(modularFunctionFieldC k 1),
      v.ord (dat.unifSnd w') = (if v = (frobOnPlacesGeomLevel k 1 data hKr) w' then (1 : ℤ) else 0)
        - (if v = dat.cusp then (1 : ℤ) else 0) := by
    intro w' hw' v; rw [hunif₂ w' hw' v, hphiσ]
  have hπw₂' : ∀ w ∈ W, dat.unifSnd w ≠ 0 :=
    (ChartOkO4.unifSnd_facts' W dat.cusp hcusp (frobOnPlacesGeomLevel k 1 data hKr) hφinj hcuspfix dat.unifSnd hunif₂'').1
  have O1₁ : ∀ v, (frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) ≠ v → (v.ord u₁ : ℤ) = EE₁ v - Ebar₁ v :=
    ChartOkO4.O1_fst P R hR W hWfix dat.cusp hcuspfix2 Q₁ Q₂ hQ₁ hQ₂ T₁ hEbar₁eq
      (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) E f c₁ h₁ hr₁ hdivf g₁ _ hdivg₁'
      dat.unifFst (fun w => dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w) hunif₁ hπw₁' hg₁0 ρ₁ u₁ hρ₁ hu₁def
  have O1₂ : ∀ v, (frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) ≠ v → (v.ord u₂ : ℤ) = EE₂ v - Ebar₂ v :=
    ChartOkO4.O1_snd P R hR W hWfix dat.cusp hcuspfix2 Q₁ Q₂ hQ₁ hQ₂ T₂ hEbar₂eq
      (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) E f c₂ h₂ hr₂ hdivf g₂ _ hdivg₂'
      dat.unifSnd (fun w => dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w) hunif₂'' hπw₂' hg₂0 ρ₂ u₂ hρ₂ hu₂def

  have hc₁0 : c₁ ≠ 0 := R.R₁.smul_const_ne_zero h₁ hr₁
  have hc₂0 : c₂ ≠ 0 := R.R₂.smul_const_ne_zero h₂ hr₂
  have hdiv₁' : ∀ V, (E - ((∑ i, Finsupp.single (Q₁ i) (1 : ℤ)) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
      - (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))) V = V.ord (c₁ • f) := by
    intro V
    rw [hdivf V, Algebra.smul_def, V.ord_mul ((map_ne_zero _).mpr hc₁0) hf0,
      (V.hasValue_algebraMap c₁).ord_eq_zero hc₁0, zero_add]
  have hdiv₂' : ∀ V, (E - ((∑ i, Finsupp.single (Q₁ i) (1 : ℤ)) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
      - (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))) V = V.ord (c₂ • f) := by
    intro V
    rw [hdivf V, Algebra.smul_def, V.ord_mul ((map_ne_zero _).mpr hc₂0) hf0,
      (V.hasValue_algebraMap c₂).ord_eq_zero hc₂0, zero_add]

  have hA1₁ := (ModularCurve.PlaceSpecialization.ProlongationTuple.residue_bounds_offNodes_of_adm_oneSided hR hW hRL
    Q₁ Q₂ hQ₁ hQ₂ hinj₁ hinj₂ hT₁ hT₂ E (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) hE0 hD
    (c₁ • f) hdiv₁').1 h₁ hρ₁0
  have hA1₂ := (ModularCurve.PlaceSpecialization.ProlongationTuple.residue_bounds_offNodes_of_adm_oneSided hR hW hRL
    Q₁ Q₂ hQ₁ hQ₂ hinj₁ hinj₂ hT₁ hT₂ E (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) hE0 hD
    (c₂ • f) hdiv₂').2 h₂ hρ₂0

  haveI hcurveBar : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) :=
    ModularCurve.isCurveOver_modularFunctionFieldBar (1 * q)
  haveI hcurveC : IsCurveOver k ↥(modularFunctionFieldC k 1) := ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField k 1
  have degree_mapDomain_red : ∀ (r : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → Place k ↥(modularFunctionFieldC k 1))
      (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
      Divisor.degree (Finsupp.mapDomain r X) = Divisor.degree X := by
    intro r X
    induction X using Finsupp.induction with
    | zero => simp
    | single_add V n X _ _ ih =>
      rw [Finsupp.mapDomain_add, map_add, map_add, ih, Finsupp.mapDomain_single,
        Divisor.degree_single, Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed]

  have hZ₁ : Divisor.degree (Finsupp.mapDomain P.reduceFst (P.fstDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))))
      = -∑ w ∈ W, dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w := by rw [degree_mapDomain_red]; exact ha.1
  have hZ₂ : Divisor.degree (Finsupp.mapDomain P.reduceSnd (P.sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))))
      = -∑ w ∈ W, dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w := by rw [degree_mapDomain_red]; exact ha.2.1
  have O2₁ : ∀ v, (frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) = v → v ∉ W → 0 ≤ v.ord u₁ := by
    intro v hv hvW

    have hρ := hA1₁ v hvW
    rw [hEbar₁eq v, ChartOkO4.mapDomain_reduceFst_fstDiv_apply_eq_zero_of_fixed P _ v hv] at hρ
    have hvT : v ∉ T₁ := fun h => hT₁nf v h hv
    simp only [Ebar₁, if_neg hvT, neg_zero, sub_zero] at hρ

    have hg : v.ord g₁ = -(Divisor.degree (Finsupp.mapDomain P.reduceFst (P.fstDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))))
        * (if dat.cusp = v then 1 else 0)) := by
      rw [← hdivg₁ v]
      change (Finsupp.mapDomain P.reduceFst (P.fstDiv _) - Divisor.degree (Finsupp.mapDomain P.reduceFst (P.fstDiv _)) • Finsupp.single dat.cusp (1:ℤ)) v = _
      rw [Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_apply,
        ChartOkO4.mapDomain_reduceFst_fstDiv_apply_eq_zero_of_fixed P _ v hv, zero_sub, smul_eq_mul]

    have hπ : v.ord π₁ = ∑ w ∈ W, dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w * v.ord (dat.unifFst w) :=
      ChartOkO4.ord_prod_zpow v W dat.unifFst _ hπw₁
    have hπ' : ∀ w ∈ W, v.ord (dat.unifFst w) = -(if v = dat.cusp then (1 : ℤ) else 0) := by
      intro w hw
      rw [hunif₁ w hw v, if_neg (show ¬ v = w by rintro rfl; exact hvW hw)]; ring
    rw [Finset.sum_congr rfl fun w hw => by rw [hπ' w hw]] at hπ
    rw [hu₁def, Place.ord_mul _ (mul_ne_zero hρ₁0 hg₁0) hπ₁0, Place.ord_mul _ hρ₁0 hg₁0, hg, hπ, ← Finset.sum_mul, hZ₁]
    by_cases hvc : v = dat.cusp
    · subst hvc; simp; linarith
    · rw [if_neg hvc, if_neg (Ne.symm hvc)]; simp; linarith
  have O2₂ : ∀ v, (frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) = v → v ∉ W → 0 ≤ v.ord u₂ := by
    intro v hv hvW
    have hρ := hA1₂ v hvW
    rw [hEbar₂eq v, ChartOkO4.mapDomain_reduceSnd_sndDiv_apply_eq_zero_of_fixed P _ v hv] at hρ
    have hvT : v ∉ T₂ := fun h => hT₂nf v h hv
    simp only [Ebar₂, if_neg hvT, neg_zero, sub_zero] at hρ
    have hg : v.ord g₂ = -(Divisor.degree (Finsupp.mapDomain P.reduceSnd (P.sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))))
        * (if dat.cusp = v then 1 else 0)) := by
      rw [← hdivg₂ v]
      change (Finsupp.mapDomain P.reduceSnd (P.sndDiv _) - Divisor.degree (Finsupp.mapDomain P.reduceSnd (P.sndDiv _)) • Finsupp.single dat.cusp (1:ℤ)) v = _
      rw [Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_apply,
        ChartOkO4.mapDomain_reduceSnd_sndDiv_apply_eq_zero_of_fixed P _ v hv, zero_sub, smul_eq_mul]
    have hπ : v.ord π₂ = ∑ w ∈ W, dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w * v.ord (dat.unifSnd w) :=
      ChartOkO4.ord_prod_zpow v W dat.unifSnd _ hπw₂
    have hπ' : ∀ w ∈ W, v.ord (dat.unifSnd w) = -(if v = dat.cusp then (1 : ℤ) else 0) := by
      intro w hw
      rw [hunif₂' w hw v, if_neg (show ¬ v = (frobOnPlacesGeomLevel k 1 data hKr) w by rintro rfl; exact hvW (hWφ w hw))]; ring
    rw [Finset.sum_congr rfl fun w hw => by rw [hπ' w hw]] at hπ
    rw [hu₂def, Place.ord_mul _ (mul_ne_zero hρ₂0 hg₂0) hπ₂0, Place.ord_mul _ hρ₂0 hg₂0, hg, hπ, ← Finset.sum_mul, hZ₂]
    by_cases hvc : v = dat.cusp
    · subst hvc; simp; linarith
    · rw [if_neg hvc, if_neg (Ne.symm hvc)]; simp; linarith

  have hgw₁ : ∀ w ∈ W, w.ord g₁ = 0 := fun w hw =>
    (hgvals ⟨(w, arithFrobC q k 1 • w), (mem_nodePairsOfPlaces_iff _ _ _).mpr ⟨w, hw, rfl⟩⟩).1.ord_eq_zero (Units.ne_zero _)
  have hgw₂ : ∀ w ∈ W, ((frobOnPlacesGeomLevel k 1 data hKr) w).ord g₂ = 0 := fun w hw => by
    rw [← hphiσ]
    exact (hgvals ⟨(w, arithFrobC q k 1 • w), (mem_nodePairsOfPlaces_iff _ _ _).mpr ⟨w, hw, rfl⟩⟩).2.ord_eq_zero (Units.ne_zero _)
  have hunifW₁' := (ChartOkO4.unifFst_facts' W dat.cusp hcusp dat.unifFst hunif₁).2
  have hunifW₂' := (ChartOkO4.unifSnd_facts' W dat.cusp hcusp (frobOnPlacesGeomLevel k 1 data hKr) hφinj hcuspfix dat.unifSnd hunif₂'').2
  have hs₁ : ∀ w ∈ W, w.ord u₁ = w.ord ρ₁ + dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w := fun w hw => by
    rw [hu₁def]
    exact ChartOkO4.ord_corrected_eq W ρ₁ g₁ hρ₁0 hg₁0 dat.unifFst (fun w' => dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w') hπw₁' w hw (hgw₁ w hw)
      (hunifW₁' w hw) _ rfl
  have hs₂ : ∀ w ∈ W, ((frobOnPlacesGeomLevel k 1 data hKr) w).ord u₂ = ((frobOnPlacesGeomLevel k 1 data hKr) w).ord ρ₂ + dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w :=
    fun w hw => by
    rw [hu₂def]
    exact ChartOkO4.ord_corrected_eq' W ρ₂ g₂ hρ₂0 hg₂0 dat.unifSnd (fun w' => dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w') hπw₂'
      ((frobOnPlacesGeomLevel k 1 data hKr) w) w hw (hgw₂ w hw) (hunifW₂' w hw) _ rfl

  have A₁' : ∀ w ∈ W, δ ≤ (dat.width w : ℚ) * ((w.ord u₁ : ℤ) : ℚ) := fun w hw => by
    rw [hs₁ w hw, hρ₁]; push_cast; exact hA₁ c₁ h₁ hr₁ w hw
  have A₂' : ∀ w ∈ W, -((dat.width w : ℚ) * ((((frobOnPlacesGeomLevel k 1 data hKr) w).ord u₂ : ℤ) : ℚ)) ≤ δ := fun w hw => by
    rw [hs₂ w hw, hρ₂, ← hphiσ]; push_cast; exact hA₂ c₂ h₂ hr₂ w hw
  have B' : ∀ w ∈ W, δ = 0 → ((frobOnPlacesGeomLevel k 1 data hKr) w).ord u₂ = 0 →
      w.ord u₁ = 0 ∧ ∃ c : k, w.HasValue u₁ c ∧ ((frobOnPlacesGeomLevel k 1 data hKr) w).HasValue u₂ c := by
    intro w hw hδ h2
    rw [hs₂ w hw, hρ₂, ← hphiσ] at h2
    obtain ⟨h1, c, hv₁, hv₂⟩ := hB' g₁ g₂ av bv hdivg₁ hdivg₂ hgvals hgratio w hw hδ h2
    refine ⟨by rw [hs₁ w hw, hρ₁]; exact h1, (c : k), ?_, ?_⟩
    · simp only [hu₁def, hρ₁, hπ₁] at hv₁ ⊢; exact hv₁
    · rw [← hphiσ]; simp only [hu₂def, hρ₂, hπ₂] at hv₂ ⊢; exact hv₂

  obtain ⟨hh₁, hh₁', hh₂, hh₂', hval⟩ := ChartOkA2.carrier_hypotheses_of_endSlopes (frobOnPlacesGeomLevel k 1 data hKr) hφinj W T₁ T₂ hWne hWfix hWφ hT₁nf hT₂nf
    Ebar₁ Ebar₂ EE₁ EE₂ (fun v => rfl) (fun v => rfl) hEE₁ hEE₂ u₁ u₂ hu₁0 hu₂0 O1₁ O1₂ O2₁ O2₂
    dat.width hwidth δ A₁' A₂' B' hgp₁ hgp₂

  have hlink₁ : ∀ v, (frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) ≠ v → v.ord u₁ = Finsupp.mapDomain P.reduceFst (P.fstDiv E) v
        - Finsupp.mapDomain P.reduceFst (∑ i, Finsupp.single (Q₁ i) (1 : ℤ)) v := by
    intro v hv; rw [O1₁ v hv, hEbar₁eq]
  have hlink₂ : ∀ v, (frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) ≠ v → v.ord u₂ = Finsupp.mapDomain P.reduceSnd (P.sndDiv E) v
        - Finsupp.mapDomain P.reduceSnd (∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) v := by
    intro v hv; rw [O1₂ v hv, hEbar₂eq]
  have hval' : ∀ w ∈ W, ∃ c : k, w.HasValue u₁ c ∧ (arithFrobC q k 1 • w).HasValue u₂ c := by
    intro w hw; rw [hphiσ]; exact hval w hw
  exact ModularCurve.PlaceSpecialization.mapDomain_fstDiv_eq_and_mapDomain_sndDiv_eq_of_reducedPair P W Q₁ Q₂ hQ₁ hQ₂
    hgp₁ hgp₂ E u₁ u₂ hu₁0 hu₂0 hh₁ hh₁' hh₂ hh₂' hval' hlink₁ hlink₂

namespace CHARTOKB

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve.PlaceSpecialization"

set_option autoImplicit false

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

theorem not_isStrictFst_and_isStrictSnd (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    ¬ (P.IsStrictFst V ∧ P.IsStrictSnd V) := by
  rintro ⟨⟨h1, h1'⟩, ⟨h2, -⟩⟩
  apply h1'
  rw [h1, ← h2]

theorem sum_single_apply_eq_zero' {α ι : Type*} [Fintype ι] (Q : ι → α) (V : α) (h : ∀ i, Q i ≠ V) :
    (∑ i, Finsupp.single (Q i) (1 : ℤ)) V = 0 := by
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero fun i _ => Finsupp.single_eq_of_ne (h i).symm

theorem exists_divisor_degree_eq_zero {f : ↥(modularFunctionFieldBar (1 * q))} (hf : f ≠ 0) :
    ∃ Df : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      (∀ V, Df V = V.ord f) ∧ Df.degree = 0 := by
  haveI : NeZero (1 * q) := ⟨by rw [one_mul]; exact (Fact.out : q.Prime).ne_zero⟩
  haveI := ModularCurve.isCurveOver_modularFunctionFieldBar (1 * q)
  exact HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) f hf

theorem exists_isGoodDiv_glueData_mk_eq_zero_of_polydiscRep
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (S : Finset (Place k ↥(modularFunctionFieldC k 1) × Place k ↥(modularFunctionFieldC k 1)))
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
    {d₁ d₂ : ℕ}
    (Q₁ Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q₂ Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₁' : ∀ i, P.IsStrictFst (Q₁' i))
    (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j)) (hQ₂' : ∀ j, P.IsStrictSnd (Q₂' j))
    (hred₁ : ∀ i, P.reduceFst (Q₁' i) = P.reduceFst (Q₁ i))
    (hred₂ : ∀ j, P.reduceSnd (Q₂' j) = P.reduceSnd (Q₂ j))
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0)
    (hdiv : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      V.ord f =
        ((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) :
            Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) V)
        - ((∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) :
            Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) V)
        - (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) V) :
    ∃ (E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
      (hadm : P.glueData S (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
        ∈ GluingData.admissible S),
      P.IsGoodDiv (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) ∧
      GluedPic0.mk S ⟨P.glueData S (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))), hadm⟩
        = 0 ∧
      Pic0.mk E = Pic0.mk D := by
  classical

  set E₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) :=
    ∑ i, (Finsupp.single (Q₁' i) (1 : ℤ) - Finsupp.single (Q₁ i) (1 : ℤ)) with hE₁
  set E₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) :=
    ∑ j, (Finsupp.single (Q₂' j) (1 : ℤ) - Finsupp.single (Q₂ j) (1 : ℤ)) with hE₂
  set E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) := E₁ + E₂ with hE
  have hE₁apply : ∀ V, E₁ V =
      (∑ i, Finsupp.single (Q₁' i) (1 : ℤ)) V - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ)) V := by
    intro V
    simp only [hE₁, Finsupp.finsetSum_apply, Finsupp.sub_apply, Finset.sum_sub_distrib]
  have hE₂apply : ∀ V, E₂ V =
      (∑ j, Finsupp.single (Q₂' j) (1 : ℤ)) V - (∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) V := by
    intro V
    simp only [hE₂, Finsupp.finsetSum_apply, Finsupp.sub_apply, Finset.sum_sub_distrib]

  obtain ⟨Df, hDf, hDfdeg⟩ := exists_divisor_degree_eq_zero hf
  have hEeq : E = (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) + Df := by
    ext V
    rw [Finsupp.add_apply (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) Df V, hDf V,
      hdiv V, hE, Finsupp.add_apply E₁ E₂ V, hE₁apply, hE₂apply,
      Finsupp.add_apply (∑ i, Finsupp.single (Q₁' i) (1 : ℤ)) (∑ j, Finsupp.single (Q₂' j) (1 : ℤ)) V,
      Finsupp.add_apply (∑ i, Finsupp.single (Q₁ i) (1 : ℤ)) (∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) V]
    ring
  have hEdeg : E ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))) := by
    rw [hEeq]; exact add_mem D.2 ((Divisor.mem_degZero).mpr hDfdeg)

  have hE₁zero : ∀ V, ¬ P.IsStrictFst V → E₁ V = 0 := by
    intro V hV
    rw [hE₁apply, sum_single_apply_eq_zero' Q₁' V (fun i h => hV (h ▸ hQ₁' i)),
      sum_single_apply_eq_zero' Q₁ V (fun i h => hV (h ▸ hQ₁ i)), sub_zero]
  have hE₂zero : ∀ V, ¬ P.IsStrictSnd V → E₂ V = 0 := by
    intro V hV
    rw [hE₂apply, sum_single_apply_eq_zero' Q₂' V (fun j h => hV (h ▸ hQ₂' j)),
      sum_single_apply_eq_zero' Q₂ V (fun j h => hV (h ▸ hQ₂ j)), sub_zero]
  have hfst : P.fstDiv E = E₁ := by
    ext V
    unfold PlaceSpecialization.fstDiv
    rw [Finsupp.filter_apply]
    split_ifs with h
    · rw [hE, Finsupp.add_apply, hE₂zero V (fun h2 => not_isStrictFst_and_isStrictSnd P V ⟨h, h2⟩), add_zero]
    · exact (hE₁zero V h).symm
  have hsnd : P.sndDiv E = E₂ := by
    ext V
    unfold PlaceSpecialization.sndDiv
    rw [Finsupp.filter_apply]
    split_ifs with h
    · rw [hE, Finsupp.add_apply, hE₁zero V (fun h1 => not_isStrictFst_and_isStrictSnd P V ⟨h1, h⟩), zero_add]
    · exact (hE₂zero V h).symm

  have hmap₁ : Finsupp.mapDomain P.reduceFst E₁ = 0 := by
    change Finsupp.mapDomain.addMonoidHom P.reduceFst E₁ = 0
    rw [hE₁, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_sub, Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain.addMonoidHom_apply,
      Finsupp.mapDomain_single, Finsupp.mapDomain_single, hred₁ i, sub_self]
  have hmap₂ : Finsupp.mapDomain P.reduceSnd E₂ = 0 := by
    change Finsupp.mapDomain.addMonoidHom P.reduceSnd E₂ = 0
    rw [hE₂, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_sub, Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain.addMonoidHom_apply,
      Finsupp.mapDomain_single, Finsupp.mapDomain_single, hred₂ j, sub_self]
  have hglue : P.glueData S E = 0 := by
    unfold PlaceSpecialization.glueData
    rw [hfst, hsnd, hmap₁, hmap₂]
    rfl
  have hadm : P.glueData S E ∈ GluingData.admissible S := by
    rw [hglue]; exact zero_mem _

  refine ⟨⟨E, hEdeg⟩, hadm, ?_, ?_, ?_⟩
  ·
    intro V hV
    by_contra hbad
    rcases not_or.mp hbad with ⟨h1, h2⟩
    apply Finsupp.mem_support_iff.mp hV
    show E V = 0
    rw [hE, Finsupp.add_apply, hE₁zero V h1, hE₂zero V h2, add_zero]
  · have h0 : (⟨P.glueData S E, hadm⟩ : ↥(GluingData.admissible S)) = 0 := Subtype.ext hglue
    rw [h0, map_zero]
  · show (QuotientAddGroup.mk _ : Pic0 _ _) = QuotientAddGroup.mk _
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    have hcoe : ((-(⟨E, hEdeg⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
        (F := ↥(modularFunctionFieldBar (1 * q))))) + D :
          ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))))) :
        Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) =
          -E + (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) := rfl
    rw [hcoe, hEeq, neg_add_rev, add_assoc, neg_add_cancel, add_zero]
    exact neg_mem ⟨f, hf, hDf⟩

end CHARTOKB

namespace CHARTOKB

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve.PlaceSpecialization"

set_option autoImplicit false

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

theorem isGoodDiv_and_glueData_eq_zero_of_reduce_eq
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (S : Finset (Place k ↥(modularFunctionFieldC k 1) × Place k ↥(modularFunctionFieldC k 1)))
    {d₁ d₂ : ℕ}
    (Q₁ Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q₂ Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₁' : ∀ i, P.IsStrictFst (Q₁' i))
    (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j)) (hQ₂' : ∀ j, P.IsStrictSnd (Q₂' j))
    (hred₁ : ∀ i, P.reduceFst (Q₁' i) = P.reduceFst (Q₁ i))
    (hred₂ : ∀ j, P.reduceSnd (Q₂' j) = P.reduceSnd (Q₂ j)) :
    P.IsGoodDiv ((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
        - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))) ∧
    P.glueData S ((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
        - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))) = 0 := by
  classical
  set E₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) :=
    ∑ i, (Finsupp.single (Q₁' i) (1 : ℤ) - Finsupp.single (Q₁ i) (1 : ℤ)) with hE₁
  set E₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) :=
    ∑ j, (Finsupp.single (Q₂' j) (1 : ℤ) - Finsupp.single (Q₂ j) (1 : ℤ)) with hE₂
  have hEsplit : ((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
        - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) :
        Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) = E₁ + E₂ := by
    rw [hE₁, hE₂, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    abel
  rw [hEsplit]
  have hE₁apply : ∀ V, E₁ V =
      (∑ i, Finsupp.single (Q₁' i) (1 : ℤ)) V - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ)) V := by
    intro V
    simp only [hE₁, Finsupp.finsetSum_apply, Finsupp.sub_apply, Finset.sum_sub_distrib]
  have hE₂apply : ∀ V, E₂ V =
      (∑ j, Finsupp.single (Q₂' j) (1 : ℤ)) V - (∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) V := by
    intro V
    simp only [hE₂, Finsupp.finsetSum_apply, Finsupp.sub_apply, Finset.sum_sub_distrib]
  have hE₁zero : ∀ V, ¬ P.IsStrictFst V → E₁ V = 0 := by
    intro V hV
    rw [hE₁apply, sum_single_apply_eq_zero' Q₁' V (fun i h => hV (h ▸ hQ₁' i)),
      sum_single_apply_eq_zero' Q₁ V (fun i h => hV (h ▸ hQ₁ i)), sub_zero]
  have hE₂zero : ∀ V, ¬ P.IsStrictSnd V → E₂ V = 0 := by
    intro V hV
    rw [hE₂apply, sum_single_apply_eq_zero' Q₂' V (fun j h => hV (h ▸ hQ₂' j)),
      sum_single_apply_eq_zero' Q₂ V (fun j h => hV (h ▸ hQ₂ j)), sub_zero]
  refine ⟨?_, ?_⟩
  · intro V hV
    by_contra hbad
    rcases not_or.mp hbad with ⟨h1, h2⟩
    apply Finsupp.mem_support_iff.mp hV
    rw [Finsupp.add_apply, hE₁zero V h1, hE₂zero V h2, add_zero]
  · have hfst : P.fstDiv (E₁ + E₂) = E₁ := by
      ext V
      unfold PlaceSpecialization.fstDiv
      rw [Finsupp.filter_apply]
      split_ifs with h
      · rw [Finsupp.add_apply, hE₂zero V (fun h2 => not_isStrictFst_and_isStrictSnd P V ⟨h, h2⟩), add_zero]
      · exact (hE₁zero V h).symm
    have hsnd : P.sndDiv (E₁ + E₂) = E₂ := by
      ext V
      unfold PlaceSpecialization.sndDiv
      rw [Finsupp.filter_apply]
      split_ifs with h
      · rw [Finsupp.add_apply, hE₁zero V (fun h1 => not_isStrictFst_and_isStrictSnd P V ⟨h1, h⟩), zero_add]
      · exact (hE₂zero V h).symm
    have hmap₁ : Finsupp.mapDomain P.reduceFst E₁ = 0 := by
      change Finsupp.mapDomain.addMonoidHom P.reduceFst E₁ = 0
      rw [hE₁, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_sub, Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain.addMonoidHom_apply,
        Finsupp.mapDomain_single, Finsupp.mapDomain_single, hred₁ i, sub_self]
    have hmap₂ : Finsupp.mapDomain P.reduceSnd E₂ = 0 := by
      change Finsupp.mapDomain.addMonoidHom P.reduceSnd E₂ = 0
      rw [hE₂, map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_sub, Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain.addMonoidHom_apply,
        Finsupp.mapDomain_single, Finsupp.mapDomain_single, hred₂ j, sub_self]
    unfold PlaceSpecialization.glueData
    rw [hfst, hsnd, hmap₁, hmap₂]
    rfl

theorem exists_isGoodDiv_glueData_mk_eq_zero_of_pic0Mk_eq
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (S : Finset (Place k ↥(modularFunctionFieldC k 1) × Place k ↥(modularFunctionFieldC k 1)))
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
    {d₁ d₂ : ℕ}
    (Q₁ Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q₂ Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₁' : ∀ i, P.IsStrictFst (Q₁' i))
    (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j)) (hQ₂' : ∀ j, P.IsStrictSnd (Q₂' j))
    (hred₁ : ∀ i, P.reduceFst (Q₁' i) = P.reduceFst (Q₁ i))
    (hred₂ : ∀ j, P.reduceSnd (Q₂' j) = P.reduceSnd (Q₂ j))
    (hdeg0 : ((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
        - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) :
          Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) ∈
            Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))))
    (hmkD : Pic0.mk ⟨_, hdeg0⟩ = Pic0.mk D) :
    ∃ (E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
      (hadm : P.glueData S (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
        ∈ GluingData.admissible S),
      P.IsGoodDiv (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) ∧
      GluedPic0.mk S ⟨P.glueData S (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))), hadm⟩
        = 0 ∧
      Pic0.mk E = Pic0.mk D := by
  obtain ⟨hgood, hglue⟩ :=
    isGoodDiv_and_glueData_eq_zero_of_reduce_eq P S Q₁ Q₁' Q₂ Q₂' hQ₁ hQ₁' hQ₂ hQ₂' hred₁ hred₂
  have hadm : P.glueData S (((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
      - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) :
        Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))) ∈ GluingData.admissible S := by
    rw [hglue]; exact zero_mem _
  refine ⟨⟨_, hdeg0⟩, hadm, hgood, ?_, hmkD⟩
  have h0 : (⟨_, hadm⟩ : ↥(GluingData.admissible S)) = 0 := Subtype.ext hglue
  rw [h0, map_zero]

end CHARTOKB

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple PlaceSpecialization.fstDiv PlaceSpecialization.sndDiv PlaceSpecialization.glueData arithmeticGalois modularFunctionFieldBar ModularPolynomialData modularFunctionFieldFull modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence nodePairsOfPlaces mem_nodePairsOfPlaces_iff ssPlaces jGeomGen jNGeomGen jNGeomGen_one IsCentreOf IsAffineGeomPlace arithFrobC PlaceSpecialization.ProlongationTuple.AnnulusDatumQ NodeLocalized.coeffSubring NodeLocalized.redRestrict PlaceSpecialization.ProlongationTuple.AnnulusDatum jWidth PlaceSpecialization.ProlongationTuple.cuspLawInfty_oneSided_levelOne PlaceSpecialization.ProlongationTuple.cuspLawZero_oneSided_levelOne PlaceSpecialization.ProlongationTuple.divisorLawFst_oneSided_levelOne PlaceSpecialization.ProlongationTuple.divisorLawSnd_oneSided_levelOne PlaceSpecialization.ProlongationTuple.regularityLawFst_oneSided_levelOne PlaceSpecialization.ProlongationTuple.regularityLawSnd_oneSided_levelOne PlaceSpecialization.exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace PlaceSpecialization.exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq PlaceSpecialization.not_fixed_reduceFst_of_isStrictSnd arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces arithFrobC_smul_eq_frobOnPlacesGeomLevel deg_eq_one_modularFunctionFieldBar essFiniteType_modularFunctionFieldFullC exists_effective_pic0Mk_sub_eq_of_genusFF_le_degree exists_eq_algebraMap_of_hasValue_smul_of_generalPosition finite_setOf_ord_jGeomGen_sub_pos frobOnPlacesGeomLevel_charLGeomPlaceOfPoint genusFF_modularFunctionFieldBar_mul_add_one_eq_of_ssPlaces isAffineGeomPlace_frobOnPlacesGeomLevel isCurveOver_modularFunctionFieldBar isCurveOver_modularFunctionFieldC_of_perfectField isSeparable_jqNModC_of_natCast_ne_zero mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq modularFunctionFieldC_eq_modularFunctionFieldFullC pow_mem_ssJSet_iff_of_perfectField ssPlaces_nonempty PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple ProlongationTuple.residue₁_apply ProlongationTuple.residue₂_apply reduceFst reduceSnd IsStrictFst IsStrictSnd IsGoodDiv fstDiv sndDiv glueData sp mk d1 ProlongationTuple.AnnulusDatumQ ProlongationTuple.AnnulusDatum ProlongationTuple.TwistVector ProlongationTuple.cuspLawInfty_oneSided_levelOne ProlongationTuple.cuspLawZero_oneSided_levelOne ProlongationTuple.divisorLawFst_oneSided_levelOne ProlongationTuple.divisorLawSnd_oneSided_levelOne ProlongationTuple.regularityLawFst_oneSided_levelOne ProlongationTuple.regularityLawSnd_oneSided_levelOne exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq not_fixed_reduceFst_of_isStrictSnd ProlongationTuple.AnnulusDatumQ.exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

private theorem _root_.ModularCurve.PlaceSpecialization.not_isStrictFst_of_isStrictSnd {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h2 : P.IsStrictSnd W) : ¬ P.IsStrictFst W := by
  intro h1
  apply h1.2
  rw [h1.1, ← h2.1]

p2m_export "ModularCurve.PlaceSpecialization" "not_isStrictFst_of_isStrictSnd"

theorem degree_eq_sum (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    D.degree = D.sum (fun _ n => n) := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun W _ => ?_
  simp [ModularCurve.deg_eq_one_modularFunctionFieldBar]

private theorem _root_.ModularCurve.PlaceSpecialization.fstDiv_nonneg {E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hE : 0 ≤ E) :
    0 ≤ P.fstDiv E := by
  intro W
  simp only [fstDiv, Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
  split_ifs
  · exact hE W
  · exact le_rfl

p2m_export "ModularCurve.PlaceSpecialization" "fstDiv_nonneg"
private theorem _root_.ModularCurve.PlaceSpecialization.sndDiv_nonneg {E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hE : 0 ≤ E) :
    0 ≤ P.sndDiv E := by
  intro W
  simp only [sndDiv, Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
  split_ifs
  · exact hE W
  · exact le_rfl

p2m_export "ModularCurve.PlaceSpecialization" "sndDiv_nonneg"

private theorem _root_.ModularCurve.PlaceSpecialization.exists_eq_fstDiv_add_sndDiv_add {E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hE : 0 ≤ E) :
    ∃ E₃ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), 0 ≤ E₃ ∧
      E = P.fstDiv E + P.sndDiv E + E₃ ∧ ∀ W ∈ E₃.support, ¬ P.IsStrictFst W ∧ ¬ P.IsStrictSnd W := by
  classical
  refine ⟨(E.filter fun W => ¬ P.IsStrictFst W).filter fun W => ¬ P.IsStrictSnd W, ?_, ?_, ?_⟩
  · intro W
    simp only [Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
    split_ifs <;> first | exact hE W | exact le_rfl
  · ext W
    simp only [fstDiv, sndDiv, Finsupp.coe_add, Pi.add_apply, Finsupp.filter_apply]
    by_cases h1 : P.IsStrictFst W
    · have h2 : ¬ P.IsStrictSnd W := fun h2 => P.not_isStrictFst_of_isStrictSnd h2 h1
      simp [h1, h2]
    · by_cases h2 : P.IsStrictSnd W
      · simp [h1, h2]
      · simp [h1, h2]
  · intro W hW
    rw [Finsupp.mem_support_iff] at hW
    simp only [Finsupp.filter_apply] at hW
    by_cases h2 : ¬ P.IsStrictSnd W
    · rw [if_pos h2] at hW
      by_cases h1 : ¬ P.IsStrictFst W
      · exact ⟨h1, h2⟩
      · rw [if_neg h1] at hW; exact absurd rfl hW
    · rw [if_neg h2] at hW; exact absurd rfl hW

p2m_export "ModularCurve.PlaceSpecialization" "exists_eq_fstDiv_add_sndDiv_add"

private theorem _root_.ModularCurve.PlaceSpecialization.exists_eq_sum_add_sum_of_mapDomain_fstDiv_sndDiv
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hE : 0 ≤ E)
    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
    (hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
    (h₁ : Finsupp.mapDomain P.reduceFst (P.fstDiv E) = ∑ i, Finsupp.single (P.reduceFst (Q₁ i)) (1 : ℤ))
    (h₂ : Finsupp.mapDomain P.reduceSnd (P.sndDiv E) = ∑ j, Finsupp.single (P.reduceSnd (Q₂ j)) (1 : ℤ))
    (hdeg : E.degree = (d₁ + d₂ : ℕ)) :
    ∃ (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
      (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      (∀ i, P.IsStrictFst (Q₁' i)) ∧ (∀ j, P.IsStrictSnd (Q₂' j)) ∧
      (∀ i, P.reduceFst (Q₁' i) = P.reduceFst (Q₁ i)) ∧
      (∀ j, P.reduceSnd (Q₂' j) = P.reduceSnd (Q₂ j)) ∧
      E = ∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) := by
  classical
  obtain ⟨Q₁', hE₁, hred₁⟩ := Finsupp.exists_eq_sum_single_of_mapDomain_eq_sum_single P.reduceFst (P.fstDiv E)
    (P.fstDiv_nonneg hE) (fun i => P.reduceFst (Q₁ i)) hinj₁ h₁
  obtain ⟨Q₂', hE₂, hred₂⟩ := Finsupp.exists_eq_sum_single_of_mapDomain_eq_sum_single P.reduceSnd (P.sndDiv E)
    (P.sndDiv_nonneg hE) (fun j => P.reduceSnd (Q₂ j)) hinj₂ h₂

  have mem₁ : ∀ i, Q₁' i ∈ (P.fstDiv E).support := by
    intro i
    rw [hE₁, Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
    apply ne_of_gt
    apply Finset.sum_pos'
    · intro j _; rw [Finsupp.single_apply]; split_ifs <;> omega
    · exact ⟨i, Finset.mem_univ _, by simp⟩
  have mem₂ : ∀ j, Q₂' j ∈ (P.sndDiv E).support := by
    intro j
    rw [hE₂, Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
    apply ne_of_gt
    apply Finset.sum_pos'
    · intro i _; rw [Finsupp.single_apply]; split_ifs <;> omega
    · exact ⟨j, Finset.mem_univ _, by simp⟩
  have hQ₁' : ∀ i, P.IsStrictFst (Q₁' i) := fun i => by
    have := mem₁ i
    rw [fstDiv, Finsupp.support_filter, Finset.mem_filter] at this
    exact this.2
  have hQ₂' : ∀ j, P.IsStrictSnd (Q₂' j) := fun j => by
    have := mem₂ j
    rw [sndDiv, Finsupp.support_filter, Finset.mem_filter] at this
    exact this.2
  refine ⟨Q₁', Q₂', hQ₁', hQ₂', hred₁, hred₂, ?_⟩

  obtain ⟨E₃, hE₃, hsplit, -⟩ := P.exists_eq_fstDiv_add_sndDiv_add hE
  have hmass : E₃.sum (fun _ n => n) = 0 := by
    have h := congrArg (fun D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) =>
      D.sum (fun _ n => n)) hsplit
    beta_reduce at h
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), ← degree_eq_sum, hdeg, hE₁, hE₂,
      ← Finsupp.sum_finset_sum_index (fun _ => rfl) (fun _ _ _ => rfl),
      ← Finsupp.sum_finset_sum_index (fun _ => rfl) (fun _ _ _ => rfl)] at h
    simp only [Finsupp.sum_single_index, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, nsmul_eq_mul, mul_one] at h
    push_cast at h
    omega
  have hE₃0 : E₃ = 0 := by
    by_contra hne
    obtain ⟨W, hW⟩ : ∃ W, E₃ W ≠ 0 := by
      by_contra h'; push Not at h'; exact hne (Finsupp.ext h')
    have hpos : 0 < E₃.sum (fun _ n => n) := by
      rw [Finsupp.sum]
      exact Finset.sum_pos' (fun b _ => hE₃ b)
        ⟨W, Finsupp.mem_support_iff.mpr hW, lt_of_le_of_ne (hE₃ W) (Ne.symm hW)⟩
    omega
  rw [hsplit, hE₃0, add_zero, hE₁, hE₂]

p2m_export "ModularCurve.PlaceSpecialization" "exists_eq_sum_add_sum_of_mapDomain_fstDiv_sndDiv"
end ModularCurve.PlaceSpecialization

namespace CHARTOKB

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve.PlaceSpecialization"

set_option autoImplicit false

theorem exists_isGoodDiv_mk_glueData_eq_zero_pic0Mk_eq_of_pin
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {W : Finset (Place k (modularFunctionFieldC k 1))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
    (PIN : ∀ {d₁ d₂ : ℕ}
      (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
      (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
      (_hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (_hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
      (_hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
      (_hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
      {T₁ T₂ : Finset (Place k ↥(modularFunctionFieldC k 1))}
      (_hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v)
      (_hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v)
      (_hT₁W : Disjoint T₁ W)
      (_hT₁aff : ∀ v ∈ T₁, IsAffineGeomPlace k 1 v) (_hT₂aff : ∀ v ∈ T₂, IsAffineGeomPlace k 1 v)
      (_hT₁sm : ∀ v ∈ T₁, ∃ c : k × k, IsCentreOf k 1 c v ∧
        (∀ v' : Place k ↥(modularFunctionFieldC k 1), IsCentreOf k 1 c v' → v' = v) ∧
        (v.ord (jGeomGen k 1 - algebraMap k ↥(modularFunctionFieldC k 1) c.1) = 1 ∨
          v.ord (jNGeomGen k 1 - algebraMap k ↥(modularFunctionFieldC k 1) c.2) = 1))
      (_hT₂sm : ∀ v ∈ T₂, ∃ c : k × k, IsCentreOf k 1 c v ∧
        (∀ v' : Place k ↥(modularFunctionFieldC k 1), IsCentreOf k 1 c v' → v' = v) ∧
        (v.ord (jGeomGen k 1 - algebraMap k ↥(modularFunctionFieldC k 1) c.1) = 1 ∨
          v.ord (jNGeomGen k 1 - algebraMap k ↥(modularFunctionFieldC k 1) c.2) = 1))
      (_hT₁gen : ∀ i, (P.reduceFst (Q₁ i)).evalAt (jGeomGen k 1) ^ (q ^ 2) ≠ (P.reduceFst (Q₁ i)).evalAt (jGeomGen k 1) ∧
        (P.reduceFst (Q₁ i)).evalAt (jNGeomGen k 1) ^ (q ^ 2) ≠ (P.reduceFst (Q₁ i)).evalAt (jNGeomGen k 1))
      (_hT₂gen : ∀ j, (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k 1) ^ (q ^ 2) ≠ (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k 1) ∧
        (P.reduceSnd (Q₂ j)).evalAt (jNGeomGen k 1) ^ (q ^ 2) ≠ (P.reduceSnd (Q₂ j)).evalAt (jNGeomGen k 1))
      (_hgp₁ : ∀ h : ↥(modularFunctionFieldC k 1),
        (∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
        (∀ w ∈ W, w.HasValue h 0) → h = 0)
      (_hgp₂ : ∀ h : ↥(modularFunctionFieldC k 1),
        (∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
        ∃ c : k, h = algebraMap k ↥(modularFunctionFieldC k 1) c)
      (_hdeg : d₁ + d₂ = genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
      (Qs : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (_hQs : P.IsStrictFst Qs)
      (_hQs' : ∀ i, P.reduceFst Qs ≠ P.reduceFst (Q₁ i))
      (_hQ₁I : ∀ i, ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₁ i = Q₁ i)
      (_hQ₂I : ∀ j, ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₂ j = Q₂ j)
      (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (_hE0 : 0 ≤ E)
      (f : ↥(modularFunctionFieldBar (1 * q))) (_hf0 : f ≠ 0)
      (_hdivf : ∀ V, (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
        - (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))) V = V.ord f),
      Finsupp.mapDomain P.reduceFst (P.fstDiv E) = ∑ i, Finsupp.single (P.reduceFst (Q₁ i)) (1 : ℤ) ∧
      Finsupp.mapDomain P.reduceSnd (P.sndDiv E) = ∑ j, Finsupp.single (P.reduceSnd (Q₂ j)) (1 : ℤ)) :
    ∃ (D₀ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
      (hadm₀ : P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W)
          (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
        ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W)),
      P.IsGoodDiv (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) ∧
      GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k 1) W)
          ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W)
            (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))), hadm₀⟩ = 0 ∧
      Pic0.mk D₀ = Pic0.mk D := by
  have hqN : ¬ q ∣ 1 := fun h => (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h)
  haveI : NeZero (1 * q) := ⟨by rw [one_mul]; exact (Fact.out : q.Prime).ne_zero⟩
  classical

  haveI hIC : IsCurveOver k ↥(modularFunctionFieldC k 1) :=
    ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField k 1
  haveI hEFT : Algebra.EssFiniteType k ↥(modularFunctionFieldC k 1) := by
    rw [ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC k q 1 hqN]
    exact ModularCurve.essFiniteType_modularFunctionFieldFullC k 1
  obtain ⟨w₀, hw₀⟩ := ModularCurve.ssPlaces_nonempty q 1 hqN k
  have hWne : W.Nonempty := ⟨w₀, (hW w₀).mpr hw₀⟩
  have hC : ConstantsAreBase k ↥(modularFunctionFieldC k 1) :=
    AlgebraicCurve.constantsAreBase_of_deg_eq_one w₀ (IsCurveOver.deg_eq_one_of_isAlgClosed w₀)
  obtain ⟨Kc, hRR⟩ :=
    AlgebraicCurve.exists_weilCanonical_riemannRoch k ↥(modularFunctionFieldC k 1) hC

  have hNk : ((1 : ℕ) : k) ≠ 0 := fun h => hqN ((CharP.cast_eq_zero_iff k q 1).mp h)
  have hsep := ModularCurve.isSeparable_jqNModC_of_natCast_ne_zero k 1 hNk
  have hq2 : 1 < q ^ 2 := Nat.one_lt_pow two_ne_zero (Fact.out : q.Prime).one_lt
  have hXne : (Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero k hq2
  obtain ⟨d₁, d₂, Q₁, Q₂, T₁, T₂, Qs, hd₁, hd₂, hQ₁, hQ₂, hinj₁, hinj₂, hT₁, hT₂, hT₁W, hT₁B, hT₂B,
      hT₁aff, hT₂aff, hT₁sm, hT₂sm, hgp₁, hgp₂, hQs, hQs', hQ₁I, hQ₂I⟩ :=
    ModularCurve.PlaceSpecialization.exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq
      P hqN W hWne
      (((Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots.toFinset).biUnion
        fun a => (ModularCurve.finite_setOf_ord_jGeomGen_sub_pos k 1 hsep a).toFinset)
      Kc (genusFF k ↥(modularFunctionFieldC k 1)) hRR
  have hjB : ∀ (v : Place k ↥(modularFunctionFieldC k 1)) (c : k × k), IsCentreOf k 1 c v →
      v ∉ (((Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots.toFinset).biUnion
        fun a => (ModularCurve.finite_setOf_ord_jGeomGen_sub_pos k 1 hsep a).toFinset) →
      v.evalAt (jGeomGen k 1) ^ (q ^ 2) ≠ v.evalAt (jGeomGen k 1) ∧
        v.evalAt (jNGeomGen k 1) ^ (q ^ 2) ≠ v.evalAt (jNGeomGen k 1) := by
    intro v c hc hvB
    rw [ModularCurve.jNGeomGen_one k, hc.evalAt_jGeomGen]
    have key : c.1 ^ (q ^ 2) ≠ c.1 := by
      intro heq
      apply hvB
      rw [Finset.mem_biUnion]
      refine ⟨c.1, ?_, ?_⟩
      · rw [Multiset.mem_toFinset, Polynomial.mem_roots hXne, Polynomial.IsRoot.def, Polynomial.eval_sub,
          Polynomial.eval_pow, Polynomial.eval_X, heq, sub_self]
      · rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
        exact hc.1
    exact ⟨key, key⟩
  have hT₁gen : ∀ i, (P.reduceFst (Q₁ i)).evalAt (jGeomGen k 1) ^ (q ^ 2) ≠ (P.reduceFst (Q₁ i)).evalAt (jGeomGen k 1) ∧
      (P.reduceFst (Q₁ i)).evalAt (jNGeomGen k 1) ^ (q ^ 2) ≠ (P.reduceFst (Q₁ i)).evalAt (jNGeomGen k 1) := fun i => by
    have hv : P.reduceFst (Q₁ i) ∈ T₁ := (hT₁ _).mpr ⟨i, rfl⟩
    obtain ⟨c, hc, -, -⟩ := hT₁sm _ hv
    exact hjB _ c hc (Finset.disjoint_left.mp hT₁B hv)
  have hT₂gen : ∀ j, (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k 1) ^ (q ^ 2) ≠ (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k 1) ∧
      (P.reduceSnd (Q₂ j)).evalAt (jNGeomGen k 1) ^ (q ^ 2) ≠ (P.reduceSnd (Q₂ j)).evalAt (jNGeomGen k 1) := fun j => by
    have hv : P.reduceSnd (Q₂ j) ∈ T₂ := (hT₂ _).mpr ⟨j, rfl⟩
    obtain ⟨c, hc, -, -⟩ := hT₂sm _ hv
    exact hjB _ c hc (Finset.disjoint_left.mp hT₂B hv)

  have hgen := ModularCurve.genusFF_modularFunctionFieldBar_mul_add_one_eq_of_ssPlaces q 1 hqN k W hW
  have hdeg : d₁ + d₂ = genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) := by
    omega

  set E₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) :=
    ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) with hE₀
  have hE₀deg : Divisor.degree (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))) E₀
      = ((d₁ + d₂ : ℕ) : ℤ) := by
    rw [hE₀, map_add, map_sum, map_sum]
    simp only [Divisor.degree_single, ModularCurve.deg_eq_one_modularFunctionFieldBar, Nat.cast_one,
      mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  obtain ⟨E, hE0, hEdeg, hEdz, hEx⟩ :=
    ModularCurve.exists_effective_pic0Mk_sub_eq_of_genusFF_le_degree (1 * q) E₀
      (by rw [hE₀deg]; exact_mod_cast hdeg.ge) (Pic0.mk D)

  have hprin : (E - E₀ - (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))) ∈
      Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))) := by
    have h := hEx
    rw [Pic0.mk, Pic0.mk, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
    have h' : -(E - E₀) + (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) ∈
        Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))) := h
    have := neg_mem h'
    convert this using 1
    abel
  obtain ⟨f, hf0, hdivf⟩ := hprin

  obtain ⟨hpush₁, hpush₂⟩ := PIN Q₁ Q₂ hQ₁ hQ₂ hinj₁ hinj₂ hT₁ hT₂ hT₁W hT₁aff hT₂aff hT₁sm hT₂sm hT₁gen hT₂gen
    hgp₁ hgp₂ hdeg Qs hQs hQs' hQ₁I hQ₂I E hE0 f hf0 (by rw [hE₀] at hdivf; exact hdivf)

  have hEdeg' : Divisor.degree (K := AlgebraicClosure ℚ) E = ((d₁ + d₂ : ℕ) : ℤ) := hEdeg.trans hE₀deg
  obtain ⟨Q₁', Q₂', hQ₁', hQ₂', hred₁, hred₂, hEQ⟩ :=
    P.exists_eq_sum_add_sum_of_mapDomain_fstDiv_sndDiv E hE0 Q₁ Q₂ hinj₁ hinj₂ hpush₁ hpush₂ hEdeg'

  have hdeg0 : (((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
      - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) :
      Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) ∈
        Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))) := by
    rw [← hEQ, ← hE₀]; exact hEdz
  have hmkD : Pic0.mk ⟨_, hdeg0⟩ = Pic0.mk D := by
    have heq : (⟨_, hdeg0⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
        = ⟨E - E₀, hEdz⟩ := by
      apply Subtype.ext
      simp [hEQ, hE₀]
    rw [heq]
    exact hEx
  exact exists_isGoodDiv_glueData_mk_eq_zero_of_pic0Mk_eq P _ D Q₁ Q₁' Q₂ Q₂' hQ₁ hQ₁' hQ₂ hQ₂' hred₁ hred₂ hdeg0 hmkD

end CHARTOKB

open _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.ModularCurve.PlaceSpecialization in
theorem solution
    {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {W : Finset (Place k (modularFunctionFieldC k 1))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (dat : R.AnnulusDatumQ W)
    (hwidth : ∀ w ∈ W, 1 ≤ dat.width w)
    (hwidthj : ∀ w ∈ W, dat.width w = jWidth (w.evalAt (jGeomGen k 1)))
    (hdepthQ : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
        (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
        P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
          0 < dat.depthQ V ∧ dat.depthQ V < dat.width w ∧ (dat.coord w hw).yDepth V ^ (dat.depthQ V).den =
            A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (dat.depthQ V).num.toNat)
    (hdepthσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        dat.depthQ (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V) = dat.depthQ V)
    (hcusp : dat.cusp ∉ W) (hcuspφ : arithFrobC q k 1 • dat.cusp = dat.cusp)
    (hunif : ∀ w ∈ W,
      (∀ v : Place k (modularFunctionFieldC k 1),
          ((Finsupp.single w (1 : ℤ) - Finsupp.single dat.cusp 1 :
              Divisor k ↥(modularFunctionFieldC k 1)) v) = v.ord (dat.unifFst w)) ∧
      (∀ v : Place k (modularFunctionFieldC k 1),
          ((Finsupp.single (arithFrobC q k 1 • w) (1 : ℤ) - Finsupp.single dat.cusp 1 :
              Divisor k ↥(modularFunctionFieldC k 1)) v) = v.ord (dat.unifSnd w)))
    (hKfix : ∀ w ∈ W, ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ dat.K w, σ z = z)
    [hK : ∀ w : Place k (modularFunctionFieldC k 1), FiniteDimensional ℚ ↥(dat.K w)]
    (ϖ : ∀ w : Place k (modularFunctionFieldC k 1), ↥(NodeLocalized.coeffSubring A (dat.K w)))
    (hϖ : ∀ w ∈ W, ∀ d : ↥(NodeLocalized.coeffSubring A (dat.K w)),
      NodeLocalized.redRestrict red (dat.K w) d = 0 ↔ ∃ d', d = ϖ w * d')
    (eK : Place k (modularFunctionFieldC k 1) → ℕ) (heK : ∀ w ∈ W, 1 ≤ eK w)
    (ε : ∀ w : Place k (modularFunctionFieldC k 1), ↥(NodeLocalized.coeffSubring A (dat.K w)))
    (hε : ∀ w ∈ W, IsUnit (ε w))
    (hqϖ : ∀ w ∈ W, ((q : ℕ) : ↥(NodeLocalized.coeffSubring A (dat.K w))) = ϖ w ^ eK w * ε w)
    (hε1 : ∀ w ∈ W, NodeLocalized.redRestrict red (dat.K w) (ε w) = 1)
    (u : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W), ↥(R.nodeIntegersOver (dat.K w) w))
    (hu : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W), IsUnit (u w hw) ∧
        (dat.coord w hw).x * (dat.coord w hw).y = R.nodeConst (dat.K w) w (ϖ w) ^ (dat.width w * eK w) * u w hw)
    (hmax : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
        (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x, (dat.coord w hw).y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver (dat.K w) w), M.IsMaximal →
          M = Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x, (dat.coord w hw).y})
    (hbr : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
        (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x}).IsPrime ∧
        (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).y}).IsPrime ∧
        (dat.coord w hw).y ∉ Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x} ∧
        (dat.coord w hw).x ∉ Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).y})
    (hnoeth : ∀ w ∈ W, IsNoetherianRing ↥(R.nodeIntegersOver (dat.K w) w))
    (hres : ∀ w ∈ W, ∀ g : ↥(R.nodeIntegersOver (dat.K w) w),
        ∃ o : ↥(NodeLocalized.coeffSubring A (dat.K w)), ¬ IsUnit (g - R.nodeConst (dat.K w) w o))
    (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w)
    (hu0 : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨(u w hw : ↥(modularFunctionFieldBar (1 * q))), (u w hw).2.1⟩) ((dat.u0 w : kˣ) : k))
    (hlam : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q))), (dat.coord w hw).y.2.1⟩
        / dat.unifFst w) ((dat.lam w : kˣ) : k))
    (hmu : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
      (arithFrobC q k 1 • w).HasValue
        (R.nodeResidue₂ w ⟨((dat.coord w hw).x : ↥(modularFunctionFieldBar (1 * q))), (dat.coord w hw).x.2.1⟩
          / dat.unifSnd w) ((dat.mu w : kˣ) : k))
    (X : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
    (hXstab : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • (X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) = X)
    (hXsupp : ∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)
    (a : ProlongationTuple.TwistVector (k := k) W)
    (ha : dat.IsTwistOf a (X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))))
    (hadm : dat.spData a (X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W))
    (hsp : GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k 1) W) ⟨dat.spData a (X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))), hadm⟩ = 0) :
    ∃ (D₂ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
      (hadm₂ : P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) (D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W)),
      P.IsGoodDiv (D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) ∧
      GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k 1) W) ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) (D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))), hadm₂⟩ = 0 ∧
      Pic0.mk D₂ = Pic0.mk X := by
  classical
  have hphi : ∀ w : Place k ↥(modularFunctionFieldC k 1), arithFrobC q k 1 • w = frobOnPlacesGeomLevel k 1 data hKr w :=
    fun w => ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr w
  have hcuspfix : frobOnPlacesGeomLevel k 1 data hKr dat.cusp = dat.cusp := by rw [← hphi]; exact hcuspφ
  have hunif₁ : ∀ w ∈ W, ∀ v : Place k ↥(modularFunctionFieldC k 1),
      v.ord (dat.unifFst w) = (if v = w then (1 : ℤ) else 0) - (if v = dat.cusp then (1 : ℤ) else 0) := by
    intro w hw v; rw [← (hunif w hw).1 v]; simp [Finsupp.single_apply, eq_comm]
  have hunif₂ : ∀ w ∈ W, ∀ v : Place k ↥(modularFunctionFieldC k 1),
      v.ord (dat.unifSnd w) = (if v = arithFrobC q k 1 • w then (1 : ℤ) else 0) - (if v = dat.cusp then (1 : ℤ) else 0) := by
    intro w hw v; rw [← (hunif w hw).2 v]; simp [Finsupp.single_apply, eq_comm]
  refine CHARTOKB.exists_isGoodDiv_mk_glueData_eq_zero_pic0Mk_eq_of_pin P hW X ?_
  intro d₁ d₂ Q₁ Q₂ hQ₁ hQ₂ hinj₁ hinj₂ T₁ T₂ hT₁ hT₂ hT₁W hT₁aff hT₂aff hT₁sm hT₂sm hT₁gen hT₂gen hgp₁ hgp₂ hdeg Qs hQs hQs' hQ₁I hQ₂I E hE0 f hf0 hdivf
  have hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A := fun c => by
    rw [← R.redBar_residue, map_eq_zero_iff _ R.redBar.injective, IsLocalRing.residue_eq_zero_iff]
  obtain ⟨δ, hA₁, hA₂, hB⟩ :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable
      hq5 P hW R hR hRL hNV hO dat hwidth hwidthj hdepthQ hdepthσ hcusp hcuspφ hunif hKfix ϖ hϖ eK heK ε hε hqϖ hε1 u hu hmax hbr
      hnoeth hres hVI hu0 hlam hmu X hXstab hXsupp a ha hadm hsp Q₁ Q₂ hQ₁ hQ₂ E hE0 f hf0 hdivf hker
  exact ModularCurve.PlaceSpecialization.chartOk_pin_harness P hW R hR hRL hNV hO dat hcusp hwidth hcuspfix hunif₁ hunif₂
    X hXsupp a ha hadm hsp Q₁ Q₂ hQ₁ hQ₂ hinj₁ hinj₂ hT₁ hT₂ hT₁W hT₁aff hT₂aff hT₁sm hT₂sm hT₁gen hT₂gen hgp₁ hgp₂ hdeg Qs hQs hQs'
    hQ₁I hQ₂I E hE0 f hf0 hdivf δ hA₁ hA₂ hB

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable (solution)
