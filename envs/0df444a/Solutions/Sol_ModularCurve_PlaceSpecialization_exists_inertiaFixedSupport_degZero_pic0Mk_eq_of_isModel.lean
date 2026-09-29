-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_inertiaFixedSupport_degZero_pic0Mk_eq_of_isModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/b9abb110-b876-5edc-9c67-fcf306c498cf

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictFst_or_isStrictSnd_iff
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_arithmeticGalois_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceSnd_arithmeticGalois_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_evalAt_ne
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos
import Theorems.Thm_ModularCurve_genusFF_modularFunctionFieldBar_mul_add_one_eq_of_ssPlaces
import Theorems.Thm_ModularCurve_ssPlaces_nonempty
import Theorems.Thm_AlgebraicCurve_exists_weilCanonical_riemannRoch
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_finite_setOf_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ValuationSubring_ReduceAt
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeValueLaw_of_regularityLaw
import Definitions.Def_ModularCurve_AnnulusSpecializationLevel
import Definitions.Def_ModularCurve_PlaceWidthChar
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_annulusDatumLevel_laws
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_exists_fixedGood_isTwistOf_sub_of_inertiaStable
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_exists_fixedStrict_add_kernelGood_of_isTwistOf_of_inertiaStable
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valueIntegralityLaw_of_orderLawFixed
import Theorems.Thm_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_inertiaStable_pic0Mk_eq_of_inertiaStable_of_isModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_inertiaFixedSupport_degZero_pic0Mk_eq_of_isModel
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsElliptic_tateBase ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.numberField_of_finiteDimensional AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instIsScalarTowerJAdjoin ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.GaussReduction.isLocalHom_constToGauss"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero HahnSeries.ramScale_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.veluPointMap2_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆"
p2m_attr_erase "simp" "ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.Gamma0Pair.map_toCurve"
p2m_attr_erase "simp" "WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.symPoly_zero AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.frobeniusPullbackGeomLevelUnconditional_single"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants"
p2m_attr_erase "simp" "AlgebraicCurve.Place.restrictConstants_toValuationSubring GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatum.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.TwistVector.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.TwistVector.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatum.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.mk.injEq"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

set_option maxHeartbeats 16000000 in
theorem FoldK0.splitting_of_heads
    (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N] (k : Type*) [Field k]
    [CharP k q] (red : A →+* k) (data : ModularPolynomialData q)
    (hKr : KroneckerCongruence q data) (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q) [IsAlgClosed k]
    [DecidableEq k] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hmodel : R.IsModel) (hO : R.OrderLawFixed) (hNR : R.RegularityLaw W)
    (X : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
    (hXst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = X)
    (hXgood : ∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W) :
        ∃ (D₁ D₂ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))),
          (∀ V ∈ (D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).support,
            (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
              (P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)) ∧
          P.IsGoodDiv (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∧
          (∃ hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k N) W) (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
              ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W),
            GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k N) W)
              ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k N) W) (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), hadm⟩ = 0) ∧
          ((X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - D₁ - D₂) ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI := Classical.decEq (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
  have hNV : R.NodeValueLaw W :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.nodeValueLaw_of_regularityLaw P hqN hW R hNR
  have hVI : ∀ w ∈ W, R.ValueIntegralityLaw w := fun w hw =>
    ModularCurve.PlaceSpecialization.ProlongationTuple.valueIntegralityLaw_of_orderLawFixed R hqN hO w ((hW w).mp hw)

  have hAL := ModularCurve.PlaceSpecialization.ProlongationTuple.exists_annulusDatumLevel_laws P hqN hW R hmodel hNR hNV hO hVI
  obtain ⟨dat, hwidth, hwidthc, hdepthQ, hdepthσ, hD1, hunif, hKfix, hK, hrest⟩ := hAL
  obtain ⟨ϖ, eK, ε, u, hϖ, heK, hε, hqϖ, hε1, hu, hmax, hbr, hnoeth, hres, hu0, hlam, hmu⟩ := hrest

  obtain ⟨Dfix, hDfixdeg, hDfixsupp, a, ha⟩ :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.exists_fixedGood_isTwistOf_sub_of_inertiaStable
      P hqN hW R dat hwidth hdepthQ hdepthσ hD1 hKfix X hXst hXgood ∅
  have hDfixdz : Dfix ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))) := by
    rw [Divisor.mem_degZero]; exact hDfixdeg
  have hDfixst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Dfix = Dfix := by
    intro σ hσ
    rw [SemilinearAut.divisor_smul_def, Finsupp.mapDomain_congr (g := id) (fun V hV => (hDfixsupp V hV).1 σ hσ),
      Finsupp.mapDomain_id]
  have hgoodOfFix : ∀ V ∈ Dfix.support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W := by
    intro V hV
    rcases (hDfixsupp V hV).2 with h' | h' | h'
    · exact Or.inl h'.1
    · exact Or.inr (Or.inl h'.1)
    · exact Or.inr (Or.inr h'.1)
  set X' : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))) :=
    ⟨(X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - Dfix, sub_mem X.2 hDfixdz⟩ with hX'
  have hX'st : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (X' : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = X' := by
    intro σ hσ
    show arithmeticGalois (modularFunctionFieldFull (N * q)) σ • ((X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - Dfix) = (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - Dfix
    rw [smul_sub, hXst σ hσ, hDfixst σ hσ]
  have hX'good : ∀ V ∈ (X' : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W := by
    intro V hV
    change V ∈ ((X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - Dfix).support at hV
    rcases Finset.mem_union.mp (Finsupp.support_sub hV) with h | h
    · exact hXgood V h
    · exact hgoodOfFix V h

  obtain ⟨Dt, D₂, hDt, hD₂good, ⟨hadm, hmk⟩, hprin⟩ :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.exists_fixedStrict_add_kernelGood_of_isTwistOf_of_inertiaStable
      P hqN hW R hmodel hNR hNV hO hVI dat hwidth hwidthc hdepthQ hdepthσ hD1 hunif hKfix hK ϖ eK ε u hϖ heK hε hqϖ hε1 hu hmax
      hbr hnoeth hres hu0 hlam hmu X' hX'st hX'good a ha
  refine ⟨⟨Dfix + (Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), add_mem hDfixdz Dt.2⟩, D₂, ?_, hD₂good, ⟨hadm, hmk⟩, ?_⟩
  · intro V hV
    change V ∈ (Dfix + (Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))).support at hV
    rcases Finset.mem_union.mp (Finsupp.support_add hV) with h | h
    · exact ⟨(hDfixsupp V h).1, hgoodOfFix V h⟩
    · refine ⟨(hDt V h).1, ?_⟩
      rcases (hDt V h).2 with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
  · have hre : (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - (Dfix + (Dt : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) - (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) =
        ((X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - Dfix) - Dt - D₂ := by abel
    rw [hre]
    exact hprin

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace GENF

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N₀ : ℕ} [NeZero N₀]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ q}

def Good (P : PlaceSpecialization A q N₀ data hKr k red hα hβ) (W : Finset (Place k (modularFunctionFieldC k N₀))) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) : Prop :=
  P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W

def Fixed (A : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) : Prop :=
  ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • V = V

def NotFixed (A : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) : Prop :=
  ¬ Fixed A q V

theorem isStrictFst_smul_iff (P : PlaceSpecialization A q N₀ data hKr k red hα hβ)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) :
    P.IsStrictFst (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • V) ↔ P.IsStrictFst V := by
  unfold PlaceSpecialization.IsStrictFst
  rw [P.reduceFst_arithmeticGalois_smul σ hσ V, P.reduceSnd_arithmeticGalois_smul σ hσ V]

theorem isStrictSnd_smul_iff (P : PlaceSpecialization A q N₀ data hKr k red hα hβ)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) :
    P.IsStrictSnd (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • V) ↔ P.IsStrictSnd V := by
  unfold PlaceSpecialization.IsStrictSnd
  rw [P.reduceFst_arithmeticGalois_smul σ hσ V, P.reduceSnd_arithmeticGalois_smul σ hσ V]

theorem good_iff (P : PlaceSpecialization A q N₀ data hKr k red hα hβ) (W : Finset (Place k (modularFunctionFieldC k N₀))) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) :
    (P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W) ↔ (P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W) :=
  Iff.rfl

theorem good_smul_iff (P : PlaceSpecialization A q N₀ data hKr k red hα hβ) (W : Finset (Place k (modularFunctionFieldC k N₀)))
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) :
    (P.IsStrictFst (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • V) ∨ P.IsStrictSnd (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • V) ∨ P.reduceFst (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • V) ∈ W) ↔
      (P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W) := by
  rw [isStrictFst_smul_iff P hσ, isStrictSnd_smul_iff P hσ, P.reduceFst_arithmeticGalois_smul σ hσ V]

theorem not_isStrictFst_of_isStrictSnd (P : PlaceSpecialization A q N₀ data hKr k red hα hβ) {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))}
    (h2 : P.IsStrictSnd V) : ¬ P.IsStrictFst V := by
  intro h1; apply h1.2; rw [h1.1, ← h2.1]

theorem exists_eq_of_sum_single_apply_ne_zero {d : ℕ} (Q : Fin d → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)))
    (hV : (∑ i, Finsupp.single (Q i) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) V ≠ 0) : ∃ i, Q i = V := by
  classical
  rw [Finsupp.finset_sum_apply] at hV
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hV
  rw [Finsupp.single_apply] at hi
  split_ifs at hi with h
  · exact ⟨i, h⟩
  · exact absurd rfl hi

theorem one_le_sum_single_apply_self {d : ℕ} (Q : Fin d → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) (i : Fin d) :
    (1 : ℤ) ≤ (∑ i', Finsupp.single (Q i') (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) (Q i) := by
  classical
  rw [Finsupp.finset_sum_apply]
  have h : ∀ i' ∈ (Finset.univ : Finset (Fin d)), (0 : ℤ) ≤ (Finsupp.single (Q i') (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) (Q i) := by
    intro i' _; rw [Finsupp.single_apply]; split_ifs <;> norm_num
  refine le_trans ?_ (Finset.single_le_sum h (Finset.mem_univ i))
  rw [Finsupp.single_eq_same]

theorem sum_single_apply_nonneg {d : ℕ} (Q : Fin d → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) :
    (0 : ℤ) ≤ (∑ i', Finsupp.single (Q i') (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) V := by
  classical
  rw [Finsupp.finset_sum_apply]
  exact Finset.sum_nonneg fun i' _ => by rw [Finsupp.single_apply]; split_ifs <;> norm_num

theorem degree_finset_sum_single (O : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)))) :
    Divisor.degree (∑ V' ∈ O, Finsupp.single V' (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) = O.card := by
  rw [map_sum]
  simp only [Divisor.degree_single, ModularCurve.deg_eq_one_modularFunctionFieldBar (N₀ * q), Nat.cast_one, mul_one,
    Finset.sum_const, nsmul_eq_mul]

theorem smul_sum_single_of_orbit {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) (O : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)))) (hO : ∀ V', V' ∈ O ↔ ∃ τ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) τ • V = V') :
    arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • (∑ V' ∈ O, Finsupp.single V' (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) = ∑ V' ∈ O, Finsupp.single V' (1 : ℤ) := by
  classical
  rw [Finset.smul_sum]
  simp only [SemilinearAut.smul_single]
  refine Finset.sum_nbij (fun V' => arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • V') (fun V' hV' => ?_) (fun a _ b _ h => smul_left_cancel _ h)
    (fun V' hV' => ?_) (fun _ _ => rfl)
  · rw [hO] at hV' ⊢
    obtain ⟨τ, hτ, rfl⟩ := hV'
    exact ⟨σ * τ, mul_mem hσ hτ, by rw [map_mul, mul_smul]⟩
  · rw [Finset.mem_coe, hO] at hV'
    obtain ⟨τ, hτ, rfl⟩ := hV'
    refine ⟨(arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ)⁻¹ • (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) τ • V), ?_, ?_⟩
    · rw [Finset.mem_coe, hO]
      exact ⟨σ⁻¹ * τ, mul_mem (inv_mem hσ) hτ, by rw [map_mul, map_inv, mul_smul]⟩
    · dsimp only
      rw [smul_inv_smul]

set_option maxHeartbeats 12800000 in

theorem exists_fixed_good_rep_of_orbit [IsAlgClosed k] [DecidableEq k]
    (P : PlaceSpecialization A q N₀ data hKr k red hα hβ)
    (hqN : ¬ q ∣ N₀) (R : ProlongationTuple P) (hR : R.IsModel) (hOL : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N₀))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N₀ k)
    (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hsplit : ∀ (X : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * q))))),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) = X) →
      (∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))).support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W) →
      ∃ (D₁ D₂ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * q))))),
        (∀ V ∈ (D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))).support,
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • V = V) ∧
            (P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)) ∧
        P.IsGoodDiv (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) ∧
        (∃ hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k N₀) W) (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)))
            ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N₀) W),
          GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k N₀) W)
            ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k N₀) W) (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))), hadm⟩ = 0) ∧
        ((X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) - D₁ - D₂) ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * q))))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) (hV : P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)
    (O : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))))
    (hO : ∀ V', V' ∈ O ↔ ∃ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • V = V') :
    ∃ D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)),
      (∀ V' ∈ D.support,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • V' = V') ∧
          (P.IsStrictFst V' ∨ P.IsStrictSnd V' ∨ P.reduceFst V' ∈ W)) ∧
      ((∑ V' ∈ O, Finsupp.single V' (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) - D) ∈
          Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * q))) ∧
      ((∑ V' ∈ O, Finsupp.single V' (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) - D) ∈
          Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * q))) := by
  classical

  haveI hIC : IsCurveOver k ↥(modularFunctionFieldC k N₀) :=
    ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField k N₀
  haveI hEFT : Algebra.EssFiniteType k ↥(modularFunctionFieldC k N₀) := by
    rw [ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC k q N₀ hqN]
    exact ModularCurve.essFiniteType_modularFunctionFieldFullC k N₀
  obtain ⟨w₀, hw₀⟩ := ModularCurve.ssPlaces_nonempty q N₀ hqN k
  have hWne : W.Nonempty := ⟨w₀, (hW w₀).mpr hw₀⟩
  have hC : ConstantsAreBase k ↥(modularFunctionFieldC k N₀) :=
    AlgebraicCurve.constantsAreBase_of_deg_eq_one w₀ (IsCurveOver.deg_eq_one_of_isAlgClosed w₀)
  obtain ⟨Kc, hRR⟩ :=
    AlgebraicCurve.exists_weilCanonical_riemannRoch k ↥(modularFunctionFieldC k N₀) hC

  have hNk : ((N₀ : ℕ) : k) ≠ 0 := fun h => hqN ((CharP.cast_eq_zero_iff k q N₀).mp h)
  have hsep := ModularCurve.isSeparable_jqNModC_of_natCast_ne_zero k N₀ hNk
  have hfin0 := ModularCurve.finite_setOf_ord_jGeomGen_sub_pos k N₀ hsep 0
  have hfin1728 := ModularCurve.finite_setOf_ord_jGeomGen_sub_pos k N₀ hsep 1728
  obtain ⟨d₁, d₂, Q₁, Q₂, T₁, T₂, Qs, hd₁, hd₂, hQ₁, hQ₂, hinj₁, hinj₂, hT₁, hT₂, hT₁W, hT₁B, hT₂B,
      hT₁aff, hT₂aff, hT₁sm, hT₂sm, hgp₁, hgp₂, hQs, hQs', hI₁, hI₂⟩ :=
    ModularCurve.PlaceSpecialization.exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq
      P hqN W hWne (hfin0.toFinset ∪ hfin1728.toFinset) Kc (genusFF k ↥(modularFunctionFieldC k N₀)) hRR
  have hjB : ∀ (v : Place k ↥(modularFunctionFieldC k N₀)) (c : k × k), IsCentreOf k N₀ c v →
      v ∉ hfin0.toFinset ∪ hfin1728.toFinset →
      v.evalAt (jGeomGen k N₀) ≠ 0 ∧ v.evalAt (jGeomGen k N₀) ≠ 1728 := by
    intro v c hc hvB
    rw [hc.evalAt_jGeomGen]
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or] at hvB
    refine ⟨fun h0 => hvB.1 ?_, fun h1 => hvB.2 ?_⟩
    · have h := hc.1; rw [h0] at h; exact h
    · have h := hc.1; rw [h1] at h; exact h
  have hj₁ : ∀ i, (P.reduceFst (Q₁ i)).evalAt (jGeomGen k N₀) ≠ 0 ∧
      (P.reduceFst (Q₁ i)).evalAt (jGeomGen k N₀) ≠ 1728 := fun i => by
    have hv : P.reduceFst (Q₁ i) ∈ T₁ := (hT₁ _).mpr ⟨i, rfl⟩
    obtain ⟨c, hc, -, -⟩ := hT₁sm _ hv
    exact hjB _ c hc (fun hB => Finset.disjoint_left.mp hT₁B hv hB)
  have hj₂ : ∀ j, (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k N₀) ≠ 0 ∧
      (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k N₀) ≠ 1728 := fun j => by
    have hv : P.reduceSnd (Q₂ j) ∈ T₂ := (hT₂ _).mpr ⟨j, rfl⟩
    obtain ⟨c, hc, -, -⟩ := hT₂sm _ hv
    exact hjB _ c hc (fun hB => Finset.disjoint_left.mp hT₂B hv hB)

  have hgen := ModularCurve.genusFF_modularFunctionFieldBar_mul_add_one_eq_of_ssPlaces q N₀ hqN k W hW
  have hdeg : d₁ + d₂ = genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)) := by
    omega

  obtain ⟨Qb, Qb₂, hQb, -, -, -, -, -, hQbfix, -⟩ :=
    ModularCurve.PlaceSpecialization.exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq P hqN ∅ 1 0

  set Osum : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)) := ∑ V' ∈ O, Finsupp.single V' (1 : ℤ) with hOsum
  set X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)) := Osum - (O.card : ℤ) • Finsupp.single (Qb 0) (1 : ℤ) with hX
  have hXdeg : X ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * q))) := by
    rw [Divisor.mem_degZero, hX, map_sub, map_zsmul, hOsum, degree_finset_sum_single, Divisor.degree_single,
      ModularCurve.deg_eq_one_modularFunctionFieldBar (N₀ * q)]
    simp
  have hXst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • X = X := by
    intro σ hσ
    rw [hX, smul_sub, hOsum, smul_sum_single_of_orbit hσ V O hO, smul_comm, SemilinearAut.smul_single, hQbfix 0 σ hσ]
  have hVgood : P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W := (good_iff P W V).mpr hV
  have hXgood : ∀ V' ∈ X.support, P.IsStrictFst V' ∨ P.IsStrictSnd V' ∨ P.reduceFst V' ∈ W := by
    intro V' hV'
    rw [Finsupp.mem_support_iff, hX, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul] at hV'
    by_cases h1 : Osum V' = 0
    · rw [h1, zero_sub, neg_ne_zero, mul_ne_zero_iff, Finsupp.single_apply_ne_zero] at hV'
      rw [hV'.2.1]
      exact Or.inl (hQb 0)
    · rw [hOsum, Finsupp.finset_sum_apply] at h1
      obtain ⟨V'', hV''O, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
      rw [Finsupp.single_apply_ne_zero] at hne
      rw [hne.1]
      obtain ⟨τ, hτ, rfl⟩ := (hO V'').mp hV''O
      exact (good_smul_iff P W hτ V).mpr hVgood

  obtain ⟨D₁, D₂, hD₁, hD₂good, ⟨hadm, hmk⟩, hprin⟩ := hsplit ⟨X, hXdeg⟩ hXst hXgood

  obtain ⟨Q₁', Q₂', hQ₁', hQ₂', hred₁, hred₂, hdeg0, hx'⟩ :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv
      hqN hR hW hRL hNV hOL Q₁ Q₂ hQ₁ hQ₂ hinj₁ hinj₂ hT₁ hT₂ hT₁W hT₁aff hT₂aff hgp₁ hgp₂ hdeg D₂ hD₂good hadm hmk

  have hD₁st : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • (D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) = D₁ := by
    intro σ hσ
    rw [SemilinearAut.divisor_smul_def, Finsupp.mapDomain_congr (g := id) (fun V' hV' => (hD₁ V' hV').1 σ hσ), Finsupp.mapDomain_id]
  have hD₂cls : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) - D₂) ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * q))) := by
    intro σ hσ
    have hC := SemilinearAut.smul_mem_principal (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ) hprin
    have : arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) - D₂ = -((arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • (X - D₁ - D₂)) - (X - D₁ - D₂)) := by
      rw [smul_sub, smul_sub, hXst σ hσ, hD₁st σ hσ]; abel
    rw [this]
    exact neg_mem (sub_mem hC hprin)

  set E0 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)) := ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) with hE0
  set E1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)) := ∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) with hE1
  have hE0st : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • E0 = E0 := by
    intro σ hσ
    rw [hE0, smul_add, Finset.smul_sum, Finset.smul_sum]
    simp only [SemilinearAut.smul_single, hI₁ _ σ hσ, hI₂ _ σ hσ]
  have hfixE' : ∀ σ ∈ A.inertiaSubgroupIn ℚ, (∀ i, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • Q₁' i = Q₁' i) ∧ (∀ j, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • Q₂' j = Q₂' j) := by
    intro σ hσ

    have hQ₁'' : ∀ i, P.IsStrictFst (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • Q₁' i) := fun i => (isStrictFst_smul_iff P hσ _).mpr (hQ₁' i)
    have hQ₂'' : ∀ j, P.IsStrictSnd (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • Q₂' j) := fun j => (isStrictSnd_smul_iff P hσ _).mpr (hQ₂' j)
    have hred₁'' : ∀ i, P.reduceFst (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • Q₁' i) = P.reduceFst (Q₁' i) := fun i =>
      P.reduceFst_arithmeticGalois_smul σ hσ _
    have hred₂'' : ∀ j, P.reduceSnd (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • Q₂' j) = P.reduceSnd (Q₂' j) := fun j =>
      P.reduceSnd_arithmeticGalois_smul σ hσ _

    have hinj₁' : Function.Injective fun i => P.reduceFst (Q₁' i) := by
      intro i j h; apply hinj₁; simp only [hred₁] at h; exact h
    have hinj₂' : Function.Injective fun j => P.reduceSnd (Q₂' j) := by
      intro i j h; apply hinj₂; simp only [hred₂] at h; exact h
    have hT₁' : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁' i) = v := fun v => by
      rw [hT₁]; simp only [hred₁]
    have hT₂' : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂' j) = v := fun v => by
      rw [hT₂]; simp only [hred₂]
    have hj₁' : ∀ i, (P.reduceFst (Q₁' i)).evalAt (jGeomGen k N₀) ≠ 0 ∧ (P.reduceFst (Q₁' i)).evalAt (jGeomGen k N₀) ≠ 1728 :=
      fun i => by rw [hred₁]; exact hj₁ i
    have hj₂' : ∀ j, (P.reduceSnd (Q₂' j)).evalAt (jGeomGen k N₀) ≠ 0 ∧ (P.reduceSnd (Q₂' j)).evalAt (jGeomGen k N₀) ≠ 1728 :=
      fun j => by rw [hred₂]; exact hj₂ j
    have hQs'' : ∀ i, P.reduceFst Qs ≠ P.reduceFst (Q₁' i) := fun i => by rw [hred₁]; exact hQs' i

    have hsE1 : arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • E1 = ∑ i, Finsupp.single (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • Q₂' j) (1 : ℤ) := by
      rw [hE1, smul_add, Finset.smul_sum, Finset.smul_sum]; simp only [SemilinearAut.smul_single]
    have hprinE : (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • E1 - E1) ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * q))) := by

      have h1 : ((E1 - E0) - (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)))) ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * q))) := by
        have := (QuotientAddGroup.eq (s := (Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * q)))).addSubgroupOf _)).mp hx'.symm
        rw [AddSubgroup.mem_addSubgroupOf] at this

        have hcoe : ((-D₂ + ⟨E1 - E0, hdeg0⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * q))))) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) = -(D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) + (E1 - E0) := rfl
        rw [hcoe, neg_add_eq_sub] at this
        exact this
      have h2 := SemilinearAut.smul_mem_principal (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ) h1
      have : arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • E1 - E1 = (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • ((E1 - E0) - (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)))) - ((E1 - E0) - D₂)) + (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) - D₂) := by
        rw [smul_sub, smul_sub, hE0st σ hσ]; abel
      rw [this]
      exact add_mem (sub_mem h2 h1) (hD₂cls σ hσ)
    obtain ⟨f, hf, hford⟩ := hprinE
    have hE := ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_evalAt_ne
      hqN hR hW hNV hRL Q₁' (fun i => arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • Q₁' i) Q₂' (fun j => arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • Q₂' j) hQ₁' hQ₁'' hQ₂' hQ₂'' hinj₁' hinj₂'
      (fun i => hred₁'' i) (fun j => hred₂'' j) hT₁' hT₂' hT₁W hT₁aff hT₂aff hj₁' hj₂' hgp₁ hgp₂ Qs hQs hQs'' 1 (by norm_num) f hf
      (fun U => by rw [← hford U, ← hsE1, Finsupp.sub_apply]; push_cast; ring)

    rw [← hsE1] at hE
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have hle := one_le_sum_single_apply_self (fun i => arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • Q₁' i) i
      have hmem : (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • E1) (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • Q₁' i) ≠ 0 := by
        rw [hsE1, Finsupp.add_apply]
        have := sum_single_apply_nonneg (fun j => arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • Q₂' j) (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • Q₁' i)
        omega
      rw [hE, Finsupp.add_apply] at hmem
      by_cases hA : (∑ i', Finsupp.single (Q₁' i') (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • Q₁' i) = 0
      · rw [hA, zero_add] at hmem
        obtain ⟨j, hj⟩ := exists_eq_of_sum_single_apply_ne_zero Q₂' _ hmem
        exact absurd ((hj ▸ hQ₂' j : P.IsStrictSnd (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • Q₁' i))) (fun h => not_isStrictFst_of_isStrictSnd P h (hQ₁'' i))
      · obtain ⟨i', hi'⟩ := exists_eq_of_sum_single_apply_ne_zero Q₁' _ hA
        have : i' = i := hinj₁' (by simp only []; rw [← hred₁'' i, ← hi'])
        rw [← hi', this]
    · have hmem : (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • E1) (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • Q₂' j) ≠ 0 := by
        rw [hsE1, Finsupp.add_apply]
        have h1 := sum_single_apply_nonneg (fun i => arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • Q₁' i) (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • Q₂' j)
        have h2 := one_le_sum_single_apply_self (fun j => arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • Q₂' j) j
        omega
      rw [hE, Finsupp.add_apply] at hmem
      by_cases hB : (∑ j', Finsupp.single (Q₂' j') (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • Q₂' j) = 0
      · rw [hB, add_zero] at hmem
        obtain ⟨i, hi⟩ := exists_eq_of_sum_single_apply_ne_zero Q₁' _ hmem
        exact absurd ((hi ▸ hQ₁' i : P.IsStrictFst (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • Q₂' j))) (not_isStrictFst_of_isStrictSnd P (hQ₂'' j))
      · obtain ⟨j', hj'⟩ := exists_eq_of_sum_single_apply_ne_zero Q₂' _ hB
        have : j' = j := hinj₂' (by simp only []; rw [← hred₂'' j, ← hj'])
        rw [← hj', this]

  refine ⟨(O.card : ℤ) • Finsupp.single (Qb 0) (1 : ℤ) + (D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) + (E1 - E0), ?_, ?_, ?_⟩
  ·
    intro V' hV'
    have hcases : (Finsupp.single (Qb 0) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) V' ≠ 0 ∨ (D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) V' ≠ 0 ∨ E1 V' ≠ 0 ∨ E0 V' ≠ 0 := by
      by_contra h; push_neg at h; obtain ⟨a1, a2, a3, a4⟩ := h
      apply Finsupp.mem_support_iff.mp hV'
      rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, a1, a2, a3, a4]; simp
    rcases hcases with h | h | h | h
    · rw [Finsupp.single_apply_ne_zero] at h
      rw [h.1]
      exact ⟨hQbfix 0, Or.inl (hQb 0)⟩
    · exact ⟨(hD₁ V' (Finsupp.mem_support_iff.mpr h)).1, (good_iff P W V').mp (hD₁ V' (Finsupp.mem_support_iff.mpr h)).2⟩
    · rw [hE1, Finsupp.add_apply] at h
      by_cases h1 : (∑ i, Finsupp.single (Q₁' i) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) V' = 0
      · rw [h1, zero_add] at h
        obtain ⟨j, rfl⟩ := exists_eq_of_sum_single_apply_ne_zero Q₂' V' h
        exact ⟨fun σ hσ => (hfixE' σ hσ).2 j, (good_iff P W _).mp (Or.inr (Or.inl (hQ₂' j)))⟩
      · obtain ⟨i, rfl⟩ := exists_eq_of_sum_single_apply_ne_zero Q₁' V' h1
        exact ⟨fun σ hσ => (hfixE' σ hσ).1 i, (good_iff P W _).mp (Or.inl (hQ₁' i))⟩
    · rw [hE0, Finsupp.add_apply] at h
      by_cases h1 : (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) V' = 0
      · rw [h1, zero_add] at h
        obtain ⟨j, rfl⟩ := exists_eq_of_sum_single_apply_ne_zero Q₂ V' h
        exact ⟨hI₂ j, (good_iff P W _).mp (Or.inr (Or.inl (hQ₂ j)))⟩
      · obtain ⟨i, rfl⟩ := exists_eq_of_sum_single_apply_ne_zero Q₁ V' h1
        exact ⟨hI₁ i, (good_iff P W _).mp (Or.inl (hQ₁ i))⟩
  ·
    have h1 : ((E1 - E0) - (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)))) ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * q))) := by
      have := (QuotientAddGroup.eq (s := (Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * q)))).addSubgroupOf _)).mp hx'.symm
      rw [AddSubgroup.mem_addSubgroupOf] at this
      have hcoe : ((-D₂ + ⟨E1 - E0, hdeg0⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * q))))) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) = -(D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) + (E1 - E0) := rfl
      rw [hcoe, neg_add_eq_sub] at this
      exact this
    have : Osum - ((O.card : ℤ) • Finsupp.single (Qb 0) (1 : ℤ) + (D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) + (E1 - E0)) = (X - D₁ - D₂) - ((E1 - E0) - D₂) := by
      rw [hX]; abel
    rw [this]
    exact sub_mem hprin h1
  ·
    have : Osum - ((O.card : ℤ) • Finsupp.single (Qb 0) (1 : ℤ) + (D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) + (E1 - E0)) = X - D₁ - (E1 - E0) := by
      rw [hX]; abel
    rw [this]
    exact sub_mem (sub_mem hXdeg D₁.2) hdeg0

def orbit (A : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) :=
  {V' | ∃ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • V = V'}

theorem self_mem_orbit (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) : V ∈ orbit A q V := ⟨1, one_mem _, by rw [map_one, one_smul]⟩

theorem orbit_subset_support {E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))} (hst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • E = E)
    {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))} (hV : V ∈ E.support) : orbit A q V ⊆ ↑E.support := by
  rintro V' ⟨σ, hσ, rfl⟩
  rw [Finset.mem_coe, Finsupp.mem_support_iff, ← hst σ hσ, SemilinearAut.divisor_smul_apply, inv_smul_smul]
  exact Finsupp.mem_support_iff.mp hV

theorem orbit_finite {E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))} (hst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • E = E)
    {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))} (hV : V ∈ E.support) : (orbit A q V).Finite :=
  (E.support.finite_toSet).subset (orbit_subset_support hst hV)

theorem apply_eq_of_mem_orbit {E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))} (hst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • E = E)
    {V V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))} (hV' : V' ∈ orbit A q V) : E V' = E V := by
  obtain ⟨σ, hσ, rfl⟩ := hV'
  conv_lhs => rw [← hst σ hσ]
  exact SemilinearAut.divisor_smul_apply_smul _ _ _

theorem not_fixed_of_mem_orbit {V V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))} (hV : ¬ Fixed A q V) (hV' : V' ∈ orbit A q V) : ¬ Fixed A q V' := by
  obtain ⟨τ, hτ, rfl⟩ := hV'
  intro hfix
  apply hV
  intro σ hσ
  have h := hfix (τ * σ * τ⁻¹) (mul_mem (mul_mem hτ hσ) (inv_mem hτ))
  rw [map_mul, map_mul, map_inv, mul_smul, mul_smul, inv_smul_smul] at h
  exact smul_left_cancel _ h

theorem smul_orbitSum {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) (hfin : (orbit A q V).Finite) :
    arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • (∑ V' ∈ hfin.toFinset, Finsupp.single V' (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) =
      ∑ V' ∈ hfin.toFinset, Finsupp.single V' (1 : ℤ) := by
  classical
  rw [Finset.smul_sum]
  simp only [SemilinearAut.smul_single]
  refine Finset.sum_nbij (fun V' => arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • V') (fun V' hV' => ?_) (fun a _ b _ h => smul_left_cancel _ h)
    (fun V' hV' => ?_) (fun _ _ => rfl)
  · rw [Set.Finite.mem_toFinset] at hV' ⊢
    obtain ⟨τ, hτ, rfl⟩ := hV'
    exact ⟨σ * τ, mul_mem hσ hτ, by rw [map_mul, mul_smul]⟩
  · rw [Set.Finite.coe_toFinset] at hV' ⊢
    obtain ⟨τ, hτ, rfl⟩ := hV'
    refine ⟨(arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ)⁻¹ • (arithmeticGalois (modularFunctionFieldFull (N₀ * q)) τ • V), ⟨σ⁻¹ * τ, mul_mem (inv_mem hσ) hτ, ?_⟩, ?_⟩
    · rw [map_mul, map_inv, mul_smul]
    · dsimp only
      rw [smul_inv_smul]

open Classical in

theorem exists_fixing_corrector [IsAlgClosed k] [DecidableEq k]
    (P : PlaceSpecialization A q N₀ data hKr k red hα hβ)
    (hqN : ¬ q ∣ N₀) (R : ProlongationTuple P) (hR : R.IsModel) (hOL : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N₀))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N₀ k)
    (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hsplit : ∀ (X : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * q))))),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) = X) →
      (∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))).support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W) →
      ∃ (D₁ D₂ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * q))))),
        (∀ V ∈ (D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))).support,
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • V = V) ∧
            (P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)) ∧
        P.IsGoodDiv (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) ∧
        (∃ hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k N₀) W) (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)))
            ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N₀) W),
          GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k N₀) W)
            ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k N₀) W) (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))), hadm⟩ = 0) ∧
        ((X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) - D₁ - D₂) ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * q))))
    :
    ∀ (n : ℕ) (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))),
      (E.support.filter (NotFixed A q)).card ≤ n →
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • E = E) →
      (∀ V ∈ E.support, Good P W V) →
      ∃ C : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)),
        C ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * q))) ∧
        C ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * q))) ∧
        ∀ V ∈ (E - C).support, Fixed A q V ∧ Good P W V := by
  intro n
  induction n with
  | zero =>
    intro E hcard _ hgood
    refine ⟨0, zero_mem _, zero_mem _, fun V hV => ?_⟩
    rw [sub_zero] at hV
    refine ⟨?_, hgood V hV⟩
    by_contra hnf
    have : V ∈ E.support.filter (NotFixed A q) := Finset.mem_filter.mpr ⟨hV, hnf⟩
    rw [Nat.le_zero, Finset.card_eq_zero] at hcard
    rw [hcard] at this
    exact absurd this (Finset.notMem_empty V)
  | succ n ih =>
    intro E hcard hst hgood
    by_cases hex : ∃ V ∈ E.support, ¬ Fixed A q V
    swap
    · push_neg at hex
      exact ⟨0, zero_mem _, zero_mem _, fun V hV => by rw [sub_zero] at hV; exact ⟨hex V hV, hgood V hV⟩⟩
    obtain ⟨V, hVE, hVnf⟩ := hex
    have hfin := orbit_finite hst hVE

    obtain ⟨D, hDfg, hprin, hdeg⟩ := exists_fixed_good_rep_of_orbit P hqN R hR hOL W hW hRL hNV hsplit V (hgood V hVE) hfin.toFinset
      (fun V' => by rw [Set.Finite.mem_toFinset]; rfl)
    set Orb : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)) := ∑ V' ∈ hfin.toFinset, Finsupp.single V' (1 : ℤ) with hOrb
    have hOrb_apply : ∀ V', Orb V' = if V' ∈ orbit A q V then 1 else 0 := by
      intro V'
      rw [hOrb, Finsupp.finset_sum_apply]
      simp only [Finsupp.single_apply]
      rw [Finset.sum_ite_eq' hfin.toFinset V' (fun _ => (1 : ℤ))]
      simp only [Set.Finite.mem_toFinset]

    have hDst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • D = D := by
      intro σ hσ
      rw [SemilinearAut.divisor_smul_def, Finsupp.mapDomain_congr (g := id) (fun V' hV' => (hDfg V' hV').1 σ hσ),
        Finsupp.mapDomain_id]
    set E₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)) := E - E V • (Orb - D) with hE₁
    have hst₁ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • E₁ = E₁ := by
      intro σ hσ
      rw [hE₁, smul_sub, smul_comm, smul_sub, hst σ hσ, hOrb, smul_orbitSum hσ V hfin, ← hOrb, hDst σ hσ]

    have hsub : E₁.support.filter (NotFixed A q) ⊆ (E.support.filter (NotFixed A q)).erase V := by
      intro V' hV'
      obtain ⟨hV'E₁, hV'nf⟩ := Finset.mem_filter.mp hV'
      have hDV' : D V' = 0 := by
        by_contra h
        exact hV'nf ((hDfg V' (Finsupp.mem_support_iff.mpr h)).1)
      rw [Finsupp.mem_support_iff, hE₁, Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.sub_apply, hDV', sub_zero,
        hOrb_apply, smul_eq_mul] at hV'E₁
      by_cases hVo : V' ∈ orbit A q V
      · exfalso; apply hV'E₁
        rw [if_pos hVo, mul_one, apply_eq_of_mem_orbit hst hVo, sub_self]
      · rw [if_neg hVo, mul_zero, sub_zero] at hV'E₁
        refine Finset.mem_erase.mpr ⟨fun h => hVo ?_, Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hV'E₁, hV'nf⟩⟩
        rw [h]; exact self_mem_orbit V
    have hcard₁ : (E₁.support.filter (NotFixed A q)).card ≤ n := by
      have h1 := Finset.card_le_card hsub
      have hVmem : V ∈ E.support.filter (NotFixed A q) := Finset.mem_filter.mpr ⟨hVE, hVnf⟩
      have h2 := Finset.card_erase_of_mem hVmem
      omega
    have hgood₁ : ∀ V' ∈ E₁.support, Good P W V' := by
      intro V' hV'
      by_cases h1 : V' ∈ E.support
      · exact hgood V' h1
      · by_cases h2 : V' ∈ D.support
        · exact (hDfg V' h2).2
        · exfalso
          apply Finsupp.mem_support_iff.mp hV'
          have hEV' : E V' = 0 := Finsupp.notMem_support_iff.mp h1
          have hVo : V' ∉ orbit A q V := fun h => h1 (orbit_subset_support hst hVE h)
          rw [hE₁, Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.sub_apply, Finsupp.notMem_support_iff.mp h2, hEV',
            hOrb_apply, if_neg hVo]
          simp
    obtain ⟨C', hC'p, hC'd, hC'fg⟩ := ih E₁ hcard₁ hst₁ hgood₁
    refine ⟨E V • (Orb - D) + C', add_mem (zsmul_mem hprin _) hC'p, add_mem (zsmul_mem hdeg _) hC'd, fun V' hV' => ?_⟩
    apply hC'fg V'
    rwa [hE₁, sub_sub]

end GENF

theorem FoldK0.orbitRep_fixing
    (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N] (k : Type*) [Field k]
    [CharP k q] (red : A →+* k) (data : ModularPolynomialData q)
    (hKr : KroneckerCongruence q data) (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q) [IsAlgClosed k]
    [DecidableEq k] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hmodel : R.IsModel) (hO : R.OrderLawFixed) (hNR : R.RegularityLaw W)
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hEst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E = E)
    (hEgood : ∀ V ∈ E.support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W) :
        ∃ C : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
          C ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))) ∧
          C ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))) ∧
          ∀ V ∈ (E - C).support,
            (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
              (P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hNV : R.NodeValueLaw W :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.nodeValueLaw_of_regularityLaw P hqN hW R hNR
  obtain ⟨C, hCp, hCd, hCfg⟩ :=
    GENF.exists_fixing_corrector P hqN R hmodel hO W hW hNR hNV
      (fun X hXst hXgood =>
        FoldK0.splitting_of_heads q A N k red data hKr hα hβ hqN P W hW R hmodel hO
          hNR X hXst hXgood)
      _ E le_rfl hEst (fun V hV => hEgood V hV)
  exact ⟨C, hCp, hCd, fun V hV => hCfg V hV⟩

open AlgebraicCurve IsLocalRing ModularCurve

theorem solution
    (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N] (k : Type*) [Field k]
    [CharP k q] (red : A →+* k) (data : ModularPolynomialData q)
    (hKr : KroneckerCongruence q data) (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q) [IsAlgClosed k]
    [DecidableEq k] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W)
    (hO : R.OrderLawFixed) :
      ∀ x : ↥(inertiaInvariants A (N * q)),
        ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
          Pic0.mk D = (x : JZero (N * q)) ∧
          (∀ σ ∈ A.inertiaSubgroupIn ℚ,
            ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
              arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
          (∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
            P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W) := by
  intro x
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  obtain ⟨D₀, hD₀st, hD₀x⟩ := ModularCurve.exists_inertiaStable_degZero_pic0Mk_eq (N * q) (A := A) x

  obtain ⟨D₁, hD₁, hD₁st, hD₁good⟩ :=
    ModularCurve.PlaceSpecialization.exists_inertiaStable_pic0Mk_eq_of_inertiaStable_of_isModel q A N k red data hKr hα hβ
      hqN P W hW R hR hRL hO D₀ hD₀st

  obtain ⟨C, hCp, hCd, hCfg⟩ :=
    FoldK0.orbitRep_fixing q A N k red data hKr hα hβ hqN P W hW R hR hO hRL
      (D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) hD₁st hD₁good
  refine ⟨⟨(D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - C, sub_mem D₁.2 hCd⟩, ?_, ?_, ?_⟩
  ·
    rw [← hD₀x, ← hD₁]
    rw [Pic0.mk, Pic0.mk, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    have e : ((-(⟨(D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - C, sub_mem D₁.2 hCd⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))) + D₁ :
        ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = C := by
      rw [AddSubgroup.coe_add, AddSubgroup.coe_neg]
      show -((D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) - C) + D₁ = C
      abel
    rw [e]
    exact hCp
  · intro σ hσ V hV
    exact (hCfg V hV).1 σ hσ
  · intro V hV
    exact (hCfg V hV).2

end S_ModularCurve_PlaceSpecialization_exists_inertiaFixedSupport_degZero_pic0Mk_eq_of_isModel
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_inertiaFixedSupport_degZero_pic0Mk_eq_of_isModel (solution)
