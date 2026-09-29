-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_depth_comp_depthCompLaw_depthValueLaw_sndDegLaw_surjective_repOfKer_repOfInvariant_principalGood_of_widthPinChar_of_isModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/f827b6b1-50b8-5fe1-8c2a-e8f44b6f0fd0

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeDepth
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_inertiaFixedSupport_degZero_pic0Mk_eq_of_isModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_range_redRestrict_forall_nodeCoordinates_presentation_of_orderLawFixed
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_exists_yDepth_eq_pow_of_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_reduceFst_eq_and_smul_eq_self_and_yDepth_eq_pow_of_orderLawFixed
import Theorems.Thm_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_degree_sndDiv_smul_eq_zero_of_div
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isGoodDiv_pic0Mk_eq_of_comp_eq_zero_of_depthCompLaw_depthValueLaw_repOfInvariant_of_isModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isPrincipal_isGoodDiv_degree_fstDiv_eq_widthSum_widthChar_of_isModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_saturated_of_orderLawFixed
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valueIntegralityLaw_of_orderLawFixed
import Theorems.Thm_ModularCurve_one_le_placeWidthChar_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isStrictFst_and_smul_eq_self
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isStrictSnd_restrictAlong_eq_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_PlaceSpecialization_not_fixed_reduceFst_of_isStrictSnd
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_red_surjective_of_level
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_families_isStrictFst_isStrictSnd_notMem
import Theorems.Thm_ModularCurve_comp_surjective_of_forall_exists_eq_crossingCoord
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_depth_comp_depthCompLaw_depthValueLaw_sndDegLaw_surjective_repOfKer_repOfInvariant_principalGood_of_widthPinChar_of_isModel
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsElliptic_tateBase ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ValuationSubring.instIsAlgClosedResidueField ModularCurve.numberField_of_finiteDimensional AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instIsScalarTowerJAdjoin ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero"
p2m_attr_erase "instance" "ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.GaussReduction.isLocalHom_constToGauss instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne"
p2m_attr_erase "instance" "instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix"
p2m_attr_erase "simp" "ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.veluPointMap2_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply"
p2m_attr_erase "simp" "WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast"
p2m_attr_erase "simp" "ValuationSubring.reduceAt_zero ModularCurve.symPoly_zero AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe ModularCurve.reductionDivAlong_apply"
p2m_attr_erase "simp" "ModularCurve.coe_reductionDegZeroAlong ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.TwistVectorLevel.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.TwistVectorLevel.mk.sizeOf_spec ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatum.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.TwistVector.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.TwistVector.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatum.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.mk.injEq ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂"

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace GramAsm

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)
  (g : SemilinearAut k (modularFunctionFieldC k N))
  (W : Finset (Place k (modularFunctionFieldC k N)))
  (e : Place k (modularFunctionFieldC k N) → ℕ)
  (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ)

def cls (s₀ : ↥(nodePairsOfPlaces g W))
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    componentGroup (widthOfPlaces g W e) :=
  componentGroupProj (widthOfPlaces g W e)
    (P.depthDual g W depth D +
      Divisor.degree (P.sndDiv D) •
        (((e (s₀ : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 : ℕ) : ℤ) •
          crossingCoord s₀))

theorem depthDiv_add (D D' : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    P.depthDiv depth (D + D') = P.depthDiv depth D + P.depthDiv depth D' := by
  unfold PlaceSpecialization.depthDiv
  refine Finsupp.sum_add_index' (fun V => by rw [zero_mul, Finsupp.single_zero]) ?_
  intro V a b
  rw [add_mul, Finsupp.single_add]

theorem depthDual_add (D D' : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    P.depthDual g W depth (D + D')
      = P.depthDual g W depth D + P.depthDual g W depth D' := by
  unfold PlaceSpecialization.depthDual
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [depthDiv_add, Finsupp.add_apply, add_smul]

theorem sndDiv_add (D D' : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    P.sndDiv (D + D') = P.sndDiv D + P.sndDiv D' := by
  classical
  unfold PlaceSpecialization.sndDiv
  exact Finsupp.filter_add

theorem fstDiv_add (D D' : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    P.fstDiv (D + D') = P.fstDiv D + P.fstDiv D' := by
  classical
  unfold PlaceSpecialization.fstDiv
  exact Finsupp.filter_add

set_option maxHeartbeats 64000000 in
theorem cls_add (s₀ : ↥(nodePairsOfPlaces g W))
    (D D' : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    cls P g W e depth s₀ (D + D') = cls P g W e depth s₀ D + cls P g W e depth s₀ D' := by
  have h : P.depthDual g W depth (D + D') +
      Divisor.degree (P.sndDiv (D + D')) •
        (((e (s₀ : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 : ℕ) : ℤ) •
          crossingCoord s₀)
    = (P.depthDual g W depth D +
      Divisor.degree (P.sndDiv D) •
        (((e (s₀ : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 : ℕ) : ℤ) •
          crossingCoord s₀)) +
      (P.depthDual g W depth D' +
      Divisor.degree (P.sndDiv D') •
        (((e (s₀ : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 : ℕ) : ℤ) •
          crossingCoord s₀)) := by
    rw [depthDual_add, sndDiv_add, map_add, add_smul]
    abel
  unfold cls
  rw [h, map_add]

theorem proj_vertex_sub_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℕ) (s₀ s₁ : ι) :
    componentGroupProj w (((w s₀ : ℕ) : ℤ) • crossingCoord s₀ - ((w s₁ : ℕ) : ℤ) • crossingCoord s₁) = 0 := by
  have hmem : (Pi.single s₀ (1 : ℤ) - Pi.single s₁ 1) ∈ characterLattice ι := by
    rw [mem_characterLattice]
    simp [Finset.sum_sub_distrib]
  have hgram : ((w s₀ : ℕ) : ℤ) • crossingCoord s₀ - ((w s₁ : ℕ) : ℤ) • crossingCoord s₁
      = gramMap w ⟨_, hmem⟩ := by
    apply LinearMap.ext
    intro γ
    rw [gramMap_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      crossingCoord_apply, crossingCoord_apply]
    have key : ∀ (t : ι) (γ' : ι → ℤ),
        ∑ x, ((w x : ℕ) : ℤ) * ((Pi.single t (1 : ℤ) : ι → ℤ) x * γ' x) = w t * γ' t := by
      intro t γ'
      rw [Finset.sum_eq_single t]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    simp only [Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib, key, smul_eq_mul]
  rw [hgram]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ _)

set_option maxHeartbeats 64000000 in
theorem cls_indep (s₀ s₁ : ↥(nodePairsOfPlaces g W))
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    cls P g W e depth s₀ D = cls P g W e depth s₁ D := by
  classical
  unfold cls
  rw [← sub_eq_zero, ← map_sub, add_sub_add_left_eq_sub, ← smul_sub, LinearMap.map_smul_of_tower]
  have h0 := proj_vertex_sub_eq_zero (widthOfPlaces g W e) s₀ s₁
  rw [widthOfPlaces_apply, widthOfPlaces_apply] at h0
  rw [h0]
  exact smul_zero _

theorem subsingleton_componentGroup {ι : Type*} [Fintype ι] [IsEmpty ι] (w : ι → ℕ) :
    Subsingleton (componentGroup w) := by
  infer_instance

theorem cls_zero (s₀ : ↥(nodePairsOfPlaces g W)) :
    cls P g W e depth s₀ 0 = 0 := by
  have h := cls_add P g W e depth s₀ 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

theorem cls_sub (s₀ : ↥(nodePairsOfPlaces g W))
    (D D' : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    cls P g W e depth s₀ (D - D') = cls P g W e depth s₀ D - cls P g W e depth s₀ D' := by
  have h := cls_add P g W e depth s₀ (D - D') D'
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

def AdmW (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : Prop :=
  ∀ V ∈ D.support,
    P.IsStrictFst V ∨ P.IsStrictSnd V ∨
      (P.reduceFst V ∈ W ∧
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V)

def Adm (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : Prop :=
  ∀ V ∈ D.support,
    (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
      (P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)

theorem admW_of_adm {D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h : Adm P W D) : AdmW P W D := by
  intro V hV
  obtain ⟨hfix, h'⟩ := h V hV
  rcases h' with h' | h' | h'
  · exact Or.inl h'
  · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr ⟨h', hfix⟩)

theorem admW_of_isGoodDiv {D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h : P.IsGoodDiv D) : AdmW P W D := by
  intro V hV
  rcases h V hV with h' | h'
  · exact Or.inl h'
  · exact Or.inr (Or.inl h')

theorem admW_add [DecidableEq (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))]
    {D D' : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h : AdmW P W D) (h' : AdmW P W D') : AdmW P W (D + D') := by
  intro V hV
  rcases Finset.mem_union.mp (Finsupp.support_add hV) with h1 | h1
  · exact h V h1
  · exact h' V h1

theorem admW_neg {D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h : AdmW P W D) : AdmW P W (-D) := by
  intro V hV
  rw [Finsupp.support_neg] at hV
  exact h V hV

theorem admW_sub {D D' : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h : AdmW P W D) (h' : AdmW P W D') : AdmW P W (D - D') := by
  classical
  rw [sub_eq_add_neg]; exact admW_add P W h (admW_neg P W h')

theorem adm_add [DecidableEq (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))]
    {D D' : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h : Adm P W D) (h' : Adm P W D') : Adm P W (D + D') := by
  intro V hV
  rcases Finset.mem_union.mp (Finsupp.support_add hV) with h1 | h1
  · exact h V h1
  · exact h' V h1

theorem adm_zero : Adm P W (0 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) := by
  intro V hV
  simp at hV

theorem not_isStrictSnd_of_isStrictFst {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h1 : P.IsStrictFst V) : ¬ P.IsStrictSnd V := fun h2 =>
  h1.2 (by rw [h1.1, ← h2.1])

theorem pair_mem_degZero (V₁ V₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    (Finsupp.single V₂ (1 : ℤ) - Finsupp.single V₁ 1 :
        Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∈
      Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))) := by
  rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single,
    deg_eq_one_modularFunctionFieldBar, deg_eq_one_modularFunctionFieldBar]
  simp

theorem mk_mem_inertiaInvariants
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
    (hD : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (N * q)) σ •
          (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) = D) :
    Pic0.mk D ∈ inertiaInvariants A (N * q) := by
  rw [mem_inertiaInvariants]
  intro σ hσ
  rw [galois_smul_pic0_def, SemilinearAut.pic0_smul_mk]
  congr 1
  apply Subtype.ext
  rw [SemilinearAut.coe_degZeroSMulHom]
  exact hD σ hσ

theorem support_pair_subset {V₁ V₂ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hV : V ∈ (Finsupp.single V₂ (1 : ℤ) - Finsupp.single V₁ 1 :
        Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).support) :
    V = V₂ ∨ V = V₁ := by
  classical
  rw [sub_eq_add_neg] at hV
  rcases Finset.mem_union.mp (Finsupp.support_add hV) with h | h
  · exact Or.inl (Finset.mem_singleton.mp (Finsupp.support_single_subset h))
  · rw [Finsupp.support_neg] at h
    exact Or.inr (Finset.mem_singleton.mp (Finsupp.support_single_subset h))

theorem pair_fixed {V₁ V₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h₁ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V₁ = V₁)
    (h₂ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V₂ = V₂) :
    ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      arithmeticGalois (modularFunctionFieldFull (N * q)) σ •
        (Finsupp.single V₂ (1 : ℤ) - Finsupp.single V₁ 1 :
          Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
      = Finsupp.single V₂ (1 : ℤ) - Finsupp.single V₁ 1 := by
  intro σ hσ
  rw [smul_sub, SemilinearAut.smul_single, SemilinearAut.smul_single, h₂ σ hσ, h₁ σ hσ]

theorem fst_mem_W (s : ↥(nodePairsOfPlaces g W)) :
    (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 ∈ W :=
  fst_mem_of_mem_nodePairsOfPlaces s.2

theorem depthDiv_apply_eq_zero_of_forall_ne
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (w : Place k (modularFunctionFieldC k N))
    (h : ∀ V ∈ D.support, P.reduceFst V ≠ w) :
    P.depthDiv depth D w = 0 := by
  classical
  unfold PlaceSpecialization.depthDiv
  rw [Finsupp.sum_apply]
  refine Finset.sum_eq_zero fun V hV => ?_
  show (Finsupp.single (P.reduceFst V) (D V * (depth V : ℤ))) w = 0
  rw [Finsupp.single_apply, if_neg (h V hV)]

theorem depthDual_eq_zero_of_forall_not_mem
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (h : ∀ V ∈ D.support, P.reduceFst V ∉ W) :
    P.depthDual g W depth D = 0 := by
  unfold PlaceSpecialization.depthDual
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [depthDiv_apply_eq_zero_of_forall_ne P depth D _ (fun V hV hVs => h V hV (hVs ▸ fst_mem_W g W s)),
    zero_smul]

theorem reduceFst_not_mem_of_strict
    (hWφ : ∀ w ∈ W, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w)
    {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hV : P.IsStrictFst V ∨ P.IsStrictSnd V) : P.reduceFst V ∉ W := by
  intro hmem
  rcases hV with hV | hV
  · exact hV.2 (hWφ _ hmem)
  · exact not_fixed_reduceFst_of_isStrictSnd P V hV (hWφ _ hmem)

set_option maxHeartbeats 64000000 in
theorem cls_of_isGoodDiv
    (hWφ : ∀ w ∈ W, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w)
    (s₀ : ↥(nodePairsOfPlaces g W))
    {D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hD : P.IsGoodDiv D) :
    cls P g W e depth s₀ D =
      Divisor.degree (P.sndDiv D) • componentGroupProj (widthOfPlaces g W e)
        ((((e (s₀ : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 : ℕ) : ℤ) •
          crossingCoord s₀)) := by
  unfold cls
  rw [depthDual_eq_zero_of_forall_not_mem P g W depth D
      (fun V hV => reduceFst_not_mem_of_strict P W hWφ (hD V hV)), zero_add, map_zsmul]

theorem sndDiv_pair {V₁ V₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h2 : P.IsStrictSnd V₂) (h1 : ¬ P.IsStrictSnd V₁) :
    P.sndDiv (Finsupp.single V₂ 1 - Finsupp.single V₁ 1) = Finsupp.single V₂ 1 := by
  classical
  unfold PlaceSpecialization.sndDiv
  rw [Finsupp.filter_sub, Finsupp.filter_single_of_pos _ h2, Finsupp.filter_single_of_neg _ h1, sub_zero]

theorem sndDiv_pair_eq_zero {V₁ V₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h2 : ¬ P.IsStrictSnd V₂) (h1 : ¬ P.IsStrictSnd V₁) :
    P.sndDiv (Finsupp.single V₂ 1 - Finsupp.single V₁ 1) = 0 := by
  classical
  unfold PlaceSpecialization.sndDiv
  rw [Finsupp.filter_sub, Finsupp.filter_single_of_neg _ h2, Finsupp.filter_single_of_neg _ h1, sub_zero]

set_option maxHeartbeats 64000000 in
theorem cls_strict_pair
    (hWφ : ∀ w ∈ W, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w)
    {V₁ V₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hV₁ : P.IsStrictFst V₁) (hV₂ : P.IsStrictSnd V₂)
    (s₀ : ↥(nodePairsOfPlaces g W)) :
    cls P g W e depth s₀ (Finsupp.single V₂ 1 - Finsupp.single V₁ 1)
      = componentGroupProj (widthOfPlaces g W e)
          (((widthOfPlaces g W e s₀ : ℕ) : ℤ) • crossingCoord s₀) := by
  have hgood : P.IsGoodDiv (Finsupp.single V₂ 1 - Finsupp.single V₁ 1) := by
    intro V hV
    rcases support_pair_subset (q := q) hV with rfl | rfl
    · exact Or.inr hV₂
    · exact Or.inl hV₁
  rw [cls_of_isGoodDiv P g W e depth hWφ s₀ hgood,
    sndDiv_pair P hV₂ (not_isStrictSnd_of_isStrictFst P hV₁), Divisor.degree_single,
    deg_eq_one_modularFunctionFieldBar, widthOfPlaces_apply]
  simp

set_option maxHeartbeats 64000000 in
theorem depthDual_node_pair
    {V₀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hV₀ : P.reduceFst V₀ ∉ W) (s : ↥(nodePairsOfPlaces g W))
    (hV : P.reduceFst V = (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1) :
    P.depthDual g W depth (Finsupp.single V 1 - Finsupp.single V₀ 1) = (depth V : ℤ) • crossingCoord s := by
  classical
  have happ : ∀ w ∈ W, P.depthDiv depth (Finsupp.single V 1 - Finsupp.single V₀ 1) w =
      if P.reduceFst V = w then (depth V : ℤ) else 0 := by
    intro w hw
    have h0 : P.reduceFst V₀ ≠ w := fun h => hV₀ (h ▸ hw)
    unfold PlaceSpecialization.depthDiv
    rw [sub_eq_add_neg, ← Finsupp.single_neg,
      Finsupp.sum_add_index' (fun V => by rw [zero_mul, Finsupp.single_zero])
        (fun V a b => by rw [add_mul, Finsupp.single_add]),
      Finsupp.sum_single_index (by rw [zero_mul, Finsupp.single_zero]),
      Finsupp.sum_single_index (by rw [zero_mul, Finsupp.single_zero]),
      Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply, one_mul,
      if_neg h0, add_zero]
  unfold PlaceSpecialization.depthDual
  rw [Finset.sum_eq_single s]
  · rw [happ _ (fst_mem_W g W s), if_pos hV]
  · intro t _ hts
    rw [happ _ (fst_mem_W g W t), if_neg, zero_smul]
    intro h
    apply hts
    apply (nodeEquivOfPlaces g W).symm.injective
    apply Subtype.ext
    rw [coe_nodeEquivOfPlaces_symm_apply, coe_nodeEquivOfPlaces_symm_apply, ← h, hV]
  · intro h; exact absurd (Finset.mem_univ s) h

set_option maxHeartbeats 64000000 in
theorem cls_node_pair
    {V₀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hV₀W : P.reduceFst V₀ ∉ W) (hV₀s : ¬ P.IsStrictSnd V₀) (hVs : ¬ P.IsStrictSnd V)
    (s s₀ : ↥(nodePairsOfPlaces g W))
    (hV : P.reduceFst V = (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1) :
    cls P g W e depth s₀ (Finsupp.single V 1 - Finsupp.single V₀ 1)
      = (depth V : ℤ) • componentGroupProj (widthOfPlaces g W e) (crossingCoord s) := by
  unfold cls
  rw [depthDual_node_pair P g W depth hV₀W s hV, sndDiv_pair_eq_zero P hVs hV₀s, map_zero, zero_smul,
    add_zero, map_zsmul]

end GramAsm

namespace GramAsm

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

theorem fstDiv_add_sndDiv_of_isGoodDiv {G : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hgood : P.IsGoodDiv G) : P.fstDiv G + P.sndDiv G = G := by
  classical
  ext V
  unfold PlaceSpecialization.fstDiv PlaceSpecialization.sndDiv
  rw [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.filter_apply]
  by_cases hV : V ∈ G.support
  · rcases hgood V hV with h | h
    · rw [if_pos h, if_neg (not_isStrictSnd_of_isStrictFst P h), add_zero]
    · have h' : ¬ P.IsStrictFst V := fun h' => not_isStrictSnd_of_isStrictFst P h' h
      rw [if_neg h', if_pos h, zero_add]
  · rw [Finsupp.notMem_support_iff.mp hV]
    simp

theorem degree_eq_zero_of_isPrincipal {G : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hpr : G.IsPrincipal) : G.degree = 0 := by
  obtain ⟨f, hf, hG⟩ := hpr
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  obtain ⟨D, hD, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) f hf
  have : G = D := Finsupp.ext fun V => by rw [hG V, hD V]
  rw [this, hdeg]

theorem degree_sndDiv_eq_neg {G : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hpr : G.IsPrincipal) (hgood : P.IsGoodDiv G) : (P.sndDiv G).degree = -(P.fstDiv G).degree := by
  have h := congrArg Divisor.degree (fstDiv_add_sndDiv_of_isGoodDiv P hgood)
  rw [map_add, degree_eq_zero_of_isPrincipal hpr] at h
  linarith

end GramAsm

namespace GramAsm

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)
  (g : SemilinearAut k (modularFunctionFieldC k N))
  (W : Finset (Place k (modularFunctionFieldC k N)))
  (e : Place k (modularFunctionFieldC k N) → ℕ)
  (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ)
  (s₀ : ↥(nodePairsOfPlaces g W))

set_option maxHeartbeats 64000000 in

theorem exists_comp_of_rep
    (rep : ↥(inertiaInvariants A (N * q)) →
      ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
    (hrep_mk : ∀ x, Pic0.mk (rep x) = (x : JZero (N * q)))
    (hrep_adm : ∀ x, AdmW P W (rep x : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
    (hwd : ∀ (D₁ D₂ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))),
      Pic0.mk D₁ = Pic0.mk D₂ →
      AdmW P W (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) →
      AdmW P W (D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) →
      cls P g W e depth s₀ (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
        = cls P g W e depth s₀ (D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) :
    ∃ comp : ↥(inertiaInvariants A (N * q)) →+ componentGroup (widthOfPlaces g W e),
      ∀ (x : ↥(inertiaInvariants A (N * q)))
        (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))),
        Pic0.mk D = (x : JZero (N * q)) →
        AdmW P W (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) →
        comp x = cls P g W e depth s₀ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) := by
  classical
  have hcompD : ∀ (x : ↥(inertiaInvariants A (N * q)))
      (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))),
      Pic0.mk D = (x : JZero (N * q)) →
      AdmW P W (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) →
      cls P g W e depth s₀ (rep x : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
        = cls P g W e depth s₀ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :=
    fun x D hD hD' => hwd (rep x) D ((hrep_mk x).trans hD.symm) (hrep_adm x) hD'
  refine ⟨{ toFun := fun x =>
              cls P g W e depth s₀ (rep x : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
            map_zero' := ?_,
            map_add' := ?_ }, fun x D hD hD' => hcompD x D hD hD'⟩
  · show cls P g W e depth s₀ (rep 0 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) = 0
    rw [hcompD 0 0 (by rw [Pic0.mk_zero, ZeroMemClass.coe_zero]) (admW_of_adm P W (adm_zero P W))]
    exact cls_zero P g W e depth s₀
  · intro x y
    show cls P g W e depth s₀ (rep (x + y) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      = cls P g W e depth s₀ (rep x : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
        + cls P g W e depth s₀ (rep y : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    rw [hcompD (x + y) (rep x + rep y) (by rw [Pic0.mk_add, hrep_mk, hrep_mk, AddMemClass.coe_add])
        (admW_add P W (hrep_adm x) (hrep_adm y))]
    exact cls_add P g W e depth s₀ _ _

variable (comp : ↥(inertiaInvariants A (N * q)) →+ componentGroup (widthOfPlaces g W e))
  (hcomp : ∀ (x : ↥(inertiaInvariants A (N * q)))
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))),
    Pic0.mk D = (x : JZero (N * q)) →
    AdmW P W (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) →
    comp x = cls P g W e depth s₀ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))

include hcomp in
set_option maxHeartbeats 64000000 in

theorem depthCompLaw_of_hcomp : P.DepthCompLaw g W e depth comp := by
  intro D hH hD s₁ hs₁
  rw [hcomp ⟨Pic0.mk D, hH⟩ D rfl (admW_of_adm P W hD), cls_indep P g W e depth s₀ ⟨s₁, hs₁⟩]
  rfl

include hcomp in
set_option maxHeartbeats 64000000 in

theorem sndDeg_of_hcomp
    (hWφ : ∀ w ∈ W, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w)
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
    (hH : Pic0.mk D ∈ inertiaInvariants A (N * q))
    (hgood : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
    (s₁ : ↥(nodePairsOfPlaces g W)) :
    comp ⟨Pic0.mk D, hH⟩ =
      (P.sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))).degree •
        componentGroupProj (widthOfPlaces g W e)
          ((widthOfPlaces g W e s₁ : ℤ) •
            (LinearMap.proj s₁ : (↥(nodePairsOfPlaces g W) → ℤ) →ₗ[ℤ] ℤ).comp
              (characterLattice ↥(nodePairsOfPlaces g W)).subtype) := by
  rw [hcomp ⟨Pic0.mk D, hH⟩ D rfl (admW_of_isGoodDiv P W hgood), cls_indep P g W e depth s₀ s₁,
    cls_of_isGoodDiv P g W e depth hWφ s₁ hgood, widthOfPlaces_apply]
  rfl

include hcomp in
set_option maxHeartbeats 64000000 in

theorem coord_hit_of_strict_pair
    (hWφ : ∀ w ∈ W, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w)
    {V₁ V₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hV₁ : P.IsStrictFst V₁)
    (hV₁fix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V₁ = V₁)
    (hV₂ : P.IsStrictSnd V₂)
    (hV₂fix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V₂ = V₂)
    (s : ↥(nodePairsOfPlaces g W))
    (h1 : e (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 = 1) :
    ∃ x, comp x = componentGroupProj (widthOfPlaces g W e) (crossingCoord s) := by
  let D₀ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))) :=
    ⟨_, pair_mem_degZero V₁ V₂⟩
  have hH₀ : Pic0.mk D₀ ∈ inertiaInvariants A (N * q) := mk_mem_inertiaInvariants D₀ (pair_fixed hV₁fix hV₂fix)
  refine ⟨⟨Pic0.mk D₀, hH₀⟩, ?_⟩
  have hgood : P.IsGoodDiv (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) := by
    intro V hV
    rcases support_pair_subset (q := q) hV with rfl | rfl
    · exact Or.inr hV₂
    · exact Or.inl hV₁
  rw [hcomp ⟨Pic0.mk D₀, hH₀⟩ D₀ rfl (admW_of_isGoodDiv P W hgood), cls_indep P g W e depth s₀ s]
  show cls P g W e depth s (Finsupp.single V₂ 1 - Finsupp.single V₁ 1) = _
  rw [cls_strict_pair P g W e depth hWφ hV₁ hV₂ s, widthOfPlaces_apply, h1]
  simp

include hcomp in
set_option maxHeartbeats 64000000 in

theorem coord_hit_of_node_place
    {V₀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hV₀s : P.IsStrictFst V₀)
    (hV₀fix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V₀ = V₀)
    (hV₀W : P.reduceFst V₀ ∉ W)
    (s : ↥(nodePairsOfPlaces g W))
    (hVw : P.reduceFst V = (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1)
    (hVfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V)
    (hVs : ¬ P.IsStrictSnd V) (hd : depth V = 1) :
    ∃ x, comp x = componentGroupProj (widthOfPlaces g W e) (crossingCoord s) := by
  have hVW : P.reduceFst V ∈ W := by rw [hVw]; exact fst_mem_W g W s
  let D₁ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))) :=
    ⟨_, pair_mem_degZero V₀ V⟩
  have hH₁ : Pic0.mk D₁ ∈ inertiaInvariants A (N * q) := mk_mem_inertiaInvariants D₁ (pair_fixed hV₀fix hVfix)
  refine ⟨⟨Pic0.mk D₁, hH₁⟩, ?_⟩
  have hadm : AdmW P W (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) := by
    intro V' hV'
    rcases support_pair_subset (q := q) hV' with rfl | rfl
    · exact Or.inr (Or.inr ⟨hVW, hVfix⟩)
    · exact Or.inl hV₀s
  rw [hcomp ⟨Pic0.mk D₁, hH₁⟩ D₁ rfl hadm]
  show cls P g W e depth s₀ (Finsupp.single V 1 - Finsupp.single V₀ 1) = _
  rw [cls_node_pair P g W e depth hV₀W (not_isStrictSnd_of_isStrictFst P hV₀s) hVs s s₀ hVw, hd]
  simp

end GramAsm

set_option maxHeartbeats 192000000 in
open GramAsm in
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
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (e : Place k (modularFunctionFieldC k N) → ℕ)
    (he : ∀ w ∈ W, e w = placeWidthChar q N w) :
    ∃ (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ)
      (comp : ↥(inertiaInvariants A (N * q)) →+
        componentGroup (widthOfPlaces (arithFrobC q k N) W e)),
      P.DepthCompLaw (arithFrobC q k N) W e depth comp ∧
        (∀ w ∈ W, ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K)
          (xw : ↥(NodeLocalized.coeffSubring A K)) (_ : NodeLocalized.redRestrict red K xw = w.evalAt (jGeomGen k N))
          (ϖ : ↥(NodeLocalized.coeffSubring A K))
          (_ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
          (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)) (_ : IsUnit ε)
          (_ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
          (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (_ : IsUnit u)
          (_ : ∀ g g' : ↥(R.nodeIntegersOver K w),
            0 < w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) → w.ord (R.nodeResidue₁ w ⟨g', g'.2.1⟩) = 1 →
            ∃ b : ↥(R.nodeIntegersOver K w),
              R.nodeResidue₁ w ⟨g, g.2.1⟩ = R.nodeResidue₁ w ⟨g', g'.2.1⟩ * R.nodeResidue₁ w ⟨b, b.2.1⟩)
          (_ : ∀ g g' : ↥(R.nodeIntegersOver K w),
            0 < (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) →
            (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g', g'.2.1⟩) = 1 →
            ∃ b : ↥(R.nodeIntegersOver K w),
              R.nodeResidue₂ w ⟨g, g.2.1⟩ = R.nodeResidue₂ w ⟨g', g'.2.1⟩ * R.nodeResidue₂ w ⟨b, b.2.1⟩),
          c.x * c.y = R.nodeConst K w ϖ ^ E * u ∧ c.DepthValueLaw depth) ∧
      (∀ w ∈ W, 0 < e w) ∧
      (∀ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
            (F := ↥(modularFunctionFieldBar (N * q)))))
          (hH : Pic0.mk D ∈ inertiaInvariants A (N * q)),
          P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) →
          ∀ s₀ : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
            comp ⟨Pic0.mk D, hH⟩ =
              (P.sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))).degree •
                componentGroupProj (widthOfPlaces (arithFrobC q k N) W e)
                  ((widthOfPlaces (arithFrobC q k N) W e s₀ : ℤ) •
                    (LinearMap.proj s₀ : (↥(nodePairsOfPlaces (arithFrobC q k N) W) → ℤ) →ₗ[ℤ] ℤ).comp
                      (characterLattice ↥(nodePairsOfPlaces (arithFrobC q k N) W)).subtype)) ∧
      Function.Surjective comp ∧
      (∀ x : ↥(inertiaInvariants A (N * q)), comp x = 0 →
        ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
            (F := ↥(modularFunctionFieldBar (N * q)))),
          P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∧
            Pic0.mk D = (x : JZero (N * q))) ∧
      (∀ x : ↥(inertiaInvariants A (N * q)),
        ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
            (F := ↥(modularFunctionFieldBar (N * q)))),
          (∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
            (∀ σ ∈ A.inertiaSubgroupIn ℚ,
                arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
              (P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)) ∧
            Pic0.mk D = (x : JZero (N * q))) ∧
      (∃ G : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        Divisor.IsPrincipal G ∧ P.IsGoodDiv G ∧
          (P.fstDiv G).degree = ((∑ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
            Finset.univ.lcm (widthOfPlaces (arithFrobC q k N) W e) / widthOfPlaces (arithFrobC q k N) W e s : ℕ) : ℤ) ∧
          (P.sndDiv G).degree = -((∑ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
            Finset.univ.lcm (widthOfPlaces (arithFrobC q k N) W e) / widthOfPlaces (arithFrobC q k N) W e s : ℕ) : ℤ)) := by
  classical
  haveI : PerfectField k := inferInstance

  have hW' : ∀ w ∈ W, w ∈ ssPlaces q N k := fun w hw => (hW w).mp hw
  have hWφ : ∀ w ∈ W, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w :=
    fun w hw => frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
      k N hqN data hKr w (hW' w hw)
  have hred : Function.Surjective red := red_surjective_of_level P
  have hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A := by
    have hmax : (RingHom.ker red).IsMaximal := RingHom.ker_isMaximal_of_surjective red hred
    have heq : RingHom.ker red = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal hmax
    intro c
    rw [← heq, RingHom.mem_ker]
  have hwid : ∀ w ∈ W, 1 ≤ e w := fun w hw => by
    rw [he w hw]; exact one_le_placeWidthChar_of_mem_ssPlaces hqN (hW' w hw)
  have hwid0 : ∀ w ∈ W, 0 < e w := fun w hw => hwid w hw
  have hVI : ∀ w ∈ W, R.ValueIntegralityLaw w :=
    fun w hw => ProlongationTuple.valueIntegralityLaw_of_orderLawFixed R hqN hO w (hW' w hw)
  have hrat : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V.IsRational :=
    fun V => (Place.isRational_iff_deg_eq_one V).mpr (deg_eq_one_modularFunctionFieldBar (N * q) V)

  have hvq1 : A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) < 1 := by
    have hmem : ((q : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A :=
      (hker _).mp (by rw [map_natCast]; exact CharP.cast_eq_zero k q)
    have h := (A.valuation_lt_one_iff _).mp hmem
    simpa using h
  have hvq0 : A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hvqpos : 0 < A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) := zero_lt_iff.mpr hvq0

  obtain ⟨K₀, hK₀fd, hK₀fix, hϖ, hk₀, cs, hxy, hmax, hbr, hnoeth, hres⟩ :=
    ProlongationTuple.exists_inertiaFixed_range_redRestrict_forall_nodeCoordinates_presentation_of_orderLawFixed
      R hqN hker hR hO W hW' hRL hNV
  haveI := hK₀fd
  set ϖq : ↥(NodeLocalized.coeffSubring A K₀) := ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) with hϖq_def
  have hϖq_coe : ((ϖq : ↥(NodeLocalized.coeffSubring A K₀)) : AlgebraicClosure ℚ) = ((q : ℕ) : AlgebraicClosure ℚ) := by
    rw [hϖq_def]; norm_cast
  have hϖq0 : ((ϖq : ↥(NodeLocalized.coeffSubring A K₀)) : AlgebraicClosure ℚ) ≠ 0 := by
    rw [hϖq_coe]; exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) = ϖq ^ 1 * 1 := by rw [pow_one, mul_one]
  have hxy' : ∀ w (hw : w ∈ W), ∃ u : ↥(R.nodeIntegersOver K₀ w), IsUnit u ∧
      (cs w hw).x * (cs w hw).y = R.nodeConst K₀ w ϖq ^ (e w * 1) * u := by
    intro w hw; rw [mul_one, he w hw]; exact hxy w hw

  have hdep : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), ∃ d : ℕ,
      ∀ (hw : P.reduceFst V ∈ W),
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) →
        (cs _ hw).yDepth V = A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ d := by
    intro V
    by_cases hw : P.reduceFst V ∈ W
    · by_cases hfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V
      · obtain ⟨u, hu, hxyw⟩ := hxy _ hw
        obtain ⟨d, hd⟩ := ProlongationTuple.NodeCoordinates.exists_yDepth_eq_pow_of_forall_inertia_smul_eq
          (cs _ hw) (hVI _ hw) hK₀fix ϖq hϖq0 _ u hu hxyw V rfl (hrat V) hfix
        exact ⟨d, fun _ _ => hd⟩
      · exact ⟨0, fun _ h => absurd h hfix⟩
    · exact ⟨0, fun h => absurd h hw⟩
  choose depth hdepth using hdep
  have hDVL : ∀ w (hw : w ∈ W), (cs w hw).DepthValueLaw depth := by
    intro w hw V hV hfix
    subst hV
    exact hdepth V hw hfix

  have hR1 : ∀ (f : ↥(modularFunctionFieldBar (N * q))) (hf : f ≠ 0)
      (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hDf : ∀ V, D V = V.ord f)
      (hsupp : AdmW P W D) (s₀ : ↥(nodePairsOfPlaces (arithFrobC q k N) W)),
      cls P (arithFrobC q k N) W e depth s₀ D = 0 :=
    fun f hf D hDf hsupp s₀ =>
      componentGroupProj_depthDual_add_degree_sndDiv_smul_eq_zero_of_div P R hqN hR hO W hW hRL hNV e hwid
        K₀ ϖq hϖ 1 le_rfl 1 isUnit_one hqϖ cs hxy' hmax hbr hnoeth hres hVI depth hDVL f hf D hDf hsupp s₀

  have hwd : ∀ (s₀ : ↥(nodePairsOfPlaces (arithFrobC q k N) W))
      (D₁ D₂ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))),
      Pic0.mk D₁ = Pic0.mk D₂ →
      AdmW P W (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) →
      AdmW P W (D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) →
      cls P (arithFrobC q k N) W e depth s₀ (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
        = cls P (arithFrobC q k N) W e depth s₀ (D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) := by
    intro s₀ D₁ D₂ h h1 h2
    have hpr : ((D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) - D₂).IsPrincipal := by
      have h' := QuotientAddGroup.eq_iff_sub_mem.mp h
      rw [AddSubgroup.mem_addSubgroupOf, AddSubgroupClass.coe_sub] at h'
      exact h'
    obtain ⟨f, hf, hDf⟩ := hpr
    have h0 := hR1 f hf _ hDf (admW_sub P W h1 h2) s₀
    rw [cls_sub] at h0
    exact sub_eq_zero.mp h0

  have hrep0 := exists_inertiaFixedSupport_degZero_pic0Mk_eq_of_isModel q A N k red data hKr hα hβ hqN P W hW R hR hRL hO
  have hrep : ∀ x : ↥(inertiaInvariants A (N * q)),
      ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
        Pic0.mk D = (x : JZero (N * q)) ∧ Adm P W (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) := by
    intro x
    obtain ⟨D, hD, hfix, hsupp⟩ := hrep0 x
    exact ⟨D, hD, fun V hV => ⟨fun σ hσ => hfix σ hσ V hV, hsupp V hV⟩⟩
  choose rep hrep_mk hrep_adm using hrep
  have hrepInv : ∀ x : ↥(inertiaInvariants A (N * q)),
      ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
        (∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
            (P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)) ∧
          Pic0.mk D = (x : JZero (N * q)) :=
    fun x => ⟨rep x, hrep_adm x, hrep_mk x⟩

  have hnode : ∀ w ∈ W, ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K)
      (xw : ↥(NodeLocalized.coeffSubring A K)) (_ : NodeLocalized.redRestrict red K xw = w.evalAt (jGeomGen k N))
      (ϖ : ↥(NodeLocalized.coeffSubring A K))
      (_ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
      (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)) (_ : IsUnit ε)
      (_ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
      (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (_ : IsUnit u)
      (_ : ∀ g g' : ↥(R.nodeIntegersOver K w),
        0 < w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) → w.ord (R.nodeResidue₁ w ⟨g', g'.2.1⟩) = 1 →
        ∃ b : ↥(R.nodeIntegersOver K w),
          R.nodeResidue₁ w ⟨g, g.2.1⟩ = R.nodeResidue₁ w ⟨g', g'.2.1⟩ * R.nodeResidue₁ w ⟨b, b.2.1⟩)
      (_ : ∀ g g' : ↥(R.nodeIntegersOver K w),
        0 < (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) →
        (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g', g'.2.1⟩) = 1 →
        ∃ b : ↥(R.nodeIntegersOver K w),
          R.nodeResidue₂ w ⟨g, g.2.1⟩ = R.nodeResidue₂ w ⟨g', g'.2.1⟩ * R.nodeResidue₂ w ⟨b, b.2.1⟩),
      c.x * c.y = R.nodeConst K w ϖ ^ E * u ∧ c.DepthValueLaw depth := by
    intro w hw
    obtain ⟨xw, hxw⟩ : ∃ xw : ↥(NodeLocalized.coeffSubring A K₀),
        NodeLocalized.redRestrict red K₀ xw = w.evalAt (jGeomGen k N) :=
      hk₀ _ (pow_q_sq_eq_self_of_mem_ssJSet q (hW' w hw).2.2)
    obtain ⟨u, hu, hxyw⟩ := hxy w hw
    obtain ⟨hs1, hs2⟩ := ProlongationTuple.nodeResidue_saturated_of_orderLawFixed R hqN hR hO W hW' hRL hNV K₀ w hw
    exact ⟨K₀, hK₀fd, xw, hxw, ϖq, hϖ, 1, 1, isUnit_one, hqϖ, cs w hw, placeWidthChar q N w, u, hu, hs1, hs2,
      hxyw, hDVL w hw⟩

  have hPG : ∃ G : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        Divisor.IsPrincipal G ∧ P.IsGoodDiv G ∧
          (P.fstDiv G).degree = ((∑ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
            Finset.univ.lcm (widthOfPlaces (arithFrobC q k N) W e) / widthOfPlaces (arithFrobC q k N) W e s : ℕ) : ℤ) ∧
          (P.sndDiv G).degree = -((∑ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
            Finset.univ.lcm (widthOfPlaces (arithFrobC q k N) W e) / widthOfPlaces (arithFrobC q k N) W e s : ℕ) : ℤ) := by
    obtain ⟨G, hGpr, hGgood, hGfst⟩ :=
      exists_isPrincipal_isGoodDiv_degree_fstDiv_eq_widthSum_widthChar_of_isModel hqN hred P W hW R hR hRL hNV hO e he
    exact ⟨G, hGpr, hGgood, hGfst, by rw [degree_sndDiv_eq_neg P hGpr hGgood, hGfst]⟩

  by_cases hne : (nodePairsOfPlaces (arithFrobC q k N) W).Nonempty
  swap
  · haveI : IsEmpty ↥(nodePairsOfPlaces (arithFrobC q k N) W) := ⟨fun s => hne ⟨s.1, s.2⟩⟩
    haveI : Subsingleton (componentGroup (widthOfPlaces (arithFrobC q k N) W e)) :=
      subsingleton_componentGroup _
    have hWempty : ∀ w, w ∉ W := fun w hw =>
      hne ⟨_, smulNodePair_mem_nodePairsOfPlaces (arithFrobC q k N) hw⟩
    refine ⟨depth, 0, ?_, hnode, hwid0, ?_, ?_, ?_, hrepInv, ?_⟩
    · intro D hH hD s₀ hs₀; exact absurd ⟨s₀, hs₀⟩ hne
    · intro D hH hD s₀; exact Subsingleton.elim _ _
    · exact fun y => ⟨0, Subsingleton.elim _ _⟩
    ·
      intro x _
      refine ⟨rep x, ?_, hrep_mk x⟩
      intro V hV
      rcases (hrep_adm x V hV).2 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h (hWempty _)
    · exact hPG
  obtain ⟨s₀v, hs₀v⟩ := hne
  obtain ⟨s₀⟩ : Nonempty ↥(nodePairsOfPlaces (arithFrobC q k N) W) := ⟨⟨s₀v, hs₀v⟩⟩

  obtain ⟨comp, hcomp⟩ := exists_comp_of_rep P (arithFrobC q k N) W e depth s₀ rep hrep_mk
    (fun x => admW_of_adm P W (hrep_adm x)) (hwd s₀)

  have hlaw : P.DepthCompLaw (arithFrobC q k N) W e depth comp :=
    depthCompLaw_of_hcomp P (arithFrobC q k N) W e depth s₀ comp hcomp

  have hsnd := fun D hH hgood s₁ => sndDeg_of_hcomp P (arithFrobC q k N) W e depth s₀ comp hcomp hWφ D hH hgood s₁

  obtain ⟨V₀, hV₀s, hV₀fix, hV₀W⟩ := ProlongationTuple.exists_isStrictFst_and_smul_eq_self R hqN hR W hW'
  have hcoord : ∀ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W), ∃ x, comp x =
      componentGroupProj (widthOfPlaces (arithFrobC q k N) W e) (crossingCoord s) := by
    intro s
    have hsW : (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 ∈ W :=
      fst_mem_W (arithFrobC q k N) W s
    by_cases h1 : e (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 = 1
    · obtain ⟨X, hX⟩ := exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq P hqN
      obtain ⟨-, Q₂, -, hQ₂s, -, -, -, hQ₂X⟩ := exists_families_isStrictFst_isStrictSnd_notMem P hqN X 0 1
      obtain ⟨u, hu, hufix⟩ := hX (P.reduceSnd (Q₂ 0)) (hQ₂X 0)
      obtain ⟨V₂, hV₂s, -, -, hV₂fix⟩ :=
        exists_isStrictSnd_restrictAlong_eq_forall_inertia_smul_eq P u (by rw [hu]; exact (hQ₂s 0).2) hufix
      exact coord_hit_of_strict_pair P (arithFrobC q k N) W e depth s₀ comp hcomp hWφ hV₀s hV₀fix hV₂s hV₂fix s h1
    · have h2 : 2 ≤ placeWidthChar q N (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 := by
        have := hwid _ hsW; rw [he _ hsW] at h1 this; omega
      obtain ⟨u, hu, hxyw⟩ := hxy _ hsW
      have hdE : A.valuation ((ϖq : ↥(NodeLocalized.coeffSubring A K₀)) : AlgebraicClosure ℚ) ^
          placeWidthChar q N (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1
          < A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ 1 := by
        rw [hϖq_coe]
        exact pow_lt_pow_right_of_lt_one₀ hvqpos hvq1 (by omega)
      obtain ⟨V, hVw, hVfix, hVd⟩ :=
        ProlongationTuple.exists_reduceFst_eq_and_smul_eq_self_and_yDepth_eq_pow_of_orderLawFixed R hqN hR hO W hW'
          hRL hNV K₀ _ hsW (hVI _ hsW) ϖq (cs _ hsW) _ u hu hxyw 1 one_pos hdE
      have hdepthV : depth V = 1 := by
        have h := hDVL _ hsW V hVw hVfix
        rw [hVd] at h
        by_contra hne1
        rcases Nat.lt_or_gt_of_ne hne1 with hlt | hgt
        · exact absurd h (ne_of_lt (pow_lt_pow_right_of_lt_one₀ hvqpos hvq1 hlt))
        · exact absurd h (ne_of_gt (pow_lt_pow_right_of_lt_one₀ hvqpos hvq1 hgt))
      have hVW : P.reduceFst V ∈ W := by rw [hVw]; exact hsW
      have hVs : ¬ P.IsStrictSnd V := fun h => reduceFst_not_mem_of_strict P W hWφ (Or.inr h) hVW
      exact coord_hit_of_node_place P (arithFrobC q k N) W e depth s₀ comp hcomp hV₀s hV₀fix hV₀W s hVw hVfix hVs hdepthV
  have hsurj : Function.Surjective comp :=
    comp_surjective_of_forall_exists_eq_crossingCoord (widthOfPlaces (arithFrobC q k N) W e) comp hcoord

  have hker' := exists_isGoodDiv_pic0Mk_eq_of_comp_eq_zero_of_depthCompLaw_depthValueLaw_repOfInvariant_of_isModel
    q A N k red data hKr hα hβ hqN P W hW R hR hRL hNV hO e he depth comp hlaw hnode hrepInv
  refine ⟨depth, comp, hlaw, ?_, hwid0, ?_, hsurj, ?_, hrepInv, hPG⟩
  · exact hnode
  · intro D hH hgood s₁
    exact hsnd D hH hgood s₁
  · exact hker'

end
end S_ModularCurve_PlaceSpecialization_exists_depth_comp_depthCompLaw_depthValueLaw_sndDegLaw_surjective_repOfKer_repOfInvariant_principalGood_of_widthPinChar_of_isModel
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_depth_comp_depthCompLaw_depthValueLaw_sndDegLaw_surjective_repOfKer_repOfInvariant_principalGood_of_widthPinChar_of_isModel (solution)
