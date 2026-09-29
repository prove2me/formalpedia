-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.isLocalRing_and_isNoetherianRing_nodeIntegersOver_of_nodeCoordinates_of_orderLawFixed_of_range_redRestrict
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/9e5ff5be-550f-5ab0-8401-f013f87e8c00

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_jIntegralClosure_ord_residues_pos_and_eq_zero_of_ne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isLocalRing_nodeIntegersOver_of_orderLawFixed_of_regularityLaw
import Theorems.Thm_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_nodeResidueFst_red_evalAt_of_orderLawFixed
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_nodeResidueSnd_red_evalAt_of_orderLawFixed
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valueIntegralityLaw_of_orderLawFixed
import Theorems.Thm_ModularCurve_exists_phiIrreducible
import Theorems.Thm_ModularCurve_PlaceSpecialization_red_surjective_of_level
import Theorems.Thm_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_place_forall_iff_mem_and_hasValue_of_height_one_of_natCast_notMem
import Theorems.Thm_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem_level
import Theorems.Thm_ModularCurve_PlaceSpecialization_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_of_mem_fieldOver_nodeIntegersOver
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isCuspidal_of_not_isAffineGeomPlace_reduceFst
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_isLocalRing_and_isNoetherianRing_nodeIntegersOver_of_nodeCoordinates_of_orderLawFixed_of_range_redRestrict
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.cuspCount_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ"
p2m_attr_erase "simp" "AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace NodeRingNoetherian

private theorem isLocalRing_nodeRing
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) :
    IsLocalRing ↥(R.nodeIntegersOver K w) :=
  isLocalRing_nodeIntegersOver_of_orderLawFixed_of_regularityLaw R hqN hO W hW hreg K w hw

private theorem mem_jIntegralClosure_of_mem_jRing (M : ℕ) [NeZero M] (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : x ∈ NodeLocalized.jRing A K) : x ∈ NodeLocalized.jIntegralClosure M A K := by
  show x ∈ NodeLocalized.fieldOver M K ∧ IsIntegral (NodeLocalized.jRing A K) x
  refine ⟨(Subring.closure_le (t := (NodeLocalized.fieldOver M K).toSubring)).mpr ?_ hx, ?_⟩
  · rintro y (⟨c, rfl⟩ | hy)
    · exact Subfield.subset_closure (Or.inl ⟨⟨(c : AlgebraicClosure ℚ),
        (Subring.mem_inf.mp
          (show (c : AlgebraicClosure ℚ) ∈ A.toSubring ⊓ K.toSubalgebra.toSubring from c.2)).2⟩,
        rfl⟩)
    · rw [Set.eq_of_mem_singleton hy]
      exact Subfield.subset_closure (Or.inr (Set.mem_insert _ _))
  · exact isIntegral_algebraMap (x := (⟨x, hx⟩ : NodeLocalized.jRing A K))

open ModularCurve.NodeLocalized

set_option synthInstance.maxHeartbeats 1600000 in

private theorem residue₁_algebraMap_eq_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) :
    R.residue₁ ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ),
      (R.R₁.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2⟩ = 0 := by
  show R.ι (R.R₁.residue _) = 0
  rw [R.R₁.residue_algebraMap a, (IsLocalRing.residue_eq_zero_iff a).mpr ha, RingHom.map_zero, RingHom.map_zero]

set_option synthInstance.maxHeartbeats 1600000 in

private theorem residue₂_algebraMap_eq_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) :
    R.residue₂ ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ),
      (R.R₂.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2⟩ = 0 := by
  show R.ι (R.R₂.residue _) = 0
  rw [R.R₂.residue_algebraMap a, (IsLocalRing.residue_eq_zero_iff a).mpr ha, RingHom.map_zero, RingHom.map_zero]

set_option synthInstance.maxHeartbeats 1600000 in

private theorem residue₁_sub_algebraMap_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (g : ↥(modularFunctionFieldBar (N * q))) (h₁ : g ∈ R.R₁.integers)
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) :
    R.residue₁ ⟨g - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ),
      sub_mem h₁ ((R.R₁.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2)⟩ = R.residue₁ ⟨g, h₁⟩ := by
  have hsub : (⟨g - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ),
      sub_mem h₁ ((R.R₁.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2)⟩ : R.R₁.integers)
      = ⟨g, h₁⟩ - ⟨_, (R.R₁.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2⟩ :=
    Subtype.ext (by rw [AddSubgroupClass.coe_sub])
  rw [hsub, RingHom.map_sub, residue₁_algebraMap_eq_zero R a ha, sub_zero]

set_option synthInstance.maxHeartbeats 1600000 in

private theorem residue₂_sub_algebraMap_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (g : ↥(modularFunctionFieldBar (N * q))) (h₂ : g ∈ R.R₂.integers)
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) :
    R.residue₂ ⟨g - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ),
      sub_mem h₂ ((R.R₂.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2)⟩ = R.residue₂ ⟨g, h₂⟩ := by
  have hsub : (⟨g - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ),
      sub_mem h₂ ((R.R₂.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2)⟩ : R.R₂.integers)
      = ⟨g, h₂⟩ - ⟨_, (R.R₂.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2⟩ :=
    Subtype.ext (by rw [AddSubgroupClass.coe_sub])
  rw [hsub, RingHom.map_sub, residue₂_algebraMap_eq_zero R a ha, sub_zero]

private theorem mem_maximalIdeal_iff_ord_pos_of_ne_zero {K₀ F₀ : Type*} [Field K₀] [Field F₀] [Algebra K₀ F₀]
    (v : Place K₀ F₀) {x : F₀} (hx : x ≠ 0) (hmem : x ∈ v.toValuationSubring) :
    (⟨x, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring ↔ 0 < v.ord x := by
  constructor
  · intro hmax
    have h0 : 0 ≤ v.ord x := Place.ord_nonneg_of_mem v hmem
    rcases h0.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      obtain ⟨hm, hu⟩ := Place.exists_isUnit_of_ord_eq_zero v hx heq.symm
      exact (IsLocalRing.mem_maximalIdeal _).mp hmax hu
  · intro hpos
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h0 := Place.ord_coe_unit v hu.unit
    rw [IsUnit.unit_spec] at h0
    change v.ord x = 0 at h0
    omega

private theorem hasValue_zero_of_ord_pos {K₀ F₀ : Type*} [Field K₀] [Field F₀] [Algebra K₀ F₀]
    (v : Place K₀ F₀) {x : F₀} (hx : x ≠ 0) (hpos : 0 < v.ord x) : v.HasValue x 0 := by
  have hmem : x ∈ v.toValuationSubring := Place.mem_of_ord_nonneg v hx hpos.le
  refine ⟨hmem, ?_⟩
  rw [map_zero, IsLocalRing.residue_eq_zero_iff]
  exact (mem_maximalIdeal_iff_ord_pos_of_ne_zero v hx hmem).mpr hpos

private theorem ord_sub_algebraMap_pos {K₀ F₀ : Type*} [Field K₀] [Field F₀] [Algebra K₀ F₀]
    (v : Place K₀ F₀) {g : F₀} {a : K₀} (h : v.HasValue g a) (hne : g - algebraMap K₀ F₀ a ≠ 0) :
    0 < v.ord (g - algebraMap K₀ F₀ a) := by
  have hmem : g - algebraMap K₀ F₀ a ∈ v.toValuationSubring := sub_mem h.mem (v.algebraMap_mem' a)
  refine (mem_maximalIdeal_iff_ord_pos_of_ne_zero v hne hmem).mp ?_
  rw [← IsLocalRing.residue_eq_zero_iff]
  have hsub : (⟨g - algebraMap K₀ F₀ a, hmem⟩ : v.toValuationSubring)
      = ⟨g, h.mem⟩ - algebraMap K₀ v.toValuationSubring a :=
    Subtype.ext (by rw [AddSubgroupClass.coe_sub, Place.coe_algebraMap])
  rw [hsub, RingHom.map_sub, h.residue_eq, Place.residue_algebraMap, sub_self]

private theorem le_mapDomain_apply_of_nonneg {α β : Type*} (D : α →₀ ℤ) (φ : α → β) (b : β) (x : α)
    (hx : φ x = b) (hnn : ∀ y ∈ D.support, φ y = b → 0 ≤ D y) : D x ≤ Finsupp.mapDomain φ D b := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  simp only [Finsupp.single_apply]
  unfold Finsupp.sum
  have hterm : ∀ y ∈ D.support, (0 : ℤ) ≤ (if φ y = b then D y else 0) := by
    intro y hy
    split_ifs with h
    · exact hnn y hy h
    · exact le_rfl
  by_cases hmem : x ∈ D.support
  · calc D x = (if φ x = b then D x else 0) := by rw [if_pos hx]
      _ ≤ ∑ y ∈ D.support, (if φ y = b then D y else 0) :=
        Finset.single_le_sum (f := fun y => if φ y = b then D y else 0) hterm hmem
  · rw [Finsupp.notMem_support_iff.mp hmem]
    exact Finset.sum_nonneg hterm

private theorem hasValue_of_ord_sub_pos {K₀ F₀ : Type*} [Field K₀] [Field F₀] [Algebra K₀ F₀] (v : Place K₀ F₀)
    {g : F₀} {a : K₀} (h : 0 < v.ord (g - algebraMap K₀ F₀ a)) : v.HasValue g a := by
  by_cases h0 : g - algebraMap K₀ F₀ a = 0
  · rw [sub_eq_zero.mp h0]
    exact v.hasValue_algebraMap a
  · have hmem : g - algebraMap K₀ F₀ a ∈ v.toValuationSubring := Place.mem_of_ord_nonneg v h0 h.le
    have hmax := (mem_maximalIdeal_iff_ord_pos_of_ne_zero v h0 hmem).mpr h
    have hres0 : residue v.toValuationSubring ⟨_, hmem⟩ = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmax
    have hcm : algebraMap K₀ F₀ a ∈ v.toValuationSubring := (v.hasValue_algebraMap a).mem
    have hgmem : g ∈ v.toValuationSubring := by
      have h' := add_mem hmem hcm
      rwa [sub_add_cancel] at h'
    refine ⟨hgmem, ?_⟩
    have hsplit : (⟨g, hgmem⟩ : v.toValuationSubring) = ⟨_, hmem⟩ + ⟨_, hcm⟩ := Subtype.ext (sub_add_cancel _ _).symm
    rw [hsplit, map_add, hres0, zero_add]
    exact (v.hasValue_algebraMap a).residue_eq

private theorem ord_sub_pos_of_hasValue {K₀ F₀ : Type*} [Field K₀] [Field F₀] [Algebra K₀ F₀] (v : Place K₀ F₀)
    {g : F₀} {a : K₀} (h : v.HasValue g a) (hne : g ≠ algebraMap K₀ F₀ a) : 0 < v.ord (g - algebraMap K₀ F₀ a) := by
  have hne' : g - algebraMap K₀ F₀ a ≠ 0 := sub_ne_zero.mpr hne
  have hcm : algebraMap K₀ F₀ a ∈ v.toValuationSubring := (v.hasValue_algebraMap a).mem
  have hmem : g - algebraMap K₀ F₀ a ∈ v.toValuationSubring := sub_mem h.mem hcm
  refine (mem_maximalIdeal_iff_ord_pos_of_ne_zero v hne' hmem).mp ?_
  rw [← IsLocalRing.residue_eq_zero_iff]
  have hsplit : (⟨_, hmem⟩ : v.toValuationSubring) = ⟨g, h.mem⟩ - ⟨_, hcm⟩ := Subtype.ext rfl
  rw [hsplit, map_sub, h.residue_eq, (v.hasValue_algebraMap a).residue_eq, sub_self]

private theorem evalAt_eq_of_hasValue {K₀ F₀ : Type*} [Field K₀] [Field F₀] [Algebra K₀ F₀] (v : Place K₀ F₀)
    {g : F₀} {a : K₀} (h : v.HasValue g a) : v.evalAt g = a := by
  rw [v.evalAt_of_mem h.mem, h.residue_eq, v.residueInv_algebraMap]

private theorem isRational_of_isAlgClosed {k : Type*} [Field k] [IsAlgClosed k] (N : ℕ) [NeZero N]
    (v : Place k (modularFunctionFieldC k N)) : v.IsRational := by
  haveI := isCurveOver_modularFunctionFieldC_of_perfectField k N
  haveI : Module.Finite k v.ResidueField := IsCurveOver.finite_residueField v
  show Function.Surjective (algebraMap k v.ResidueField)
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := v.ResidueField)).2

private theorem red_eq_zero_of_mem_maximalIdeal
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) {a : A} (ha : a ∈ IsLocalRing.maximalIdeal A) : red a = 0 := by
  rw [← R.redBar_residue a, (IsLocalRing.residue_eq_zero_iff a).mpr ha, RingHom.map_zero]

private theorem jFun_coe_eq_jqModC (N q : ℕ) [NeZero N] [NeZero q] :
    ((jFun N q : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
      jqModC (AlgebraicClosure ℚ) := by
  show coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ)
  have h := ModularCurve.coeffMap_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))
  rw [jqModC_rat] at h
  exact h

private theorem jFun_sub_mem_jIntegralClosure (N q : ℕ) [NeZero N] [NeZero q]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (a₀ : ↥(coeffSubring A K)) :
    ((jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a₀ : AlgebraicClosure ℚ) :
        ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K := by
  apply mem_jIntegralClosure_of_mem_jRing
  have hcoe : ((jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))
        (a₀ : AlgebraicClosure ℚ) : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
        jqModC (AlgebraicClosure ℚ) - CharPReduction.constSeries (coeffSubring A K) a₀ := by
    push_cast
    rw [jFun_coe_eq_jqModC]
    rfl
  rw [hcoe]
  exact sub_mem (Subring.subset_closure (Or.inr (Set.mem_singleton _))) (Subring.subset_closure (Or.inl ⟨a₀, rfl⟩))

set_option synthInstance.maxHeartbeats 1600000 in

private theorem hasValue_residueFst_zero_of_red_evalAt_eq_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (hvalA : R.ValueIntegralityLaw w) (t : ↥(modularFunctionFieldBar (N * q))) (htS : t ∈ R.nodeIntegersOver K w)
    (h₁ : t ∈ R.R₁.integers) (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hV₀ : P.reduceFst V₀ = w)
    (hz : red ⟨V₀.evalAt t, hvalA t (R.nodeIntegersOver_le K w htS) V₀ hV₀⟩ = 0) :
    w.HasValue (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k) := by
  have h := hasValue_nodeResidueFst_red_evalAt_of_orderLawFixed R hqN hmodel hO W hW hreg hval K w hw hvalA
    ⟨t, htS⟩ V₀ hV₀
  rw [nodeResidue₁_apply] at h
  have h' : w.HasValue (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N))
      (red ⟨V₀.evalAt t, hvalA t (R.nodeIntegersOver_le K w htS) V₀ hV₀⟩) := h
  rw [hz] at h'
  exact h'

set_option synthInstance.maxHeartbeats 1600000 in

private theorem exists_coeff_red_eq_and_hasValue_residueFst_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K))
    :
    ∃ a₀ : ↥(coeffSubring A K), redRestrict red K a₀ = w.evalAt (jGeomGen k N) ∧
      (∀ b : AlgebraicClosure ℚ, jFun N q ≠ algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) b) ∧
      ∃ h₁ : jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a₀ : AlgebraicClosure ℚ)
          ∈ R.R₁.integers,
        w.HasValue (R.residue₁ ⟨_, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k) := by
  have hwss : w ∈ ssPlaces q N k := hW w hw
  have hjss : w.evalAt (jGeomGen k N) ∈ ssJSet q k := hwss.2.2
  obtain ⟨a₀, ha₀⟩ := hk₀ _ (pow_q_sq_eq_self_of_mem_ssJSet q hjss)
  refine ⟨a₀, ha₀, ?_⟩
  obtain ⟨V₀, hV₀⟩ := reduceFst_surjective P w
  have haff₀ : IsAffineGeomPlace k N (P.reduceFst V₀) := by
    rw [hV₀]
    exact hwss.2.1
  obtain ⟨a', h1, h2⟩ := exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst P V₀ haff₀
  rw [hV₀] at h2
  have hja' : w.evalAt (jGeomGen k N) = red a' := evalAt_eq_of_hasValue w (hasValue_of_ord_sub_pos w h2)

  have hnc : ∀ b : AlgebraicClosure ℚ,
      jFun N q ≠ algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) b := by
    intro b hb
    rw [hb, ← RingHom.map_sub] at h1
    by_cases hba : b - (a' : AlgebraicClosure ℚ) = 0
    · rw [hba, RingHom.map_zero, Place.ord_zero] at h1
      exact lt_irrefl _ h1
    · rw [(V₀.hasValue_algebraMap _).ord_eq_zero hba] at h1
      exact lt_irrefl _ h1
  refine ⟨hnc, ?_⟩

  obtain ⟨t, ht_def⟩ : ∃ t : ↥(modularFunctionFieldBar (N * q)),
      t = jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a₀ : AlgebraicClosure ℚ) :=
    ⟨_, rfl⟩
  have htC : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K := by
    rw [ht_def]
    exact jFun_sub_mem_jIntegralClosure N q A K a₀
  have hVt : V₀.HasValue t ((a' : AlgebraicClosure ℚ) - (a₀ : AlgebraicClosure ℚ)) := by
    refine hasValue_of_ord_sub_pos V₀ ?_
    have hid : t - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))
          ((a' : AlgebraicClosure ℚ) - (a₀ : AlgebraicClosure ℚ)) =
        jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a' : AlgebraicClosure ℚ) := by
      rw [ht_def, RingHom.map_sub]
      exact sub_sub_sub_cancel_right _ _ _
    rw [hid]
    exact h1
  have hev : V₀.evalAt t = (a' : AlgebraicClosure ℚ) - (a₀ : AlgebraicClosure ℚ) := evalAt_eq_of_hasValue V₀ hVt
  have hnode := mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure R hqN K w hwss t htC
  have htS : t ∈ R.nodeIntegersOver K w := (R.mem_nodeIntegersOver_iff K w t).mpr ⟨hnode.1, htC.1⟩
  have hvalA : R.ValueIntegralityLaw w := valueIntegralityLaw_of_orderLawFixed R hqN hO w hwss

  obtain ⟨a₀', ha₀'⟩ : ∃ x : A, x = Subring.inclusion inf_le_left a₀ := ⟨_, rfl⟩
  have hca₀ : (a₀' : AlgebraicClosure ℚ) = (a₀ : AlgebraicClosure ℚ) := by
    rw [ha₀']
    rfl
  have hreda₀ : red a₀' = w.evalAt (jGeomGen k N) := by
    rw [ha₀']
    exact ha₀
  have hz : red ⟨V₀.evalAt t, hvalA t (R.nodeIntegersOver_le K w htS) V₀ hV₀⟩ = 0 := by
    have heq : (⟨V₀.evalAt t, hvalA t (R.nodeIntegersOver_le K w htS) V₀ hV₀⟩ : A) = a' - a₀' := by
      apply Subtype.ext
      push_cast
      rw [hev, hca₀]
    rw [heq, RingHom.map_sub, hreda₀, hja', sub_self]
  have h₁t := ((R.mem_nodeIntegers_iff w t).mp hnode.1).1
  have hvan := hasValue_residueFst_zero_of_red_evalAt_eq_zero R hqN hmodel hO W hW hreg hval K w hw hvalA t htS h₁t
    V₀ hV₀ hz
  subst ht_def
  exact ⟨h₁t, hvan⟩

set_option synthInstance.maxHeartbeats 1600000 in

private theorem reduceFst_mem_ssPlaces_of_forall_hasValue_iff
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hV : ∀ (t : ↥(modularFunctionFieldBar (N * q)))
      (_ : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K),
      ∃ a : A, V.HasValue t (a : AlgebraicClosure ℚ) ∧
        ((∃ h₁ : t ∈ R.R₁.integers, w.HasValue (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k)) ↔
          a ∈ IsLocalRing.maximalIdeal A)) :
    P.reduceFst V ∈ ssPlaces q N k := by
  have hwss : w ∈ ssPlaces q N k := hW w hw
  obtain ⟨a₀, hreda₀, hnc, h₁t, hvan⟩ :=
    exists_coeff_red_eq_and_hasValue_residueFst_zero R hqN hmodel hO W hW hreg hval K w hw hk₀

  refine (hV _ (jFun_sub_mem_jIntegralClosure N q A K a₀)).elim fun a ha => ?_
  have ham : a ∈ IsLocalRing.maximalIdeal A := ha.2.mp ⟨h₁t, hvan⟩
  have hreda : red a = 0 := red_eq_zero_of_mem_maximalIdeal R ham
  obtain ⟨a₀', ha₀'⟩ : ∃ x : A, x = Subring.inclusion inf_le_left a₀ := ⟨_, rfl⟩
  have hca₀ : (a₀' : AlgebraicClosure ℚ) = (a₀ : AlgebraicClosure ℚ) := by
    rw [ha₀']
    rfl
  have hreda₀' : red a₀' = w.evalAt (jGeomGen k N) := by
    rw [ha₀']
    exact hreda₀

  have hne : jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a₀ : AlgebraicClosure ℚ)
      ≠ algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) := by
    intro h
    exact hnc ((a : AlgebraicClosure ℚ) + (a₀ : AlgebraicClosure ℚ))
      ((sub_eq_iff_eq_add.mp h).trans (RingHom.map_add _ _ _).symm)
  have hposV : 0 < V.ord (jFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((a + a₀' : A) : AlgebraicClosure ℚ)) := by
    have hord := ord_sub_pos_of_hasValue V ha.1 hne
    have hid : jFun N q -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((a + a₀' : A) : AlgebraicClosure ℚ) =
        jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a₀ : AlgebraicClosure ℚ) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) := by
      first
        | (push_cast
           rw [hca₀, RingHom.map_add, sub_sub, add_comm])
        | (rw [Subring.coe_add, hca₀, RingHom.map_add, sub_sub, add_comm])
        | (simp only [ValuationSubring.coe_add, hca₀, RingHom.map_add, sub_sub, add_comm])
    rw [hid]
    exact hord

  have haffV : IsAffineGeomPlace k N (P.reduceFst V) := by
    by_contra hna
    exact absurd hposV (not_lt.mpr (isCuspidal_of_not_isAffineGeomPlace_reduceFst P V hna (a + a₀')))

  refine (exists_ord_jFun_sub_pos_of_isAffineGeomPlace_reduceFst P V haffV).elim fun a'' h'' => ?_
  have hab : (a'' : AlgebraicClosure ℚ) = ((a + a₀' : A) : AlgebraicClosure ℚ) :=
    (hasValue_of_ord_sub_pos V h''.1).unique (hasValue_of_ord_sub_pos V hposV)
  have ha''eq : a'' = a + a₀' := Subtype.ext hab
  have hjV : (P.reduceFst V).evalAt (jGeomGen k N) = red a'' :=
    evalAt_eq_of_hasValue _ (hasValue_of_ord_sub_pos _ h''.2)
  have hredV : red a'' = w.evalAt (jGeomGen k N) := by
    rw [ha''eq, RingHom.map_add, hreda, zero_add, hreda₀']
  show (P.reduceFst V).IsRational ∧ IsAffineGeomPlace k N (P.reduceFst V) ∧
    (P.reduceFst V).evalAt (jGeomGen k N) ∈ ssJSet q k
  refine ⟨isRational_of_isAlgClosed N _, haffV, ?_⟩
  rw [hjV, hredV]
  exact hwss.2.2

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem reduceFst_eq_of_forall_hasValue_iff
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K))
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hV : ∀ (t : ↥(modularFunctionFieldBar (N * q)))
      (_ : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K),
      ∃ a : A, V.HasValue t (a : AlgebraicClosure ℚ) ∧
        ((∃ h₁ : t ∈ R.R₁.integers, w.HasValue (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k)) ↔
          a ∈ IsLocalRing.maximalIdeal A)) :
    P.reduceFst V = w := by
  by_contra hne
  have hw'' : P.reduceFst V ∈ ssPlaces q N k :=
    reduceFst_mem_ssPlaces_of_forall_hasValue_iff R hqN hmodel hO W hW hreg hval K w hw hk₀ V hV

  refine (exists_mem_jIntegralClosure_ord_residues_pos_and_eq_zero_of_ne R hqN K hk₀ w (P.reduceFst V) (hW w hw)
    hw'' (Ne.symm hne)).elim fun g hg => ?_
  refine hg.elim fun hgC hg' => ?_
  refine hg'.elim fun h₁ hg'' => ?_
  refine hg''.elim fun h₂ hconj => ?_

  refine (hV g hgC).elim fun a ha' => ?_
  have hne₁g : (R.residue₁ ⟨g, h₁⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := by
    intro h0
    have h := hconj.1
    rw [h0, Place.ord_zero] at h
    exact lt_irrefl _ h
  have hne₂g : (R.residue₂ ⟨g, h₂⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := by
    intro h0
    have h := hconj.2.1
    rw [h0, Place.ord_zero] at h
    exact lt_irrefl _ h
  have ha : a ∈ IsLocalRing.maximalIdeal A := ha'.2.mp ⟨h₁, hasValue_zero_of_ord_pos w hne₁g hconj.1⟩

  have h₁f : g - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)
      ∈ R.R₁.integers := sub_mem h₁ ((R.R₁.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2)
  have h₂f : g - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)
      ∈ R.R₂.integers := sub_mem h₂ ((R.R₂.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2)
  have hR₁ := residue₁_sub_algebraMap_eq R g h₁ a ha
  have hR₂ := residue₂_sub_algebraMap_eq R g h₂ a ha
  have hf0 : g - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    apply hne₁g
    rw [← hR₁]
    have hz : (⟨_, h₁f⟩ : R.R₁.integers) = 0 := Subtype.ext h0
    exact (congrArg R.residue₁ hz).trans (RingHom.map_zero R.residue₁)

  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  refine (HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) _ hf0).elim fun D hDd => ?_
  have hD := hDd.1

  have hfix := frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces hqN P (P.reduceFst V) hw''
  have hlaw := hO _ h₁f h₂f
    (by
      intro h0
      apply hne₁g
      rw [← hR₁]
      exact (congrArg R.ι h0).trans (RingHom.map_zero R.ι))
    (by
      intro h0
      apply hne₂g
      rw [← hR₂]
      exact (congrArg R.ι h0).trans (RingHom.map_zero R.ι))
    D hD (P.reduceFst V) hfix hw''.2.1
  rw [hR₁, hR₂, hconj.2.2.1, ← ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr (P.reduceFst V),
    hconj.2.2.2, add_zero] at hlaw

  have hgint := (R.mem_nodeIntegers_iff (P.reduceFst V) g).mp
    (mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure R hqN K (P.reduceFst V) hw'' g hgC).1
  have hle : D V ≤ Finsupp.mapDomain P.reduceFst D (P.reduceFst V) := by
    refine le_mapDomain_apply_of_nonneg D P.reduceFst (P.reduceFst V) V rfl (fun V' _ hV' => ?_)
    rw [hD V']
    exact Place.ord_nonneg_of_mem V' (sub_mem (hgint.2.2 V' hV') (V'.algebraMap_mem' _))
  have hDV : 0 < D V := by
    rw [hD V]
    exact ord_sub_algebraMap_pos V ha'.1 hf0
  rw [hlaw] at hle
  omega

open ModularCurve.NodeLocalized in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem exists_place_horizontal
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K))
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (𝔭 : Ideal ↥(jIntegralClosure (N * q) A K)) [𝔭.IsPrime] (h𝔭 : 𝔭.height = 1)
    (hq𝔭 : ((q : ℕ) : ↥(jIntegralClosure (N * q) A K)) ∉ 𝔭)
    (h𝔭w : ∀ (t : ↥(modularFunctionFieldBar (N * q)))
      (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K),
      (⟨(t : LaurentSeries (AlgebraicClosure ℚ)), ht⟩ : ↥(jIntegralClosure (N * q) A K)) ∈ 𝔭 →
        ∃ h₁ : t ∈ R.R₁.integers, w.HasValue (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k)) :
    ∃ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      (∀ g : ↥(modularFunctionFieldBar (N * q)),
          (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (N * q) K →
          ((∃ r s : ↥(jIntegralClosure (N * q) A K), s ∉ 𝔭 ∧
              (g : LaurentSeries (AlgebraicClosure ℚ)) * (s : LaurentSeries (AlgebraicClosure ℚ)) = r) ↔
            g ∈ V.toValuationSubring))
      ∧ P.reduceFst V = w :=
  (R.exists_place_forall_iff_mem_and_hasValue_of_height_one_of_natCast_notMem hqN P.red_surjective_of_level K w
      (hW w hw) 𝔭 h𝔭 hq𝔭 h𝔭w).elim fun V hV =>
    ⟨V, hV.1,
      reduceFst_eq_of_forall_hasValue_iff R hqN hmodel hO W hW hreg hval K hk₀ w hw V hV.2⟩

private theorem isNoetherianRing_of_surjective_localization {C S : Type*} [CommRing C] [CommRing S]
    [IsNoetherianRing C] (m : Ideal C) [m.IsPrime] (f : Localization.AtPrime m →+* S)
    (hf : Function.Surjective f) : IsNoetherianRing S :=
  haveI : IsNoetherianRing (Localization.AtPrime m) :=
    IsLocalization.isNoetherianRing m.primeCompl (Localization.AtPrime m) inferInstance
  isNoetherianRing_of_surjective (Localization.AtPrime m) S f hf

private theorem exists_surjective_localization_of_fractions {C S : Type*} [CommRing C] [CommRing S]
    [IsLocalRing S] (ι : C →+* S)
    (h : ∀ s : S, ∃ t u : C, ι u ∉ IsLocalRing.maximalIdeal S ∧ ι t = ι u * s) :
    ∃ (m : Ideal C) (_ : m.IsPrime) (f : Localization.AtPrime m →+* S), Function.Surjective f := by
  have hunit : ∀ y : ((IsLocalRing.maximalIdeal S).comap ι).primeCompl, IsUnit (ι y) := fun y =>
    by_contra fun hy => y.2 (Ideal.mem_comap.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hy))
  refine ⟨(IsLocalRing.maximalIdeal S).comap ι, Ideal.IsPrime.comap ι,
    IsLocalization.lift (S := Localization.AtPrime ((IsLocalRing.maximalIdeal S).comap ι)) hunit,
    fun s => ?_⟩
  obtain ⟨t, u, hu, htu⟩ := h s
  have hu' : u ∈ ((IsLocalRing.maximalIdeal S).comap ι).primeCompl :=
    fun hmem => hu (Ideal.mem_comap.mp hmem)
  refine ⟨IsLocalization.mk' (Localization.AtPrime ((IsLocalRing.maximalIdeal S).comap ι)) t ⟨u, hu'⟩, ?_⟩
  rw [IsLocalization.lift_mk'_spec]
  exact htu

private theorem exists_mul_eq_of_forall_height_one {C : Type*} [CommRing C] [IsDomain C] [IsNoetherianRing C]
    [IsIntegrallyClosed C] (m : Ideal C) [m.IsPrime] (t₀ c₀ : C) (hc₀ : c₀ ≠ 0)
    (h : ∀ (p : Ideal C) [p.IsPrime], p.height = 1 → p ≤ m → ∃ r s : C, s ∉ p ∧ t₀ * s = r * c₀) :
    ∃ a u : C, u ∉ m ∧ t₀ * u = a * c₀ := by
  haveI : IsNoetherianRing (Localization.AtPrime m) :=
    IsLocalization.isNoetherianRing m.primeCompl (Localization.AtPrime m) inferInstance
  haveI : IsIntegrallyClosed (Localization.AtPrime m) :=
    isIntegrallyClosed_of_isLocalization (R := C) (S := Localization.AtPrime m) m.primeCompl
      m.primeCompl_le_nonZeroDivisors
  have hinj := IsFractionRing.injective C (FractionRing C)
  have hc₀' : algebraMap C (FractionRing C) c₀ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hc₀
  have hx : ∀ (p : Ideal (Localization.AtPrime m)) [p.IsPrime], p.height = 1 →
      ∃ r s : Localization.AtPrime m, s ∉ p ∧
        (algebraMap C (FractionRing C) t₀ / algebraMap C (FractionRing C) c₀)
            * algebraMap (Localization.AtPrime m) (FractionRing C) s
          = algebraMap (Localization.AtPrime m) (FractionRing C) r := by
    intro p hp hp1
    haveI hq : (p.comap (algebraMap C (Localization.AtPrime m))).IsPrime := Ideal.IsPrime.comap _
    have hq1 : (p.comap (algebraMap C (Localization.AtPrime m))).height = 1 := by
      rw [← hp1]
      exact IsLocalization.height_under m.primeCompl p
    have hqm : p.comap (algebraMap C (Localization.AtPrime m)) ≤ m := fun x hx =>
      by_contra fun hxm =>
        hp.ne_top (Ideal.eq_top_of_isUnit_mem p (Ideal.mem_comap.mp hx)
          (IsLocalization.map_units (Localization.AtPrime m) (⟨x, hxm⟩ : m.primeCompl)))
    obtain ⟨r, s, hs, hrs⟩ := h _ hq1 hqm
    refine ⟨algebraMap C (Localization.AtPrime m) r, algebraMap C (Localization.AtPrime m) s,
      fun hsp => hs (Ideal.mem_comap.mpr hsp), ?_⟩
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, div_mul_eq_mul_div,
      div_eq_iff hc₀', ← map_mul, ← map_mul, hrs]
  obtain ⟨ρ, hρ⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_forall_height_eq_one
    (R := Localization.AtPrime m) (FractionRing C)
    (algebraMap C (FractionRing C) t₀ / algebraMap C (FractionRing C) c₀) hx
  obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective m.primeCompl ρ
  have e : algebraMap (Localization.AtPrime m) (FractionRing C)
        (IsLocalization.mk' (Localization.AtPrime m) a u) * algebraMap C (FractionRing C) u
      = algebraMap C (FractionRing C) a := by
    rw [IsScalarTower.algebraMap_apply C (Localization.AtPrime m) (FractionRing C) (u : C),
      IsScalarTower.algebraMap_apply C (Localization.AtPrime m) (FractionRing C) a, ← map_mul,
      IsLocalization.mk'_spec]
  rw [hρ, div_mul_eq_mul_div, div_eq_iff hc₀'] at e
  exact ⟨a, u, u.2, hinj (by simpa only [map_mul] using e)⟩

private theorem exists_mul_mem_jIntegralClosure {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    {N : ℕ} [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (z : LaurentSeries (AlgebraicClosure ℚ)) (hz : z ∈ NodeLocalized.fieldOver (N * q) K) :
    ∃ c₀ t₀ : ↥(NodeLocalized.jIntegralClosure (N * q) A K),
      c₀ ≠ 0 ∧ z * (c₀ : LaurentSeries (AlgebraicClosure ℚ)) = t₀ := by
  obtain ⟨c, s₁, hc, hs₁, hne, hx⟩ :=
    (ModularCurve.jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level A N
      (ModularCurve.exists_phiIrreducible (N * q)).choose K).2.2.1 z hz
  exact ⟨⟨s₁, mem_jIntegralClosure_of_mem_jRing (N * q) A K hs₁⟩, ⟨c, hc⟩,
    fun h => hne (congrArg Subtype.val h), hx⟩

private theorem exists_mul_eq_of_natCast_mem
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N))
    (𝔭 : Ideal ↥(NodeLocalized.jIntegralClosure (N * q) A K)) [𝔭.IsPrime] (h𝔭 : 𝔭.height = 1)
    (hq : ((q : ℕ) : ↥(NodeLocalized.jIntegralClosure (N * q) A K)) ∈ 𝔭)
    (s : ↥(R.nodeIntegersOver K w)) :
    ∃ r u : ↥(NodeLocalized.jIntegralClosure (N * q) A K), u ∉ 𝔭 ∧
      ((s : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
        * (u : LaurentSeries (AlgebraicClosure ℚ)) = r := by
  have hs := (R.mem_nodeIntegersOver_iff K w s).mp s.2
  have hn := (R.mem_nodeIntegers_iff w s).mp hs.1
  exact exists_mul_eq_of_height_one_of_natCast_mem_level N hqN red K 𝔭 h𝔭 hq
    (s : ↥(modularFunctionFieldBar (N * q))) hs.2
    ((R.mem_integersFst_iff _).mp hn.1) ((R.mem_integersSnd_iff _).mp hn.2.1)

private theorem inv_mem_of_isUnit_mk {F : Type*} [Field F] (S : ValuationSubring F) {f : F} {hf : f ∈ S}
    (hu : IsUnit (⟨f, hf⟩ : S)) : f⁻¹ ∈ S := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h1 : f * (v : F) = 1 := by
    have h := congrArg (fun z : S => (z : F)) hv
    simpa using h
  rw [← eq_inv_of_mul_eq_one_right h1]
  exact v.2

private theorem inv_mem_and_ne_zero_of_residue_ne_zero {L : Type*} [Field L] {A₀ : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F] {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A₀) Fbar]
    (R₀ : RegularProlongation A₀ F Fbar) {f : F} (hf : f ∈ R₀.integers) (hres : R₀.residue ⟨f, hf⟩ ≠ 0) :
    f⁻¹ ∈ R₀.integers ∧ f ≠ 0 := by
  have hu : IsUnit (⟨f, hf⟩ : R₀.integers) := R₀.isUnit_of_residue_ne_zero hres
  refine ⟨inv_mem_of_isUnit_mk _ hu, ?_⟩
  rintro rfl
  apply hres
  have h0 : (⟨(0 : F), hf⟩ : R₀.integers) = 0 := Subtype.ext rfl
  rw [h0, map_zero]

private theorem inv_mem_of_evalAt_ne_zero {K₀ F₀ : Type*} [Field K₀] [Field F₀] [Algebra K₀ F₀] (v : Place K₀ F₀)
    {g : F₀} (hmem : g ∈ v.toValuationSubring) (hg : v.evalAt g ≠ 0) : g⁻¹ ∈ v.toValuationSubring := by
  have hres : residue v.toValuationSubring ⟨g, hmem⟩ ≠ 0 := by
    intro h0
    apply hg
    rw [v.evalAt_of_mem hmem, h0, ← map_zero (algebraMap K₀ v.ResidueField), v.residueInv_algebraMap]
  exact inv_mem_of_isUnit_mk _ ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp hres)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem hasValue_residueFst_zero_of_mem_maximalIdeal
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (ι : ↥(NodeLocalized.jIntegralClosure (N * q) A K) →+* ↥(R.nodeIntegersOver K w))
    (hι : ∀ t : ↥(NodeLocalized.jIntegralClosure (N * q) A K),
      (((ι t : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
        = (t : LaurentSeries (AlgebraicClosure ℚ)))
    (t : ↥(modularFunctionFieldBar (N * q)))
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.jIntegralClosure (N * q) A K)
    (hm : ι ⟨_, ht⟩ ∈ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) :
    ∃ h₁ : t ∈ R.R₁.integers, w.HasValue (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k) := by
  have hwss : w ∈ ssPlaces q N k := hW w hw
  have hnode := mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure R hqN K w hwss t ht
  have htK : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (N * q) K := ht.1
  have htS : t ∈ R.nodeIntegersOver K w := (R.mem_nodeIntegersOver_iff K w t).mpr ⟨hnode.1, htK⟩
  have hιx : ι ⟨_, ht⟩ = (⟨t, htS⟩ : ↥(R.nodeIntegersOver K w)) := Subtype.ext (Subtype.ext (hι ⟨_, ht⟩))
  rw [hιx] at hm
  have hnu : ¬ IsUnit (⟨t, htS⟩ : ↥(R.nodeIntegersOver K w)) :=
    mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hm)
  have hn := (R.mem_nodeIntegers_iff w t).mp hnode.1
  have h₁ := hn.1
  have h₂ := hn.2.1
  have hfib := hn.2.2
  have hres : (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) ∈ w.toValuationSubring := hnode.2.1 h₁
  have hrat : w.IsRational := hwss.1
  obtain ⟨c, hc, -⟩ := w.exists_hasValue_of_surjective hrat hres
  refine ⟨h₁, ?_⟩
  by_cases hc0 : c = 0
  · subst hc0
    exact hc
  · exfalso
    apply hnu
    obtain ⟨V, hV⟩ := reduceFst_surjective P w
    have hvalA : R.ValueIntegralityLaw w := valueIntegralityLaw_of_orderLawFixed R hqN hO w hwss
    have hred : ∀ (V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV' : P.reduceFst V' = w),
        red ⟨V'.evalAt t, hvalA t (R.nodeIntegersOver_le K w htS) V' hV'⟩ = c := by
      intro V' hV'
      have h := hasValue_nodeResidueFst_red_evalAt_of_orderLawFixed R hqN hmodel hO W hW hreg hval K w hw hvalA
        ⟨t, htS⟩ V' hV'
      rw [nodeResidue₁_apply] at h
      exact h.unique hc
    have hB₁ := inv_mem_and_ne_zero_of_residue_ne_zero R.R₁ h₁ (by
      intro h0
      apply hc.ne_zero hc0
      rw [residue₁_apply, h0, RingHom.map_zero])
    have hb := hasValue_nodeResidueSnd_red_evalAt_of_orderLawFixed R hqN hmodel hO W hW hreg hval K w hw hvalA
      ⟨t, htS⟩ V hV
    rw [nodeResidue₂_apply, hred V hV] at hb
    have hB₂ := inv_mem_and_ne_zero_of_residue_ne_zero R.R₂ h₂ (by
      intro h0
      apply hb.ne_zero hc0
      rw [residue₂_apply, h0, RingHom.map_zero])
    have hinvfib : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V' = w →
        t⁻¹ ∈ V'.toValuationSubring := by
      intro V' hV'
      refine inv_mem_of_evalAt_ne_zero V' (hfib V' hV') ?_
      intro hev
      apply hc0
      rw [← hred V' hV']
      have hz : (⟨V'.evalAt t, hvalA t (R.nodeIntegersOver_le K w htS) V' hV'⟩ : A) = 0 :=
        Subtype.ext (by simp [hev])
      rw [hz, RingHom.map_zero]
    have hinvK : ((t⁻¹ : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
        ∈ NodeLocalized.fieldOver (N * q) K := by
      simpa using inv_mem htK
    refine IsUnit.of_mul_eq_one (⟨t⁻¹, (R.mem_nodeIntegersOver_iff K w _).mpr
      ⟨(R.mem_nodeIntegers_iff w _).mpr ⟨hB₁.1, hB₂.1, hinvfib⟩, hinvK⟩⟩ : ↥(R.nodeIntegersOver K w)) ?_
    exact Subtype.ext (mul_inv_cancel₀ hB₁.2)

private theorem exists_nodeInclusion
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) :
    ∃ ι : ↥(NodeLocalized.jIntegralClosure (N * q) A K) →+* ↥(R.nodeIntegersOver K w),
    ∀ t : ↥(NodeLocalized.jIntegralClosure (N * q) A K),
      (((ι t : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
        = (t : LaurentSeries (AlgebraicClosure ℚ)) := by
  have hw' : w ∈ ssPlaces q N k := hW w hw
  have hBar : ∀ t : ↥(NodeLocalized.jIntegralClosure (N * q) A K),
      (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (N * q) := by
    intro t
    obtain ⟨x, y, -, -, hy, hxy⟩ :=
      R.exists_mul_eq_of_mem_fieldOver_nodeIntegersOver hqN K w hw' (t : LaurentSeries (AlgebraicClosure ℚ)) t.2.1
    have hy' : (y : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := fun h => hy (Subtype.ext h)
    rw [(eq_div_iff hy').mpr hxy]
    exact div_mem x.2 y.2
  let f : ↥(NodeLocalized.jIntegralClosure (N * q) A K) →+* ↥(modularFunctionFieldBar (N * q)) :=
    { toFun := fun t => ⟨(t : LaurentSeries (AlgebraicClosure ℚ)), hBar t⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have hS : ∀ t : ↥(NodeLocalized.jIntegralClosure (N * q) A K), f t ∈ R.nodeIntegersOver K w := fun t =>
    (R.mem_nodeIntegersOver_iff K w (f t)).mpr
      ⟨(R.mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure hqN K w hw' (f t) t.2).1, t.2.1⟩
  exact ⟨f.codRestrict (R.nodeIntegersOver K w) hS, fun _ => rfl⟩

private theorem exists_fraction_of_mem_nodeRing
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K))
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (ι : ↥(NodeLocalized.jIntegralClosure (N * q) A K) →+* ↥(R.nodeIntegersOver K w))
    (hι : ∀ t : ↥(NodeLocalized.jIntegralClosure (N * q) A K),
      (((ι t : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
        = (t : LaurentSeries (AlgebraicClosure ℚ)))
    (s : ↥(R.nodeIntegersOver K w)) :
    ∃ t u : ↥(NodeLocalized.jIntegralClosure (N * q) A K),
      ι u ∉ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) ∧ ι t = ι u * s := by
  haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
  haveI : IsNoetherianRing ↥(NodeLocalized.jIntegralClosure (N * q) A K) :=
    (ModularCurve.jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level A N
      (ModularCurve.exists_phiIrreducible (N * q)).choose K).1
  haveI : IsIntegrallyClosed ↥(NodeLocalized.jIntegralClosure (N * q) A K) :=
    (ModularCurve.jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level A N
      (ModularCurve.exists_phiIrreducible (N * q)).choose K).2.1
  have hw' : w ∈ ssPlaces q N k := hW w hw
  obtain ⟨c₀, t₀, hc₀, ht₀⟩ := exists_mul_mem_jIntegralClosure A K _
    ((R.mem_nodeIntegersOver_iff K w s).mp s.2).2
  have hc₀' : (c₀ : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := fun h => hc₀ (Subtype.ext h)
  have hcl : ∀ (𝔭 : Ideal ↥(NodeLocalized.jIntegralClosure (N * q) A K)) [𝔭.IsPrime],
      𝔭.height = 1 → 𝔭 ≤ (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)).comap ι →
      ∃ r u₁ : ↥(NodeLocalized.jIntegralClosure (N * q) A K), u₁ ∉ 𝔭 ∧ t₀ * u₁ = r * c₀ := by
    intro 𝔭 h𝔭 h1 hle
    by_cases hq : ((q : ℕ) : ↥(NodeLocalized.jIntegralClosure (N * q) A K)) ∈ 𝔭
    · obtain ⟨r, u₁, hu₁, hru⟩ := exists_mul_eq_of_natCast_mem R hqN K w 𝔭 h1 hq s
      refine ⟨r, u₁, hu₁, Subtype.ext ?_⟩
      rw [Subring.coe_mul, Subring.coe_mul, ← ht₀, mul_right_comm, hru]
    · obtain ⟨V, hV, hVw⟩ :=
        exists_place_horizontal R hqN hmodel hO W hW hreg hval K hk₀ w hw 𝔭 h1 hq
          (fun t ht hmem =>
            hasValue_residueFst_zero_of_mem_maximalIdeal R hqN hmodel hO W hW hreg hval K w hw ι hι t ht
              (Ideal.mem_comap.mp (hle hmem)))
      have hsV : (s : ↥(modularFunctionFieldBar (N * q))) ∈ V.toValuationSubring :=
        ((R.mem_nodeIntegers_iff w s).mp ((R.mem_nodeIntegersOver_iff K w s).mp s.2).1).2.2 V hVw
      obtain ⟨r, u₁, hu₁, hru⟩ :=
        (hV (s : ↥(modularFunctionFieldBar (N * q))) ((R.mem_nodeIntegersOver_iff K w s).mp s.2).2).mpr hsV
      exact ⟨r, u₁, hu₁, Subtype.ext (by rw [Subring.coe_mul, Subring.coe_mul, ← ht₀, mul_right_comm, hru])⟩
  obtain ⟨a, u, hu, hau⟩ := exists_mul_eq_of_forall_height_one
    ((IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)).comap ι) t₀ c₀ hc₀ hcl
  refine ⟨a, u, fun h => hu (Ideal.mem_comap.mpr h), ?_⟩
  have h1 := congrArg Subtype.val hau
  rw [Subring.coe_mul, Subring.coe_mul, ← ht₀] at h1
  have hLS : (a : LaurentSeries (AlgebraicClosure ℚ))
      = (u : LaurentSeries (AlgebraicClosure ℚ))
        * ((s : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) :=
    (mul_right_cancel₀ hc₀' (by rw [← h1]; ring)).symm
  apply Subtype.ext
  apply Subtype.ext
  rw [Subring.coe_mul]
  push_cast
  rw [hι a, hι u]
  exact hLS

private theorem exists_surjective_localization_normalisation
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K))
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) :
    ∃ (m : Ideal ↥(NodeLocalized.jIntegralClosure (N * q) A K)) (_ : m.IsPrime)
      (f : Localization.AtPrime m →+* ↥(R.nodeIntegersOver K w)), Function.Surjective f :=
  haveI : IsLocalRing ↥(R.nodeIntegersOver K w) := isLocalRing_nodeRing R hqN hO W hW hreg K w hw
  (exists_nodeInclusion R hqN W hW K w hw).elim fun ι hι =>
    exists_surjective_localization_of_fractions ι
      (exists_fraction_of_mem_nodeRing R hqN hmodel hO W hW hreg hval K hk₀ w hw ι hι)

private theorem isNoetherianRing_nodeRing
{q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K))
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) (c : R.NodeCoordinates K w) :
    IsNoetherianRing ↥(R.nodeIntegersOver K w) :=
  haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
  haveI : IsNoetherianRing ↥(NodeLocalized.jIntegralClosure (N * q) A K) :=
    (ModularCurve.jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level A N
      (ModularCurve.exists_phiIrreducible (N * q)).choose K).1
  (exists_surjective_localization_normalisation R hqN hmodel hO W hW hreg hval K hk₀ w hw).elim
    fun m hm => hm.elim fun hprime hf => hf.elim fun f hsurj =>
      haveI : m.IsPrime := hprime
      isNoetherianRing_of_surjective_localization m f hsurj

end NodeRingNoetherian

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K))
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) (c : R.NodeCoordinates K w) :
    IsLocalRing ↥(R.nodeIntegersOver K w) ∧ IsNoetherianRing ↥(R.nodeIntegersOver K w) := by
  exact ⟨NodeRingNoetherian.isLocalRing_nodeRing R hqN hO W hW hreg K w hw,
    NodeRingNoetherian.isNoetherianRing_nodeRing R hqN hmodel hO W hW hreg hval K hk₀ w hw c⟩

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_isLocalRing_and_isNoetherianRing_nodeIntegersOver_of_nodeCoordinates_of_orderLawFixed_of_range_redRestrict
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_isLocalRing_and_isNoetherianRing_nodeIntegersOver_of_nodeCoordinates_of_orderLawFixed_of_range_redRestrict (solution)
