-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.reduceFst_eq_or_eq_arithFrobC_smul_of_forall_hasValue_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/34932e54-c86a-506b-97cf-c540374f86af

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_NodeDescentTower
import Theorems.Thm_ValuationSubring_exists_forall_apply_eq_and_isFrobeniusAt_natCard_of_liesOverPrime
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces_univ
import Theorems.Thm_ModularCurve_PlaceSpecialization_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_and_reduceSnd_arithmeticGalois_smul_of_isFrobeniusAt_pow
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_jIntegralClosure_ord_residues_pos_and_eq_zero_of_ne
import Theorems.Thm_ModularCurve_isRational_place_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_jFun_sub_jQFun_sub
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isCuspidal_of_not_isAffineGeomPlace_reduceFst
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_mem_ssJSet_map_of_isAlgClosed
import Theorems.Thm_ModularCurve_exists_algebra_ratFunc_modularFunctionFieldC_finite_isSeparable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceFst_eq_or_eq_arithFrobC_smul_of_forall_hasValue_iff
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_frobeniusModL"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of"
set_option autoImplicit false

open AlgebraicCurve ModularCurve
open ModularCurve.NodeLocalized
open ModularCurve.PlaceSpecialization

section FiniteField

variable {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [CharP k q]

private theorem mem_of_pow_eq_of_card {n : ℕ} (hn : 1 < n) (T : Finset k) (hT : T.card = n)
    (hroot : ∀ x ∈ T, x ^ n = x) {a : k} (ha : a ^ n = a) : a ∈ T := by
  classical
  have hne : (Polynomial.X ^ n - Polynomial.X : Polynomial k) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hn
  have hFcard : (Polynomial.X ^ n - Polynomial.X : Polynomial k).roots.toFinset.card ≤ n := by
    refine (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans ?_)
    rw [FiniteField.X_pow_card_sub_X_natDegree_eq k hn]
  have hsub : T ⊆ (Polynomial.X ^ n - Polynomial.X : Polynomial k).roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
    simp [hroot x hx]
  have hEq : T = (Polynomial.X ^ n - Polynomial.X : Polynomial k).roots.toFinset :=
    Finset.eq_of_subset_of_card_le hsub (hFcard.trans hT.ge)
  rw [hEq, Multiset.mem_toFinset, Polynomial.mem_roots hne]
  simp [ha]

private theorem natCast_pow_char (n : ℕ) : (n : k) ^ q = n := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_pow (Fact.out : q.Prime).ne_zero]
  | succ n ih => rw [Nat.cast_succ, add_pow_char _ _ q, ih, one_pow]

private theorem exists_natCast_eq {x : k} (hx : x ^ q = x) : ∃ n : ℕ, (n : k) = x := by
  classical
  have hT : ((Finset.range q).image (Nat.cast : ℕ → k)).card = q := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    exact CharP.natCast_injOn_Iio k q (by simpa using ha) (by simpa using hb) hab
  have hmem := mem_of_pow_eq_of_card (Fact.out : q.Prime).one_lt _ hT (fun y hy => by
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hy
    exact natCast_pow_char n) hx
  obtain ⟨n, -, hn⟩ := Finset.mem_image.mp hmem
  exact ⟨n, hn⟩

private theorem exists_natCast_add_natCast_mul_eq {β : k} (hβ2 : β ^ (q ^ 2) = β) (hβ1 : β ^ q ≠ β) {a : k}
    (ha : a ^ (q ^ 2) = a) : ∃ u v : ℕ, a = u + v * β := by
  classical
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  have hq2 : 1 < q ^ 2 := Nat.one_lt_pow two_ne_zero hq1
  have hnat2 : ∀ n : ℕ, (n : k) ^ (q ^ 2) = n := fun n => by
    rw [sq, pow_mul, natCast_pow_char, natCast_pow_char]

  have hv : ∀ u v u' v' : ℕ, (u : k) + v * β = u' + v' * β → (v : k) = v' := by
    intro u v u' v' h
    by_contra hne
    apply hβ1
    have hβeq : β = ((u' : k) - u) / ((v : k) - v') := by
      rw [eq_div_iff (sub_ne_zero.mpr hne)]
      linear_combination h
    rw [hβeq, div_pow, sub_pow_char, sub_pow_char, natCast_pow_char, natCast_pow_char, natCast_pow_char,
      natCast_pow_char]
  have hT : (((Finset.range q) ×ˢ (Finset.range q)).image fun uv : ℕ × ℕ => (uv.1 : k) + uv.2 * β).card = q ^ 2 := by
    rw [Finset.card_image_of_injOn, Finset.card_product, Finset.card_range, sq]
    rintro ⟨u, v⟩ huv ⟨u', v'⟩ huv' h
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio] at huv huv'
    have hvv : v = v' := CharP.natCast_injOn_Iio k q huv.2 huv'.2 (hv u v u' v' h)
    subst hvv
    have huu : u = u' := CharP.natCast_injOn_Iio k q huv.1 huv'.1 (add_right_cancel h)
    rw [huu]
  have hmem := mem_of_pow_eq_of_card hq2 _ hT (fun y hy => by
    obtain ⟨⟨u, v⟩, -, rfl⟩ := Finset.mem_image.mp hy
    simp only
    rw [add_pow_char_pow, mul_pow, hnat2, hnat2, hβ2]) ha
  obtain ⟨⟨u, v⟩, -, huv⟩ := Finset.mem_image.mp hmem
  exact ⟨u, v, huv.symm⟩

omit [Fact q.Prime] [CharP k q] in

private theorem pow_pow_eq_pow_of_odd {x : k} (hx : x ^ (q ^ 2) = x) {d : ℕ} (hd : Odd d) : x ^ (q ^ d) = x ^ q := by
  obtain ⟨m, rfl⟩ := hd
  induction m with
  | zero => rw [mul_zero, zero_add, pow_one]
  | succ m ih =>
    rw [show q ^ (2 * (m + 1) + 1) = q ^ (2 * m + 1) * q ^ 2 by ring, pow_mul, ih, ← pow_mul, mul_comm, pow_mul, hx]

end FiniteField

section Enlargement

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
  [IsAlgClosed k] (red : A →+* k)

omit [IsAlgClosed k] in

private theorem mem_of_mul_self_eq {α : AlgebraicClosure ℚ} {s p : ℕ}
    (h : α * α = (s : AlgebraicClosure ℚ) * α - (p : AlgebraicClosure ℚ)) : α ∈ A := by
  rw [← A.valuation_le_one_iff]
  by_contra hgt
  rw [not_le] at hgt
  have hs : A.valuation (s : AlgebraicClosure ℚ) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem _ s)
  have hp : A.valuation (p : AlgebraicClosure ℚ) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem _ p)
  have h1 : A.valuation (α * α) ≤ A.valuation α := by
    rw [h]
    refine (A.valuation.map_sub _ _).trans (max_le ?_ (hp.trans hgt.le))
    rw [map_mul]
    exact mul_le_of_le_one_left' hs
  rw [map_mul] at h1
  exact absurd h1 (not_le.mpr (by simpa [sq] using pow_lt_pow_right₀ hgt one_lt_two))

private theorem exists_quadratic_integer :
    ∃ (s p : ℤ) (α : AlgebraicClosure ℚ) (hα : α ∈ A),
      α * α = (s : AlgebraicClosure ℚ) * α - (p : AlgebraicClosure ℚ) ∧
      red ⟨α, hα⟩ ^ (q ^ 2) = red ⟨α, hα⟩ ∧ red ⟨α, hα⟩ ^ q ≠ red ⟨α, hα⟩ ∧
      FiniteDimensional ℚ (IntermediateField.adjoin ℚ {α}) ∧
      ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red (IntermediateField.adjoin ℚ {α})) := by
  classical
  have hq : q.Prime := Fact.out
  have hq1 : 1 < q := hq.one_lt
  have hq2 : 1 < q ^ 2 := Nat.one_lt_pow two_ne_zero hq1

  obtain ⟨b, hb2, hb1⟩ : ∃ b : k, b ^ (q ^ 2) = b ∧ b ^ q ≠ b := by
    have hcard2 : (Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots.toFinset.card = q ^ 2 := by
      rw [Multiset.toFinset_card_of_nodup
          (Polynomial.nodup_roots (galois_poly_separable q (q ^ 2) (dvd_pow_self q two_ne_zero))),
        ← Polynomial.Splits.natDegree_eq_card_roots (IsAlgClosed.splits _),
        FiniteField.X_pow_card_sub_X_natDegree_eq k hq2]
    have hcard1 : (Polynomial.X ^ q - Polynomial.X : Polynomial k).roots.toFinset.card ≤ q := by
      refine (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans ?_)
      rw [FiniteField.X_pow_card_sub_X_natDegree_eq k hq1]
    have hlt : (Polynomial.X ^ q - Polynomial.X : Polynomial k).roots.toFinset.card <
        (Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots.toFinset.card := by
      rw [hcard2]
      exact hcard1.trans_lt (by nlinarith)
    obtain ⟨b, hb₂, hb₁⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    refine ⟨b, ?_, fun h => hb₁ ?_⟩
    · have := (Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero k hq2)).mp (Multiset.mem_toFinset.mp hb₂)
      simpa [sub_eq_zero] using this
    · rw [Multiset.mem_toFinset, Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero k hq1)]
      simp [h]
  have hbq : (b ^ q) ^ q = b := by rw [← pow_mul, ← sq, hb2]

  obtain ⟨s, hs⟩ := exists_natCast_eq (x := b + b ^ q) (by rw [add_pow_char _ _ q, hbq, add_comm])
  obtain ⟨p, hp⟩ := exists_natCast_eq (x := b * b ^ q) (by rw [mul_pow, hbq, mul_comm])

  obtain ⟨α, hαrel⟩ : ∃ α : AlgebraicClosure ℚ,
      α * α = (s : AlgebraicClosure ℚ) * α - (p : AlgebraicClosure ℚ) := by
    have hdeg : (Polynomial.X ^ 2 - (Polynomial.C (s : AlgebraicClosure ℚ) * Polynomial.X -
        Polynomial.C (p : AlgebraicClosure ℚ))).degree = 2 := by
      compute_degree!
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ (by rw [hdeg]; decide)
    refine ⟨α, ?_⟩
    simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
      Polynomial.eval_C] at hα
    rw [← sq]
    exact sub_eq_zero.mp hα
  have hαA : α ∈ A := mem_of_mul_self_eq hαrel

  have hres : red ⟨α, hαA⟩ * red ⟨α, hαA⟩ = (s : k) * red ⟨α, hαA⟩ - (p : k) := by
    have hA : (⟨α, hαA⟩ : A) * ⟨α, hαA⟩ = (s : A) * ⟨α, hαA⟩ - (p : A) := Subtype.ext (by simpa using hαrel)
    have := congrArg red hA
    rwa [map_mul, map_sub, map_mul, map_natCast, map_natCast] at this
  have hfactor : (red ⟨α, hαA⟩ - b) * (red ⟨α, hαA⟩ - b ^ q) = 0 := by
    rw [hs, hp] at hres
    linear_combination hres
  have hβ : red ⟨α, hαA⟩ ^ (q ^ 2) = red ⟨α, hαA⟩ ∧ red ⟨α, hαA⟩ ^ q ≠ red ⟨α, hαA⟩ := by
    rcases mul_eq_zero.mp hfactor with h | h
    · rw [sub_eq_zero.mp h]
      exact ⟨hb2, hb1⟩
    · rw [sub_eq_zero.mp h]
      refine ⟨?_, fun h' => hb1 ?_⟩
      · rw [← pow_mul, mul_comm, pow_mul, hb2]
      · rw [hbq] at h'
        exact h'.symm
  refine ⟨s, p, α, hαA, by exact_mod_cast hαrel, hβ.1, hβ.2,
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) α).isIntegral, ?_⟩

  intro a ha
  obtain ⟨u, v, rfl⟩ := exists_natCast_add_natCast_mul_eq hβ.1 hβ.2 ha
  have hmemA : (u : AlgebraicClosure ℚ) + v * α ∈ A := add_mem (natCast_mem _ u) (mul_mem (natCast_mem _ v) hαA)
  have hmemK : (u : AlgebraicClosure ℚ) + v * α ∈ IntermediateField.adjoin ℚ {α} :=
    add_mem (natCast_mem _ u) (mul_mem (natCast_mem _ v) (IntermediateField.mem_adjoin_simple_self ℚ α))
  refine ⟨⟨(u : AlgebraicClosure ℚ) + v * α, hmemA, hmemK⟩, ?_⟩
  have hx : (⟨(u : AlgebraicClosure ℚ) + v * α, hmemA⟩ : A) = (u : A) + (v : A) * ⟨α, hαA⟩ := Subtype.ext (by simp)
  show red ⟨(u : AlgebraicClosure ℚ) + v * α, hmemA⟩ = _
  rw [hx, map_add, map_mul, map_natCast, map_natCast]

end Enlargement

section NormalForm

private theorem mul_add_sub_mul_eq {a : LaurentSeries (AlgebraicClosure ℚ)} {s p : ℤ}
    (hrel : a * a = (s : LaurentSeries (AlgebraicClosure ℚ)) * a - (p : LaurentSeries (AlgebraicClosure ℚ)))
    (g₀ g₁ : LaurentSeries (AlgebraicClosure ℚ)) :
    (g₀ + a * g₁) * (g₀ + ((s : LaurentSeries (AlgebraicClosure ℚ)) - a) * g₁) =
      g₀ ^ 2 + (s : LaurentSeries (AlgebraicClosure ℚ)) * g₀ * g₁ +
        (p : LaurentSeries (AlgebraicClosure ℚ)) * g₁ ^ 2 := by
  linear_combination (-(g₁ ^ 2)) * hrel

private theorem algebraMap_mul_self_eq {α : AlgebraicClosure ℚ} {s p : ℤ}
    (hrel : α * α = (s : AlgebraicClosure ℚ) * α - (p : AlgebraicClosure ℚ)) :
    algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) α *
        algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) α =
      (s : LaurentSeries (AlgebraicClosure ℚ)) *
          algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) α -
        (p : LaurentSeries (AlgebraicClosure ℚ)) := by
  rw [← map_mul, hrel, map_sub, map_mul, map_intCast, map_intCast]

private theorem mul_conjugate_eq {α : AlgebraicClosure ℚ} {s p : ℤ}
    (hrel : α * α = (s : AlgebraicClosure ℚ) * α - (p : AlgebraicClosure ℚ))
    (g₀ g₁ : LaurentSeries (AlgebraicClosure ℚ)) :
    (g₀ + algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) α * g₁) *
        (g₀ + ((s : LaurentSeries (AlgebraicClosure ℚ)) -
          algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) α) * g₁) =
      g₀ ^ 2 + (s : LaurentSeries (AlgebraicClosure ℚ)) * g₀ * g₁ +
        (p : LaurentSeries (AlgebraicClosure ℚ)) * g₁ ^ 2 :=
  mul_add_sub_mul_eq (algebraMap_mul_self_eq hrel) g₀ g₁

private def quadraticFieldOver (M : ℕ) [NeZero M] (a : LaurentSeries (AlgebraicClosure ℚ)) (s p : ℤ)
    (hrel : a * a = (s : LaurentSeries (AlgebraicClosure ℚ)) * a - (p : LaurentSeries (AlgebraicClosure ℚ)))
    (ha : a ∉ fieldOver M ⊥) : Subfield (LaurentSeries (AlgebraicClosure ℚ)) where
  carrier := {g | ∃ g₀ ∈ fieldOver M ⊥, ∃ g₁ ∈ fieldOver M ⊥, g = g₀ + a * g₁}
  zero_mem' := ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  one_mem' := ⟨1, one_mem _, 0, zero_mem _, by simp⟩
  add_mem' := by
    rintro x y ⟨x₀, hx₀, x₁, hx₁, rfl⟩ ⟨y₀, hy₀, y₁, hy₁, rfl⟩
    exact ⟨x₀ + y₀, add_mem hx₀ hy₀, x₁ + y₁, add_mem hx₁ hy₁, by ring⟩
  neg_mem' := by
    rintro x ⟨x₀, hx₀, x₁, hx₁, rfl⟩
    exact ⟨-x₀, neg_mem hx₀, -x₁, neg_mem hx₁, by ring⟩
  mul_mem' := by
    rintro x y ⟨x₀, hx₀, x₁, hx₁, rfl⟩ ⟨y₀, hy₀, y₁, hy₁, rfl⟩
    refine ⟨x₀ * y₀ - (p : LaurentSeries (AlgebraicClosure ℚ)) * (x₁ * y₁),
      sub_mem (mul_mem hx₀ hy₀) (mul_mem (intCast_mem _ p) (mul_mem hx₁ hy₁)),
      x₀ * y₁ + x₁ * y₀ + (s : LaurentSeries (AlgebraicClosure ℚ)) * (x₁ * y₁),
      add_mem (add_mem (mul_mem hx₀ hy₁) (mul_mem hx₁ hy₀)) (mul_mem (intCast_mem _ s) (mul_mem hx₁ hy₁)), ?_⟩
    linear_combination (x₁ * y₁) * hrel
  inv_mem' := by
    rintro x ⟨x₀, hx₀, x₁, hx₁, rfl⟩
    by_cases h1 : x₁ = 0
    · subst h1
      exact ⟨x₀⁻¹, inv_mem hx₀, 0, zero_mem _, by simp⟩
    by_cases hx : x₀ + a * x₁ = 0
    · rw [hx]
      exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩

    have hconj : x₀ + ((s : LaurentSeries (AlgebraicClosure ℚ)) - a) * x₁ ≠ 0 := by
      intro h0
      apply ha
      have h2 : a = ((s : LaurentSeries (AlgebraicClosure ℚ)) * x₁ + x₀) / x₁ := by
        rw [eq_div_iff h1]
        linear_combination -h0
      rw [h2]
      exact div_mem (add_mem (mul_mem (intCast_mem _ s) hx₁) hx₀) hx₁
    have hn := mul_add_sub_mul_eq hrel x₀ x₁
    set n := x₀ ^ 2 + (s : LaurentSeries (AlgebraicClosure ℚ)) * x₀ * x₁ +
      (p : LaurentSeries (AlgebraicClosure ℚ)) * x₁ ^ 2 with hn_def
    have hn0 : n ≠ 0 := by
      rw [← hn]
      exact mul_ne_zero hx hconj
    have hnF : n ∈ fieldOver M ⊥ :=
      add_mem (add_mem (pow_mem hx₀ 2) (mul_mem (mul_mem (intCast_mem _ s) hx₀) hx₁))
        (mul_mem (intCast_mem _ p) (pow_mem hx₁ 2))
    refine ⟨(x₀ + (s : LaurentSeries (AlgebraicClosure ℚ)) * x₁) / n,
      div_mem (add_mem hx₀ (mul_mem (intCast_mem _ s) hx₁)) hnF, -x₁ / n, div_mem (neg_mem hx₁) hnF, ?_⟩
    apply inv_eq_of_mul_eq_one_right
    have hsplit : (x₀ + (s : LaurentSeries (AlgebraicClosure ℚ)) * x₁) / n + a * (-x₁ / n) =
        (x₀ + ((s : LaurentSeries (AlgebraicClosure ℚ)) - a) * x₁) / n := by
      ring
    rw [hsplit, ← mul_div_assoc, hn, div_self hn0]

private theorem mem_quadraticFieldOver_iff {M : ℕ} [NeZero M] {a : LaurentSeries (AlgebraicClosure ℚ)} {s p : ℤ}
    {hrel : a * a = (s : LaurentSeries (AlgebraicClosure ℚ)) * a - (p : LaurentSeries (AlgebraicClosure ℚ))}
    {ha : a ∉ fieldOver M ⊥} {g : LaurentSeries (AlgebraicClosure ℚ)} :
    g ∈ quadraticFieldOver M a s p hrel ha ↔ ∃ g₀ ∈ fieldOver M ⊥, ∃ g₁ ∈ fieldOver M ⊥, g = g₀ + a * g₁ :=
  Iff.rfl

private theorem exists_add_mul_eq_of_mem_fieldOver_adjoin (M : ℕ) [NeZero M] {α : AlgebraicClosure ℚ} {s p : ℤ}
    (hrel : α * α = (s : AlgebraicClosure ℚ) * α - (p : AlgebraicClosure ℚ))
    (hα : algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) α ∉ fieldOver M ⊥)
    {g : LaurentSeries (AlgebraicClosure ℚ)} (hg : g ∈ fieldOver M (IntermediateField.adjoin ℚ {α})) :
    ∃ g₀ ∈ fieldOver M ⊥, ∃ g₁ ∈ fieldOver M ⊥,
      g = g₀ + algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) α * g₁ := by
  set T := quadraticFieldOver M _ s p (algebraMap_mul_self_eq hrel) hα with hT

  have hconst : ∀ x : ℚ, algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))
      (algebraMap ℚ (AlgebraicClosure ℚ) x) ∈ fieldOver M ⊥ := fun x =>
    Subfield.subset_closure (Or.inl ⟨⟨algebraMap ℚ (AlgebraicClosure ℚ) x, IntermediateField.algebraMap_mem ⊥ x⟩, rfl⟩)
  have hle : fieldOver M (IntermediateField.adjoin ℚ {α}) ≤ T := by
    refine Subfield.closure_le.mpr ?_
    rintro y (⟨c, rfl⟩ | hy)
    ·
      have hc : (c : AlgebraicClosure ℚ) ∈ IntermediateField.adjoin ℚ {α} := c.2
      show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ) ∈ T
      refine IntermediateField.adjoin_induction ℚ
        (p := fun x _ => algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) x ∈ T) ?_ ?_ ?_ ?_ ?_ hc
      · intro x hx
        rw [Set.mem_singleton_iff.mp hx]
        exact mem_quadraticFieldOver_iff.mpr ⟨0, zero_mem _, 1, one_mem _, by simp⟩
      · intro x
        exact mem_quadraticFieldOver_iff.mpr ⟨_, hconst x, 0, zero_mem _, by simp⟩
      · intro x y _ _ hx hy
        rw [map_add]
        exact add_mem hx hy
      · intro x _ hx
        rw [map_inv₀]
        exact inv_mem hx
      · intro x y _ _ hx hy
        rw [map_mul]
        exact mul_mem hx hy
    ·
      exact mem_quadraticFieldOver_iff.mpr ⟨y, Subfield.subset_closure (Or.inr hy), 0, zero_mem _, by simp⟩
  exact mem_quadraticFieldOver_iff.mp (hle hg)

end NormalForm

section World

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P)

open scoped Pointwise in

private theorem smul_mem_of_mem_decompositionSubgroup {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ A.decompositionSubgroup ℚ) {z : AlgebraicClosure ℚ} (hz : z ∈ A) : σ z ∈ A := by
  have h1 : σ • z ∈ σ • A := ValuationSubring.smul_mem_pointwise_smul σ z A hz
  rwa [MulAction.mem_stabilizer_iff.mp hσ, AlgEquiv.smul_def] at h1

include R in

private theorem frobenius_apply_ne {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} {d : ℕ} (hd : Odd d)
    (hσ : A.IsFrobeniusAt σ (q ^ d)) {β : AlgebraicClosure ℚ} (hβA : β ∈ A)
    (hβ2 : red ⟨β, hβA⟩ ^ (q ^ 2) = red ⟨β, hβA⟩) (hne : red ⟨β, hβA⟩ ^ q ≠ red ⟨β, hβA⟩) : σ β ≠ β := by
  have hmem : σ β ∈ A := smul_mem_of_mem_decompositionSubgroup hσ.mem_decompositionSubgroup hβA
  have hres : IsLocalRing.residue A ⟨σ β, hmem⟩ = IsLocalRing.residue A ⟨β, hβA⟩ ^ (q ^ d) :=
    hσ.smul_residue_eq (IsLocalRing.residue A ⟨β, hβA⟩)
  have hred : red ⟨σ β, hmem⟩ = red ⟨β, hβA⟩ ^ q := by
    rw [← R.redBar_residue, ← R.redBar_residue, hres, map_pow, R.redBar_residue, pow_pow_eq_pow_of_odd hβ2 hd]
  intro h
  apply hne
  rw [← hred]
  exact congrArg red (Subtype.ext h)

include R in

private theorem frobenius_apply_eq_sub {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} {d : ℕ} (hd : Odd d)
    (hσ : A.IsFrobeniusAt σ (q ^ d)) {β : AlgebraicClosure ℚ} (hβA : β ∈ A) {s p : ℤ}
    (hrel : β * β = (s : AlgebraicClosure ℚ) * β - (p : AlgebraicClosure ℚ))
    (hβ2 : red ⟨β, hβA⟩ ^ (q ^ 2) = red ⟨β, hβA⟩) (hne : red ⟨β, hβA⟩ ^ q ≠ red ⟨β, hβA⟩) :
    σ β = (s : AlgebraicClosure ℚ) - β := by
  have hmem : σ β ∈ A := smul_mem_of_mem_decompositionSubgroup hσ.mem_decompositionSubgroup hβA

  have hres : IsLocalRing.residue A ⟨σ β, hmem⟩ = IsLocalRing.residue A ⟨β, hβA⟩ ^ (q ^ d) :=
    hσ.smul_residue_eq (IsLocalRing.residue A ⟨β, hβA⟩)
  have hred : red ⟨σ β, hmem⟩ = red ⟨β, hβA⟩ ^ q := by
    rw [← R.redBar_residue, ← R.redBar_residue, hres, map_pow, R.redBar_residue, pow_pow_eq_pow_of_odd hβ2 hd]
  have hneq : σ β ≠ β := by
    intro h
    apply hne
    rw [← hred]
    exact congrArg red (Subtype.ext h)

  have hσrel : σ β * σ β = (s : AlgebraicClosure ℚ) * σ β - (p : AlgebraicClosure ℚ) := by
    have := congrArg σ hrel
    simpa using this
  have hfactor : (σ β - β) * (σ β + β - (s : AlgebraicClosure ℚ)) = 0 := by
    linear_combination hσrel - hrel
  rcases mul_eq_zero.mp hfactor with h | h
  · exact absurd (sub_eq_zero.mp h) hneq
  · linear_combination h

end World

section Helpers

private theorem map_sub_eq_of_map_eq_zero {S T : Type*} [Ring S] [Ring T] (f : S →+* T) {x c : S} (hc : f c = 0) :
    f (x - c) = f x := by
  rw [map_sub, hc, sub_zero]

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

private theorem hasValue_add {K₁ F₁ : Type*} [Field K₁] [Field F₁] [Algebra K₁ F₁] {v : Place K₁ F₁} {r r' : F₁}
    {b b' : K₁} (h : v.HasValue r b) (h' : v.HasValue r' b') : v.HasValue (r + r') (b + b') := by
  refine ⟨add_mem h.mem h'.mem, ?_⟩
  have hsum : (⟨r + r', add_mem h.mem h'.mem⟩ : v.toValuationSubring) = ⟨r, h.mem⟩ + ⟨r', h'.mem⟩ := rfl
  rw [hsum, map_add, h.residue_eq, h'.residue_eq, map_add]

private theorem hasValue_of_eq {K₁ F₁ : Type*} [Field K₁] [Field F₁] [Algebra K₁ F₁] {v : Place K₁ F₁} {r r' : F₁}
    {b b' : K₁} (h : v.HasValue r b) (hr : r' = r) (hb : b' = b) : v.HasValue r' b' := by
  rw [hr, hb]
  exact h

private theorem exists_hasValue_of_isRational {K₁ F₁ : Type*} [Field K₁] [Field F₁] [Algebra K₁ F₁] {v : Place K₁ F₁}
    (hv : v.IsRational) {r : F₁} (hr : r ∈ v.toValuationSubring) : ∃ b : K₁, v.HasValue r b := by
  obtain ⟨b, hb⟩ := hv (IsLocalRing.residue v.toValuationSubring ⟨r, hr⟩)
  exact ⟨b, hr, hb.symm⟩

private theorem ne_zero_of_hasValue_of_ord_eq_zero {K₁ F₁ : Type*} [Field K₁] [Field F₁] [Algebra K₁ F₁]
    {v : Place K₁ F₁} {r : F₁} {b : K₁} (hr : r ≠ 0) (h : v.HasValue r b) (h0 : v.ord r = 0) : b ≠ 0 := by
  rintro rfl
  exact (ord_pos_of_hasValue_zero v hr h).ne' h0

private theorem ne_zero_of_ord_pos {K₁ F₁ : Type*} [Field K₁] [Field F₁] [Algebra K₁ F₁] {v : Place K₁ F₁} {r : F₁}
    (h : 0 < v.ord r) : r ≠ 0 := by
  rintro rfl
  rw [Place.ord_zero] at h
  exact lt_irrefl _ h

private theorem add_mul_ne_zero {k₁ : Type*} [Field k₁] {a b c : k₁} (h₀ : b = 0 → a ≠ 0) (h₁ : b ≠ 0 → c ≠ -a / b) :
    a + c * b ≠ 0 := by
  intro h
  by_cases hb : b = 0
  · exact h₀ hb (by rwa [hb, mul_zero, add_zero] at h)
  · apply h₁ hb
    rw [eq_div_iff hb]
    linear_combination h

private theorem map_add_mul {S T : Type*} [Ring S] [Ring T] (f : S →+* T) (x c y : S) :
    f (x + c * y) = f x + f c * f y := by
  rw [map_add, map_mul]

private theorem hasValue_smul {K₁ F₁ : Type*} [Field K₁] [Field F₁] [Algebra K₁ F₁] (τ : SemilinearAut K₁ F₁)
    {v : Place K₁ F₁} {r : F₁} {b : K₁} (h : v.HasValue r b) :
    (τ • v).HasValue (τ • r) (SemilinearAut.baseAut τ b) := by
  obtain ⟨hm, hres⟩ := h
  have hmem : τ • r ∈ (τ • v).toValuationSubring := by
    rw [SemilinearAut.smul_toValuationSubring]
    exact ValuationSubring.smul_mem_pointwise_smul τ r _ hm
  refine ⟨hmem, ?_⟩
  have key := congrArg (SemilinearAut.smulResidueRingEquiv τ v) hres
  rw [SemilinearAut.smulResidueRingEquiv_algebraMap] at key
  rw [← key]
  show _ = IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _)
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  rfl

private theorem hasValue_inv_zero {K₁ F₁ : Type*} [Field K₁] [Field F₁] [Algebra K₁ F₁] (v : Place K₁ F₁) {r : F₁}
    (hr : r ∉ v.toValuationSubring) : v.HasValue r⁻¹ 0 := by
  have hnon : r⁻¹ ∈ v.toValuationSubring.nonunits :=
    (ValuationSubring.mem_nonunits_iff_or _).mpr (Or.inr (by rwa [inv_inv]))
  obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hnon
  refine ⟨hmem, ?_⟩
  rw [map_zero]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr hmax

private theorem map_inv_smul_map_smul {G H X : Type*} [Group G] [Group H] [MulAction H X] (f : G →* H) (σ : G)
    (x : X) : f σ⁻¹ • f σ • x = x := by
  rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]

private theorem exists_eq_add_mul_of_mem_adjoin {α' : AlgebraicClosure ℚ} {s p : ℤ}
    (hrel : α' * α' = (s : AlgebraicClosure ℚ) * α' - (p : AlgebraicClosure ℚ)) {x : AlgebraicClosure ℚ}
    (hx : x ∈ IntermediateField.adjoin ℚ {α'}) :
    ∃ u v : ℚ, x = algebraMap ℚ (AlgebraicClosure ℚ) u + algebraMap ℚ (AlgebraicClosure ℚ) v * α' := by
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) α'),
    Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hx
  obtain ⟨f, rfl⟩ := hx
  set m : Polynomial ℚ := Polynomial.X ^ 2 - Polynomial.C (s : ℚ) * Polynomial.X + Polynomial.C (p : ℚ) with hm_def
  have hm : m.Monic := by
    rw [hm_def]
    monicity!
  have hroot : Polynomial.aeval α' m = 0 := by
    rw [hm_def]
    simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, map_intCast]
    linear_combination hrel
  have hm2 : m.natDegree = 2 := by
    rw [hm_def]
    compute_degree!
  have hm1 : m ≠ 1 := by
    intro h
    rw [h, Polynomial.natDegree_one] at hm2
    omega
  have hdeg : (f %ₘ m).natDegree ≤ 1 := by
    have h := Polynomial.natDegree_modByMonic_lt f hm hm1
    rw [hm2] at h
    exact Nat.lt_succ_iff.mp h
  refine ⟨(f %ₘ m).coeff 0, (f %ₘ m).coeff 1, ?_⟩
  rw [← Polynomial.aeval_modByMonic_eq_self_of_root hroot]
  conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hdeg]
  simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
  ring

private theorem apply_mem_adjoin {α' : AlgebraicClosure ℚ} {s : ℤ} {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσα : σ α' = (s : AlgebraicClosure ℚ) - α') {x : AlgebraicClosure ℚ} (hx : x ∈ IntermediateField.adjoin ℚ {α'}) :
    σ x ∈ IntermediateField.adjoin ℚ {α'} := by
  have hle : (IntermediateField.adjoin ℚ {α'}).map (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) ≤
      IntermediateField.adjoin ℚ {α'} := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    refine IntermediateField.adjoin_le_iff.mpr ?_
    simpa only [Set.singleton_subset_iff, SetLike.mem_coe, AlgEquiv.coe_algHom, hσα] using
      sub_mem (intCast_mem (IntermediateField.adjoin ℚ {α'}) s) (IntermediateField.mem_adjoin_simple_self ℚ α')
  exact hle ⟨x, hx, rfl⟩

private theorem hasValue_natCast {K₁ F₁ : Type*} [Field K₁] [Field F₁] [Algebra K₁ F₁] (v : Place K₁ F₁) (n : ℕ) :
    v.HasValue (n : F₁) (n : K₁) :=
  hasValue_of_eq (Place.hasValue_algebraMap v (n : K₁)) (map_natCast (algebraMap K₁ F₁) n).symm rfl

private theorem eq_of_hasValue {K₁ F₁ : Type*} [Field K₁] [Field F₁] [Algebra K₁ F₁] {v : Place K₁ F₁} {r : F₁}
    {b b' : K₁} (h : v.HasValue r b) (h' : v.HasValue r b') : b = b' :=
  v.algebraMap_residueField_injective (h.residue_eq.symm.trans h'.residue_eq)

private theorem hasValue_evalAt {K₁ F₁ : Type*} [Field K₁] [Field F₁] [Algebra K₁ F₁] {v : Place K₁ F₁}
    (hv : v.IsRational) {r : F₁} (hr : r ∈ v.toValuationSubring) : v.HasValue r (v.evalAt r) :=
  ⟨hr, (v.algebraMap_evalAt hv hr).symm⟩

private theorem evalAt_eq_of_hasValue {K₁ F₁ : Type*} [Field K₁] [Field F₁] [Algebra K₁ F₁] {v : Place K₁ F₁}
    (hv : v.IsRational) {r : F₁} {b : K₁} (h : v.HasValue r b) : v.evalAt r = b :=
  eq_of_hasValue (hasValue_evalAt hv h.mem) h

private theorem map_mul_of_eq {S T : Type*} [NonAssocSemiring S] [NonAssocSemiring T] (f : S →+* T) {z x y : S}
    (hz : z = x * y) : f z = f x * f y := by
  rw [hz, map_mul]

private theorem map_quadratic_of_eq {S T : Type*} [NonAssocSemiring S] [NonAssocSemiring T] (f : S →+* T) {z j : S}
    (n₁ n₂ : ℕ) (hz : z = j * j + n₁ * j + n₂) : f z = f j * f j + n₁ * f j + n₂ := by
  rw [hz]
  simp only [map_add, map_mul, map_natCast]

end Helpers

section Reduction

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P)

private theorem jIntegralClosure_bot_le (M : ℕ) [NeZero M] (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) : jIntegralClosure M A ⊥ ≤ jIntegralClosure M A K := by
  rintro x ⟨hxF, hxI⟩
  have hbot : (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)) ≤ K := bot_le
  have hcoeff : coeffSubring A ⊥ ≤ coeffSubring A K := fun a ha => ⟨ha.1, hbot ha.2⟩
  have hjRing : jRing A ⊥ ≤ jRing A K := by
    refine Subring.closure_mono (Set.union_subset_union_left _ ?_)
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨a, hcoeff a.2⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · refine Subfield.closure_mono (Set.union_subset_union_left _ ?_) hxF
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨a, hbot a.2⟩, rfl⟩
  · exact hxI.map_of_comp_eq (Subring.inclusion hjRing) (RingHom.id _) (RingHom.ext fun _ => rfl)

set_option synthInstance.maxHeartbeats 1600000 in

private theorem forall_hasValue_iff_bot (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hdict : ∀ (t : ↥(modularFunctionFieldBar (N * q)))
        (_ : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K),
        ∃ a : A, W.HasValue t (a : AlgebraicClosure ℚ) ∧
          ((∃ h₁ : t ∈ R.R₁.integers, w.HasValue (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k)) ↔
            a ∈ IsLocalRing.maximalIdeal A)) :
    ∀ (t : ↥(modularFunctionFieldBar (N * q)))
        (_ : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A ⊥),
        ∃ a : A, W.HasValue t (a : AlgebraicClosure ℚ) ∧
          ((∃ h₁ : t ∈ R.R₁.integers, w.HasValue (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k)) ↔
            a ∈ IsLocalRing.maximalIdeal A) :=
  fun t ht => hdict t (jIntegralClosure_bot_le (N * q) A K ht)

end Reduction

section Assembly

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)

omit [IsAlgClosed k] [DecidableEq k] in
include R in

private theorem liesOverPrime : A.LiesOverPrime q := by
  show ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits
  have hq : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    apply R.redBar.injective
    rw [R.redBar_residue, map_natCast, map_zero, CharP.cast_eq_zero]
  simpa using A.coe_mem_nonunits_iff.mpr hq

include hqN in

private theorem frobC_smul_frobC_smul_reduceFst (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hw₂ : P.reduceFst W ∈ ssPlaces q N k) :
    arithFrobC q k N • (arithFrobC q k N • P.reduceFst W) = P.reduceFst W := by
  rw [ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr (arithFrobC q k N • P.reduceFst W),
    ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr (P.reduceFst W)]
  exact PlaceSpecialization.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces hqN P (P.reduceFst W)
    hw₂

omit [Fact q.Prime] [DecidableEq k] in
include hqN in

private theorem isRational_of_place (v : Place k (modularFunctionFieldC k N)) : v.IsRational := by
  have hN : (N : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k q N]
    exact hqN
  obtain ⟨inst, htower, -, hfin, -⟩ :=
    ModularCurve.exists_algebra_ratFunc_modularFunctionFieldC_finite_isSeparable k N hN
  letI := inst
  haveI := htower
  haveI := hfin
  exact AlgebraicCurve.Place.isRational_of_isAlgClosed v

private theorem ord_restrictAlong_pos (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (f : ↥(modularFunctionFieldBar N)) (h : 0 < W.ord (heckeAlphaBar (AlgebraicClosure ℚ) N q f)) :
    0 < (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord f := by
  rw [Place.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα] at h
  refine not_le.mp fun hle => ?_
  have he : (0 : ℤ) ≤ (Place.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) W : ℤ) :=
    Nat.cast_nonneg _
  nlinarith

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
include hqN in

private theorem reduceFst_mem_ssPlaces (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hdict : ∀ (t : ↥(modularFunctionFieldBar (N * q)))
        (_ : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A ⊥),
        ∃ a : A, W.HasValue t (a : AlgebraicClosure ℚ) ∧
          ((∃ h₁ : t ∈ R.R₁.integers, w.HasValue (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k)) ↔
            a ∈ IsLocalRing.maximalIdeal A)) :
    P.reduceFst W ∈ ssPlaces q N k := by

  have hjcoe : ((ProlongationTuple.jFun N q : ↥(modularFunctionFieldBar (N * q))) :
      LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := coeffEmb_jq_eq
  have hjF : ((ProlongationTuple.jFun N q : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      fieldOver (N * q) ⊥ := by
    rw [hjcoe]
    exact Subfield.subset_closure (Or.inr (by simp))
  have hjR : ((ProlongationTuple.jFun N q : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      jRing A ⊥ := by
    rw [hjcoe]
    exact Subring.subset_closure (Or.inr rfl)
  obtain ⟨x, hjx, -⟩ :=
    hdict (ProlongationTuple.jFun N q) ⟨hjF, isIntegral_algebraMap (x := (⟨_, hjR⟩ : jRing A ⊥))⟩
  have hrat : (P.reduceFst W).IsRational := isRational_of_place hqN (P.reduceFst W)

  have hjx0 : 0 < W.ord (ProlongationTuple.jFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (x : AlgebraicClosure ℚ)) := by
    obtain ⟨h₁, -, -, -, hres₁, -, -, -⟩ := R.residue_jFun_sub_jQFun_sub hqN x
    refine ord_pos_of_hasValue_zero W (fun h0 => ?_)
      (hasValue_of_eq (hasValue_sub_algebraMap W hjx (x : AlgebraicClosure ℚ)) rfl (sub_self _).symm)
    apply jGeomGen_sub_algebraMap_ne_zero (K := k) (N := N) (red x)
    rw [← hres₁, show (⟨_, h₁⟩ : R.R₁.integers) = 0 from Subtype.ext h0, map_zero]
  have haff : IsAffineGeomPlace k N (P.reduceFst W) := by
    by_contra hna
    exact absurd hjx0 (not_lt.mpr (ProlongationTuple.isCuspidal_of_not_isAffineGeomPlace_reduceFst P W hna x))

  have hjv : (P.reduceFst W).HasValue (jGeomGen k N) (red x) := by
    have hαj : heckeAlphaBar (AlgebraicClosure ℚ) N q
        ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full N (jq_mem N))⟩ = ProlongationTuple.jFun N q :=
      Subtype.ext (coe_heckeAlphaBar N q _)
    have hred := P.d0_j _ x (ord_restrictAlong_pos (hα := hα) W _ (by rw [map_sub, AlgHom.commutes, hαj]; exact hjx0))
    exact hasValue_of_eq (hasValue_add (hasValue_zero_of_ord_pos _ hred) (Place.hasValue_algebraMap _ (red x)))
      (sub_add_cancel _ _).symm (zero_add _).symm

  obtain ⟨hwrat, hwaff, hwss⟩ := (mem_ssPlaces_iff q N k).mp hw
  set β : k := w.evalAt (jGeomGen k N)
  have hβw : w.HasValue (jGeomGen k N) β := hasValue_evalAt hwrat hwaff.1
  have hβ2 : β ^ (q ^ 2) = β := ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet q hwss
  have hβqq : (β ^ q) ^ q = β := by
    rw [← pow_mul, ← sq, hβ2]
  obtain ⟨n₀, hn₀⟩ := exists_natCast_eq (x := β + β ^ q) (by rw [add_pow_char _ _ q, hβqq, add_comm])
  obtain ⟨n₂, hn₂⟩ := exists_natCast_eq (x := β * β ^ q) (by rw [mul_pow, hβqq, mul_comm])

  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℕ, (n₁ : k) = -(β + β ^ q) := by
    refine ⟨(q - 1) * n₀, ?_⟩
    rw [Nat.cast_mul, Nat.cast_sub (Fact.out : q.Prime).one_lt.le, Nat.cast_one, CharP.cast_eq_zero k q, hn₀]
    ring

  obtain ⟨h₁, -, -, -, hres₁, -, -, -⟩ := R.residue_jFun_sub_jQFun_sub hqN 0
  have hj₁ : ProlongationTuple.jFun N q ∈ R.R₁.integers :=
    (congrArg (· ∈ R.R₁.integers) (show ProlongationTuple.jFun N q = ProlongationTuple.jFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((0 : A) : AlgebraicClosure ℚ)
        by simp)).mpr h₁
  obtain ⟨jR, hjR'⟩ : ∃ jR : R.R₁.integers, (jR : ↥(modularFunctionFieldBar (N * q))) = ProlongationTuple.jFun N q :=
    ⟨⟨_, hj₁⟩, rfl⟩
  have hresj : (R.residue₁ jR : ↥(modularFunctionFieldC k N)) = jGeomGen k N :=
    (congrArg R.residue₁ (Subtype.ext (by rw [hjR']; simp) : jR = ⟨_, h₁⟩)).trans (hres₁.trans (by simp))

  obtain ⟨tR, htR⟩ : ∃ tR : R.R₁.integers, tR = jR * jR + (n₁ : R.R₁.integers) * jR + (n₂ : R.R₁.integers) :=
    ⟨_, rfl⟩
  have ht : (tR : ↥(modularFunctionFieldBar (N * q))) = ProlongationTuple.jFun N q * ProlongationTuple.jFun N q +
      (n₁ : ↥(modularFunctionFieldBar (N * q))) * ProlongationTuple.jFun N q +
      (n₂ : ↥(modularFunctionFieldBar (N * q))) := by
    rw [htR]
    push_cast
    rw [hjR']
  have htRing : ((tR : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ jRing A ⊥ := by
    rw [ht]
    push_cast
    exact add_mem (add_mem (mul_mem hjR hjR) (mul_mem (natCast_mem _ n₁) hjR)) (natCast_mem _ n₂)
  have htF : ((tR : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      fieldOver (N * q) ⊥ := by
    rw [ht]
    push_cast
    exact add_mem (add_mem (mul_mem hjF hjF) (mul_mem (natCast_mem _ n₁) hjF)) (natCast_mem _ n₂)
  obtain ⟨a, hta, hiff⟩ := hdict tR ⟨htF, isIntegral_algebraMap (x := (⟨_, htRing⟩ : jRing A ⊥))⟩
  have hta' : W.HasValue (tR : ↥(modularFunctionFieldBar (N * q)))
      ((x : AlgebraicClosure ℚ) * x + (n₁ : AlgebraicClosure ℚ) * x + (n₂ : AlgebraicClosure ℚ)) :=
    hasValue_of_eq (hasValue_add (hasValue_add (hjx.mul hjx) ((hasValue_natCast W n₁).mul hjx))
      (hasValue_natCast W n₂)) ht rfl
  have hax : (a : AlgebraicClosure ℚ) =
      (x : AlgebraicClosure ℚ) * x + (n₁ : AlgebraicClosure ℚ) * x + (n₂ : AlgebraicClosure ℚ) :=
    eq_of_hasValue hta hta'
  have hrest : (R.residue₁ tR : ↥(modularFunctionFieldC k N)) =
      jGeomGen k N * jGeomGen k N + (n₁ : ↥(modularFunctionFieldC k N)) * jGeomGen k N +
        (n₂ : ↥(modularFunctionFieldC k N)) := by
    have h := map_quadratic_of_eq R.residue₁ n₁ n₂ htR
    rw [hresj] at h
    exact h
  have hvan : ∃ h₁ : (tR : ↥(modularFunctionFieldBar (N * q))) ∈ R.R₁.integers,
      w.HasValue (R.residue₁ ⟨tR, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k) :=
    ⟨tR.2, hasValue_of_eq (hasValue_add (hasValue_add (hβw.mul hβw) ((hasValue_natCast w n₁).mul hβw))
      (hasValue_natCast w n₂)) hrest (by rw [hn₁, hn₂]; ring)⟩

  have hra : red a = 0 := by
    rw [← R.redBar_residue a, (IsLocalRing.residue_eq_zero_iff a).mpr (hiff.mp hvan), map_zero]
  have hroot : (red x - β) * (red x - β ^ q) = 0 := by
    have haA : a = x * x + (n₁ : A) * x + (n₂ : A) := Subtype.ext (by exact_mod_cast hax)
    have h := congrArg red haA
    simp only [map_add, map_mul, map_natCast] at h
    rw [hra, hn₁, hn₂] at h
    linear_combination h.symm
  refine (mem_ssPlaces_iff q N k).mpr ((isSupersingularPlace_iff q N k (P.reduceFst W)).mpr ⟨hrat, haff, ?_⟩)
  rw [evalAt_eq_of_hasValue hrat hjv]
  rcases mul_eq_zero.mp hroot with h | h
  · rw [sub_eq_zero.mp h]
    exact hwss
  · rw [sub_eq_zero.mp h]
    have hfrob := ModularCurve.mem_ssJSet_map_of_isAlgClosed (frobenius k q) β hwss
    rwa [frobenius_def] at hfrob

omit [IsAlgClosed k] [DecidableEq k] in
include R in

private theorem mem_range_redRestrict_of_even (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (d : ℕ) (hd : 0 < d)
    (hcard : Nat.card (Set.range fun a : {a : A // (a : AlgebraicClosure ℚ) ∈ K} => IsLocalRing.residue A a.1) = q ^ d)
    (hσK : ∀ z ∈ K, σ z = z) (hσF : A.IsFrobeniusAt σ (q ^ d)) (hev : Even d) (b : k) (hb : b ^ (q ^ 2) = b) :
    b ∈ Set.range (NodeLocalized.redRestrict red K) := by
  classical
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
include hqN in

private theorem reduceFst_eq_of_dict (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (hO : R.OrderLawFixed) (K'' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K'']
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
    R.exists_mem_jIntegralClosure_ord_residues_pos_and_eq_zero_of_ne hqN K'' hk₀ w₂ w hw₂ hw hne
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
    rw [hsub, map_sub, ProlongationTuple.residue₁_apply (f := ⟨_, hc₁⟩), R.R₁.residue_algebraMap a, hι,
      R.redBar_residue a]
  have hres₂ : (R.residue₂ ⟨f, hf₂⟩ : ↥(modularFunctionFieldC k N)) =
      R.residue₂ ⟨g, hg₂⟩ - algebraMap k ↥(modularFunctionFieldC k N) (red a) := by
    have hsub : (⟨f, hf₂⟩ : R.R₂.integers) = ⟨g, hg₂⟩ - ⟨_, hc₂⟩ := rfl
    rw [hsub, map_sub, ProlongationTuple.residue₂_apply (f := ⟨_, hc₂⟩), R.R₂.residue_algebraMap a, hι,
      R.redBar_residue a]
  have hval₁ : w₂.HasValue (R.residue₁ ⟨f, hf₁⟩ : ↥(modularFunctionFieldC k N)) (-(red a)) := by
    rw [hres₁]
    have h := hasValue_sub_algebraMap w₂ (hasValue_zero_of_ord_pos w₂ hpos₁) (red a)
    rwa [zero_sub] at h
  have hval₂ : (frobOnPlacesGeomLevel k N data hKr w₂).HasValue
      (R.residue₂ ⟨f, hf₂⟩ : ↥(modularFunctionFieldC k N)) (-(red a)) := by
    rw [hres₂]
    have h := hasValue_sub_algebraMap _ (hasValue_zero_of_ord_pos _ hpos₂) (red a)
    rwa [zero_sub] at h
  have hR₁ : R.R₁.residue ⟨f, hf₁⟩ ≠ 0 := fun h0 =>
    hval₁.ne_zero hneg (by rw [ProlongationTuple.residue₁_apply, h0, map_zero])
  have hR₂ : R.R₂.residue ⟨f, hf₂⟩ ≠ 0 := fun h0 =>
    hval₂.ne_zero hneg (by rw [ProlongationTuple.residue₂_apply, h0, map_zero])
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

private theorem card_roots_sq :
    (Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots.toFinset.card = q ^ 2 := by
  have hq2 : 1 < q ^ 2 := Nat.one_lt_pow two_ne_zero (Fact.out : q.Prime).one_lt
  rw [Multiset.toFinset_card_of_nodup
      (Polynomial.nodup_roots (galois_poly_separable q (q ^ 2) (dvd_pow_self q two_ne_zero))),
    ← Polynomial.Splits.natDegree_eq_card_roots (IsAlgClosed.splits _),
    FiniteField.X_pow_card_sub_X_natDegree_eq k hq2]

set_option synthInstance.maxHeartbeats 1600000 in
omit [IsAlgClosed k] [DecidableEq k] in

private theorem ι_algebraMap (x : IsLocalRing.ResidueField A) :
    R.ι (algebraMap (IsLocalRing.ResidueField A) (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) x) =
      algebraMap k ↥(modularFunctionFieldC k N) (R.redBar x) := by
  apply Subtype.ext
  rw [R.ι_coe]
  change coeffMap R.redBar (algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) x) =
    algebraMap k (LaurentSeries k) (R.redBar x)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

set_option synthInstance.maxHeartbeats 1600000 in
omit [IsAlgClosed k] [DecidableEq k] in

private theorem residue₁_algebraMap (a : A) :
    ∃ h : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers,
      (R.residue₁ ⟨_, h⟩ : ↥(modularFunctionFieldC k N)) = algebraMap k ↥(modularFunctionFieldC k N) (red a) :=
  ⟨(R.R₁.algebraMap_mem_iff _).mpr a.2, by
    rw [ProlongationTuple.residue₁_apply, R.R₁.residue_algebraMap a, ι_algebraMap R, R.redBar_residue a]⟩

set_option synthInstance.maxHeartbeats 1600000 in
omit [IsAlgClosed k] [DecidableEq k] in

private theorem residue₂_algebraMap (a : A) :
    ∃ h : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers,
      (R.residue₂ ⟨_, h⟩ : ↥(modularFunctionFieldC k N)) = algebraMap k ↥(modularFunctionFieldC k N) (red a) :=
  ⟨(R.R₂.algebraMap_mem_iff _).mpr a.2, by
    rw [ProlongationTuple.residue₂_apply, R.R₂.residue_algebraMap a, ι_algebraMap R, R.redBar_residue a]⟩

omit [IsAlgClosed k] [DecidableEq k] in

private theorem algebraMap_mem_jIntegralClosure (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (c : coeffSubring A K) :
    algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ) ∈
      jIntegralClosure (N * q) A K := by
  refine ⟨constSeries_mem_fieldOver (N * q) K ⟨c, c.2.2⟩, ?_⟩
  have hmem : algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ) ∈
      jRing A K := Subring.subset_closure (Or.inl ⟨c, rfl⟩)
  exact isIntegral_algebraMap (x := (⟨_, hmem⟩ : jRing A K))

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

private theorem exists_separator_of_bad (K'' : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K''))
    (w w₂ : Place k (modularFunctionFieldC k N)) (g₁ g₂ : ↥(modularFunctionFieldBar (N * q)))
    (hg₁ : (g₁ : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K'')
    (hg₂ : (g₂ : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K'')
    (h₁₁ : g₁ ∈ R.R₁.integers) (h₁₂ : g₁ ∈ R.R₂.integers) (h₂₁ : g₂ ∈ R.R₁.integers) (h₂₂ : g₂ ∈ R.R₂.integers)
    (hw₁ : 0 < w.ord (R.residue₁ ⟨g₁, h₁₁⟩ : ↥(modularFunctionFieldC k N)))
    (hw₂ : 0 < w.ord (R.residue₁ ⟨g₂, h₂₁⟩ : ↥(modularFunctionFieldC k N)))
    {aA aB aC aD bA bB bC bD : k}
    (hA₁ : w₂.HasValue (R.residue₁ ⟨g₁, h₁₁⟩ : ↥(modularFunctionFieldC k N)) aA)
    (hA₂ : w₂.HasValue (R.residue₁ ⟨g₂, h₂₁⟩ : ↥(modularFunctionFieldC k N)) bA)
    (hB₁ : (arithFrobC q k N • w₂).HasValue (R.residue₂ ⟨g₁, h₁₂⟩ : ↥(modularFunctionFieldC k N)) aB)
    (hB₂ : (arithFrobC q k N • w₂).HasValue (R.residue₂ ⟨g₂, h₂₂⟩ : ↥(modularFunctionFieldC k N)) bB)
    (hC₁ : (arithFrobC q k N • w₂).HasValue (R.residue₁ ⟨g₁, h₁₁⟩ : ↥(modularFunctionFieldC k N)) aC)
    (hC₂ : (arithFrobC q k N • w₂).HasValue (R.residue₁ ⟨g₂, h₂₁⟩ : ↥(modularFunctionFieldC k N)) bC)
    (hD₁ : w₂.HasValue (R.residue₂ ⟨g₁, h₁₂⟩ : ↥(modularFunctionFieldC k N)) aD)
    (hD₂ : w₂.HasValue (R.residue₂ ⟨g₂, h₂₂⟩ : ↥(modularFunctionFieldC k N)) bD)
    (bad : Finset k) (hbad : bad.card ≤ 3)
    (hA : bA = 0 → aA ≠ 0) (hA' : bA ≠ 0 → -aA / bA ∈ bad) (hB : bB = 0 → aB ≠ 0) (hB' : bB ≠ 0 → -aB / bB ∈ bad)
    (hC : bC = 0 → aC ≠ 0) (hC' : bC ≠ 0 → -aC / bC ∈ bad) (hD : bD = 0 → aD ≠ 0) (hD' : bD ≠ 0 → -aD / bD ∈ bad) :
    ∃ (g : ↥(modularFunctionFieldBar (N * q)))
      (_ : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K'')
      (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers),
      0 < w.ord (R.residue₁ ⟨g, h₁⟩ : ↥(modularFunctionFieldC k N)) ∧
      w₂.ord (R.residue₁ ⟨g, h₁⟩ : ↥(modularFunctionFieldC k N)) = 0 ∧
      (arithFrobC q k N • w₂).ord (R.residue₂ ⟨g, h₂⟩ : ↥(modularFunctionFieldC k N)) = 0 ∧
      (arithFrobC q k N • w₂).ord (R.residue₁ ⟨g, h₁⟩ : ↥(modularFunctionFieldC k N)) = 0 ∧
      w₂.ord (R.residue₂ ⟨g, h₂⟩ : ↥(modularFunctionFieldC k N)) = 0 ∧
      R.R₁.residue ⟨g, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨g, h₂⟩ ≠ 0 := by

  have h4 : 4 ≤ q ^ 2 := by
    have := Nat.pow_le_pow_left (Fact.out : q.Prime).two_le 2
    simpa using this
  have hlt : bad.card < (Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots.toFinset.card := by
    rw [card_roots_sq]
    omega
  obtain ⟨b, hbT, hbbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hbq : b ^ (q ^ 2) = b := by
    have hq2 : 1 < q ^ 2 := Nat.one_lt_pow two_ne_zero (Fact.out : q.Prime).one_lt
    have := (Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero k hq2)).mp (Multiset.mem_toFinset.mp hbT)
    simpa [sub_eq_zero] using this
  obtain ⟨c, hc⟩ := hk₀ b hbq
  set a : A := ⟨(c : AlgebraicClosure ℚ), c.2.1⟩
  have hred : red a = b := hc

  obtain ⟨hc₁, hres₁c⟩ := residue₁_algebraMap R a
  obtain ⟨hc₂, hres₂c⟩ := residue₂_algebraMap R a
  have hgC : ((g₁ + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) * g₂ :
      ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K'' :=
    add_mem hg₁ (mul_mem (algebraMap_mem_jIntegralClosure K'' c) hg₂)
  have hgi₁ : g₁ + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) * g₂ ∈
      R.R₁.integers := add_mem h₁₁ (mul_mem hc₁ h₂₁)
  have hgi₂ : g₁ + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) * g₂ ∈
      R.R₂.integers := add_mem h₁₂ (mul_mem hc₂ h₂₂)

  have hr₁ : (R.residue₁ ⟨_, hgi₁⟩ : ↥(modularFunctionFieldC k N)) =
      R.residue₁ ⟨g₁, h₁₁⟩ + algebraMap k ↥(modularFunctionFieldC k N) b * R.residue₁ ⟨g₂, h₂₁⟩ := by
    have h := map_add_mul R.residue₁ ⟨g₁, h₁₁⟩ ⟨_, hc₁⟩ ⟨g₂, h₂₁⟩
    rw [hres₁c, hred] at h
    exact h
  have hr₂ : (R.residue₂ ⟨_, hgi₂⟩ : ↥(modularFunctionFieldC k N)) =
      R.residue₂ ⟨g₁, h₁₂⟩ + algebraMap k ↥(modularFunctionFieldC k N) b * R.residue₂ ⟨g₂, h₂₂⟩ := by
    have h := map_add_mul R.residue₂ ⟨g₁, h₁₂⟩ ⟨_, hc₂⟩ ⟨g₂, h₂₂⟩
    rw [hres₂c, hred] at h
    exact h

  have hvA : w₂.HasValue (R.residue₁ ⟨_, hgi₁⟩ : ↥(modularFunctionFieldC k N)) (aA + b * bA) :=
    hasValue_of_eq (hasValue_add hA₁ ((Place.hasValue_algebraMap w₂ b).mul hA₂)) hr₁ rfl
  have hvB : (arithFrobC q k N • w₂).HasValue (R.residue₂ ⟨_, hgi₂⟩ : ↥(modularFunctionFieldC k N)) (aB + b * bB) :=
    hasValue_of_eq (hasValue_add hB₁ ((Place.hasValue_algebraMap _ b).mul hB₂)) hr₂ rfl
  have hvC : (arithFrobC q k N • w₂).HasValue (R.residue₁ ⟨_, hgi₁⟩ : ↥(modularFunctionFieldC k N)) (aC + b * bC) :=
    hasValue_of_eq (hasValue_add hC₁ ((Place.hasValue_algebraMap _ b).mul hC₂)) hr₁ rfl
  have hvD : w₂.HasValue (R.residue₂ ⟨_, hgi₂⟩ : ↥(modularFunctionFieldC k N)) (aD + b * bD) :=
    hasValue_of_eq (hasValue_add hD₁ ((Place.hasValue_algebraMap w₂ b).mul hD₂)) hr₂ rfl
  have hnA : aA + b * bA ≠ 0 := add_mul_ne_zero hA fun hb => fun h => hbbad (h ▸ hA' hb)
  have hnB : aB + b * bB ≠ 0 := add_mul_ne_zero hB fun hb => fun h => hbbad (h ▸ hB' hb)
  have hnC : aC + b * bC ≠ 0 := add_mul_ne_zero hC fun hb => fun h => hbbad (h ▸ hC' hb)
  have hnD : aD + b * bD ≠ 0 := add_mul_ne_zero hD fun hb => fun h => hbbad (h ▸ hD' hb)
  have hvw : w.HasValue (R.residue₁ ⟨_, hgi₁⟩ : ↥(modularFunctionFieldC k N)) 0 :=
    hasValue_of_eq (hasValue_add (hasValue_zero_of_ord_pos w hw₁)
      ((Place.hasValue_algebraMap w b).mul (hasValue_zero_of_ord_pos w hw₂))) hr₁ (by simp)
  refine ⟨_, hgC, hgi₁, hgi₂, ord_pos_of_hasValue_zero w (hvA.ne_zero hnA) hvw, hvA.ord_eq_zero hnA,
    hvB.ord_eq_zero hnB, hvC.ord_eq_zero hnC, hvD.ord_eq_zero hnD, ?_, ?_⟩
  · exact fun h0 => hvA.ne_zero hnA ((congrArg R.ι h0).trans (map_zero R.ι))
  · exact fun h0 => hvB.ne_zero hnB ((congrArg R.ι h0).trans (map_zero R.ι))

include P hqN in

private theorem arithFrobC_smul_arithFrobC_smul (v : Place k (modularFunctionFieldC k N)) (hv : v ∈ ssPlaces q N k) :
    arithFrobC q k N • (arithFrobC q k N • v) = v := by
  rw [ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr (arithFrobC q k N • v),
    ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr v]
  exact PlaceSpecialization.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces hqN P v hv

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
include hqN in

private theorem exists_separator (K'' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K'']
    (hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K''))
    (w w₂ : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k) (hw₂ : w₂ ∈ ssPlaces q N k)
    (hne₁ : w ≠ w₂) (hne₂ : w ≠ arithFrobC q k N • w₂) :
    ∃ (g : ↥(modularFunctionFieldBar (N * q)))
      (_ : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K'')
      (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers),
      0 < w.ord (R.residue₁ ⟨g, h₁⟩ : ↥(modularFunctionFieldC k N)) ∧
      w₂.ord (R.residue₁ ⟨g, h₁⟩ : ↥(modularFunctionFieldC k N)) = 0 ∧
      (arithFrobC q k N • w₂).ord (R.residue₂ ⟨g, h₂⟩ : ↥(modularFunctionFieldC k N)) = 0 ∧
      (arithFrobC q k N • w₂).ord (R.residue₁ ⟨g, h₁⟩ : ↥(modularFunctionFieldC k N)) = 0 ∧
      w₂.ord (R.residue₂ ⟨g, h₂⟩ : ↥(modularFunctionFieldC k N)) = 0 ∧
      R.R₁.residue ⟨g, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨g, h₂⟩ ≠ 0 := by
  have hφw₂ : arithFrobC q k N • w₂ ∈ ssPlaces q N k := ModularCurve.arithFrobC_smul_mem_ssPlaces_univ q N k _ hw₂
  have hφφ : arithFrobC q k N • (arithFrobC q k N • w₂) = w₂ := arithFrobC_smul_arithFrobC_smul (P := P) hqN w₂ hw₂
  have hrat₂ : w₂.IsRational := ((mem_ssPlaces_iff q N k).mp hw₂).1
  have hratφ : (arithFrobC q k N • w₂).IsRational := ((mem_ssPlaces_iff q N k).mp hφw₂).1

  obtain ⟨g₁, hg₁, h₁₁, h₁₂, hp₁₁, hp₁₂, hzA, hzB⟩ :=
    R.exists_mem_jIntegralClosure_ord_residues_pos_and_eq_zero_of_ne hqN K'' hk₀ w w₂ hw hw₂ hne₁
  obtain ⟨g₂, hg₂, h₂₁, h₂₂, hp₂₁, hp₂₂, hzC, hzD'⟩ :=
    R.exists_mem_jIntegralClosure_ord_residues_pos_and_eq_zero_of_ne hqN K'' hk₀ w _ hw hφw₂ hne₂
  have hzD : w₂.ord (R.residue₂ ⟨g₂, h₂₂⟩ : ↥(modularFunctionFieldC k N)) = 0 :=
    (congrArg (fun u : Place k (modularFunctionFieldC k N) =>
      u.ord (R.residue₂ ⟨g₂, h₂₂⟩ : ↥(modularFunctionFieldC k N))) hφφ).symm.trans hzD'
  have hn₁₁ := ne_zero_of_ord_pos hp₁₁
  have hn₁₂ := ne_zero_of_ord_pos hp₁₂
  have hn₂₁ := ne_zero_of_ord_pos hp₂₁
  have hn₂₂ := ne_zero_of_ord_pos hp₂₂

  have hreg₁ := R.mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure hqN K'' w₂ hw₂ g₁ hg₁
  have hreg₂ := R.mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure hqN K'' w₂ hw₂ g₂ hg₂
  have hreg₁' := R.mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure hqN K'' _ hφw₂ g₁ hg₁
  have hreg₂' := R.mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure hqN K'' _ hφw₂ g₂ hg₂
  obtain ⟨aA, hA₁⟩ := exists_hasValue_of_isRational hrat₂ (hreg₁.2.1 h₁₁)
  obtain ⟨bA, hA₂⟩ := exists_hasValue_of_isRational hrat₂ (hreg₂.2.1 h₂₁)
  obtain ⟨aB, hB₁⟩ := exists_hasValue_of_isRational hratφ (hreg₁.2.2 h₁₂)
  obtain ⟨bB, hB₂⟩ := exists_hasValue_of_isRational hratφ (hreg₂.2.2 h₂₂)
  obtain ⟨aC, hC₁⟩ := exists_hasValue_of_isRational hratφ (hreg₁'.2.1 h₁₁)
  obtain ⟨bC, hC₂⟩ := exists_hasValue_of_isRational hratφ (hreg₂'.2.1 h₂₁)
  obtain ⟨aD, hD₁⟩ := exists_hasValue_of_isRational hrat₂
    ((congrArg (fun u : Place k (modularFunctionFieldC k N) =>
      (R.residue₂ ⟨g₁, h₁₂⟩ : ↥(modularFunctionFieldC k N)) ∈ u.toValuationSubring) hφφ).mp (hreg₁'.2.2 h₁₂))
  obtain ⟨bD, hD₂⟩ := exists_hasValue_of_isRational hrat₂
    ((congrArg (fun u : Place k (modularFunctionFieldC k N) =>
      (R.residue₂ ⟨g₂, h₂₂⟩ : ↥(modularFunctionFieldC k N)) ∈ u.toValuationSubring) hφφ).mp (hreg₂'.2.2 h₂₂))
  by_cases hcase : bA ≠ 0 ∧ bB ≠ 0
  ·
    exact ⟨g₂, hg₂, h₂₁, h₂₂, hp₂₁, hA₂.ord_eq_zero hcase.1, hB₂.ord_eq_zero hcase.2, hzC, hzD,
      fun h0 => hA₂.ne_zero hcase.1 ((congrArg R.ι h0).trans (map_zero R.ι)),
      fun h0 => hB₂.ne_zero hcase.2 ((congrArg R.ι h0).trans (map_zero R.ι))⟩
  ·
    have haA : aA ≠ 0 := ne_zero_of_hasValue_of_ord_eq_zero hn₁₁ hA₁ hzA
    have haB : aB ≠ 0 := ne_zero_of_hasValue_of_ord_eq_zero hn₁₂ hB₁ hzB
    have hbC : bC ≠ 0 := ne_zero_of_hasValue_of_ord_eq_zero hn₂₁ hC₂ hzC
    have hbD : bD ≠ 0 := ne_zero_of_hasValue_of_ord_eq_zero hn₂₂ hD₂ hzD
    rcases not_and_or.mp hcase with hbA | hbB
    · exact exists_separator_of_bad R K'' hk₀ w w₂ g₁ g₂ hg₁ hg₂ h₁₁ h₁₂ h₂₁ h₂₂ hp₁₁ hp₂₁ hA₁ hA₂ hB₁ hB₂ hC₁ hC₂
        hD₁ hD₂ {-aB / bB, -aC / bC, -aD / bD} Finset.card_le_three (fun _ => haA) (fun h => absurd h hbA)
        (fun _ => haB) (fun _ => by simp) (fun h => absurd h hbC) (fun _ => by simp) (fun h => absurd h hbD)
        (fun _ => by simp)
    · exact exists_separator_of_bad R K'' hk₀ w w₂ g₁ g₂ hg₁ hg₂ h₁₁ h₁₂ h₂₁ h₂₂ hp₁₁ hp₂₁ hA₁ hA₂ hB₁ hB₂ hC₁ hC₂
        hD₁ hD₂ {-aA / bA, -aC / bC, -aD / bD} Finset.card_le_three (fun _ => haA) (fun _ => by simp)
        (fun _ => haB) (fun h => absurd h hbB) (fun h => absurd h hbC) (fun _ => by simp) (fun h => absurd h hbD)
        (fun _ => by simp)

omit [IsAlgClosed k] [DecidableEq k] in

private theorem algebraMap_notMem_fieldOver_bot (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσK : ∀ z ∈ (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)), σ z = z) {α' : AlgebraicClosure ℚ} (hσα : σ α' ≠ α') :
    algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) α' ∉ fieldOver (N * q) ⊥ := by
  intro h
  have h₁ := (ModularCurve.arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver (N * q) ⊥ σ hσK
    (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) α') h).1
  have h₂ := SemilinearAut.smul_algebraMap (arithmeticGalois (modularFunctionFieldFull (N * q)) σ) α'
  rw [baseAut_arithmeticGalois] at h₂
  exact hσα ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).injective (h₂.symm.trans h₁))

omit [IsAlgClosed k] [DecidableEq k] in

private theorem exists_eq_add_mul_of_mem_jIntegralClosure_adjoin {α' : AlgebraicClosure ℚ} {s p : ℤ}
    (hrel : α' * α' = (s : AlgebraicClosure ℚ) * α' - (p : AlgebraicClosure ℚ))
    (hα' : algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) α' ∉ fieldOver (N * q) ⊥)
    (g : ↥(modularFunctionFieldBar (N * q)))
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A (IntermediateField.adjoin ℚ {α'})) :
    ∃ g₀ g₁ : ↥(modularFunctionFieldBar (N * q)),
      (g₀ : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (N * q) ⊥ ∧
      (g₁ : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (N * q) ⊥ ∧
      (g : LaurentSeries (AlgebraicClosure ℚ)) =
        g₀ + algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) α' * g₁ := by
  obtain ⟨g₀, hg₀, g₁, hg₁, hdec⟩ := exists_add_mul_eq_of_mem_fieldOver_adjoin (N * q) hrel hα' hg.1
  exact ⟨⟨g₀, fieldOver_le_modularFunctionFieldBar (N * q) ⊥ hg₀⟩,
    ⟨g₁, fieldOver_le_modularFunctionFieldBar (N * q) ⊥ hg₁⟩, hg₀, hg₁, hdec⟩

private theorem valuation_inv_apply_lt_one {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσd : σ ∈ A.decompositionSubgroup ℚ) {x : AlgebraicClosure ℚ} (hx : A.valuation x < 1) :
    A.valuation (σ⁻¹ x) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or] at hx ⊢
  rcases hx with rfl | hx
  · exact Or.inl (map_zero _)
  · refine Or.inr fun h => hx ?_
    have h' := smul_mem_of_mem_decompositionSubgroup hσd h
    rwa [map_inv₀, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply] at h'

private theorem arithmeticGalois_smul_eq_of_dec {α' : AlgebraicClosure ℚ} {s : ℤ}
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσK : ∀ z ∈ (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)), σ z = z)
    (hσα : σ α' = (s : AlgebraicClosure ℚ) - α') (g g₀ g₁ : ↥(modularFunctionFieldBar (N * q)))
    (hg₀ : (g₀ : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (N * q) ⊥)
    (hg₁ : (g₁ : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (N * q) ⊥)
    (hdec : (g : LaurentSeries (AlgebraicClosure ℚ)) =
      g₀ + algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) α' * g₁) :
    arithmeticGalois (modularFunctionFieldFull (N * q)) σ • g =
      g₀ +
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((s : AlgebraicClosure ℚ) - α') * g₁ := by
  have hg_eq : g = g₀ + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) α' * g₁ := Subtype.ext hdec
  have h₀ := (ModularCurve.arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver (N * q) ⊥ σ hσK g₀ hg₀).1
  have h₁ := (ModularCurve.arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver (N * q) ⊥ σ hσK g₁ hg₁).1
  have hc : arithmeticGalois (modularFunctionFieldFull (N * q)) σ •
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) α' =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((s : AlgebraicClosure ℚ) - α') := by
    rw [← hσα]
    exact SemilinearAut.smul_algebraMap (arithmeticGalois (modularFunctionFieldFull (N * q)) σ) α'
  rw [hg_eq, smul_add, smul_mul', h₀, h₁, hc]

private theorem norm_eq_mul_smul {α' : AlgebraicClosure ℚ} {s p : ℤ}
    (hrel : α' * α' = (s : AlgebraicClosure ℚ) * α' - (p : AlgebraicClosure ℚ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσK : ∀ z ∈ (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)), σ z = z)
    (hσα : σ α' = (s : AlgebraicClosure ℚ) - α') (g g₀ g₁ n : ↥(modularFunctionFieldBar (N * q)))
    (hg₀ : (g₀ : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (N * q) ⊥)
    (hg₁ : (g₁ : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (N * q) ⊥)
    (hdec : (g : LaurentSeries (AlgebraicClosure ℚ)) =
      g₀ + algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) α' * g₁)
    (hn : (n : LaurentSeries (AlgebraicClosure ℚ)) =
      (g₀ : LaurentSeries (AlgebraicClosure ℚ)) ^ 2 +
        (s : LaurentSeries (AlgebraicClosure ℚ)) * (g₀ : LaurentSeries (AlgebraicClosure ℚ)) *
          (g₁ : LaurentSeries (AlgebraicClosure ℚ)) +
        (p : LaurentSeries (AlgebraicClosure ℚ)) * (g₁ : LaurentSeries (AlgebraicClosure ℚ)) ^ 2) :
    n = g * (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • g) := by
  have hn' : n = g₀ ^ 2 + (s : ↥(modularFunctionFieldBar (N * q))) * g₀ * g₁ +
      (p : ↥(modularFunctionFieldBar (N * q))) * g₁ ^ 2 := Subtype.ext (by exact_mod_cast hn)
  have hg_eq : g = g₀ + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) α' * g₁ := Subtype.ext hdec
  have hrel' : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) α' *
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) α' =
      (s : ↥(modularFunctionFieldBar (N * q))) *
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) α' -
        (p : ↥(modularFunctionFieldBar (N * q))) := by
    rw [← map_mul, hrel, map_sub, map_mul, map_intCast, map_intCast]
  rw [arithmeticGalois_smul_eq_of_dec σ hσK hσα g g₀ g₁ hg₀ hg₁ hdec, hn', hg_eq, map_sub, map_intCast]
  linear_combination (g₁ ^ 2) * hrel'

private theorem algebraMap_isIntegral_jRing_bot {α' : AlgebraicClosure ℚ} {s p : ℤ}
    (hrel : α' * α' = (s : AlgebraicClosure ℚ) * α' - (p : AlgebraicClosure ℚ))
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσα : σ α' = (s : AlgebraicClosure ℚ) - α')
    (hσd : σ ∈ A.decompositionSubgroup ℚ) (c : coeffSubring A (IntermediateField.adjoin ℚ {α'})) :
    IsIntegral (jRing A ⊥)
      (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ)) := by
  obtain ⟨u, v, huv⟩ := exists_eq_add_mul_of_mem_adjoin hrel c.2.2
  have hσc : σ (c : AlgebraicClosure ℚ) =
      algebraMap ℚ (AlgebraicClosure ℚ) u + algebraMap ℚ (AlgebraicClosure ℚ) v * ((s : AlgebraicClosure ℚ) - α') := by
    rw [huv, map_add, map_mul, hσα, AlgEquiv.commutes, AlgEquiv.commutes]

  have hσcA : σ (c : AlgebraicClosure ℚ) ∈ A := smul_mem_of_mem_decompositionSubgroup hσd c.2.1
  set t₁ : AlgebraicClosure ℚ := (c : AlgebraicClosure ℚ) + σ (c : AlgebraicClosure ℚ) with ht₁
  set t₂ : AlgebraicClosure ℚ := (c : AlgebraicClosure ℚ) * σ (c : AlgebraicClosure ℚ) with ht₂
  have ht₁Q : t₁ = algebraMap ℚ (AlgebraicClosure ℚ) (u + u + v * s) := by
    rw [ht₁, hσc, huv]
    simp only [map_add, map_mul, map_intCast]
    ring
  have ht₂Q : t₂ = algebraMap ℚ (AlgebraicClosure ℚ) (u * u + u * v * s + v * v * p) := by
    rw [ht₂, hσc, huv]
    simp only [map_add, map_mul, map_intCast]
    linear_combination (-(algebraMap ℚ (AlgebraicClosure ℚ) v * algebraMap ℚ (AlgebraicClosure ℚ) v)) * hrel
  have ht₁mem : t₁ ∈ coeffSubring A ⊥ :=
    ⟨add_mem c.2.1 hσcA, by rw [ht₁Q]; exact IntermediateField.algebraMap_mem ⊥ _⟩
  have ht₂mem : t₂ ∈ coeffSubring A ⊥ :=
    ⟨mul_mem c.2.1 hσcA, by rw [ht₂Q]; exact IntermediateField.algebraMap_mem ⊥ _⟩
  have hc₁ : algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) t₁ ∈ jRing A ⊥ :=
    Subring.subset_closure (Or.inl ⟨⟨t₁, ht₁mem⟩, rfl⟩)
  have hc₂ : algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) t₂ ∈ jRing A ⊥ :=
    Subring.subset_closure (Or.inl ⟨⟨t₂, ht₂mem⟩, rfl⟩)

  refine ⟨Polynomial.X ^ 2 - Polynomial.C (⟨_, hc₁⟩ : jRing A ⊥) * Polynomial.X +
    Polynomial.C (⟨_, hc₂⟩ : jRing A ⊥), by monicity!, ?_⟩
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C]
  have hcoe₁ : algebraMap (jRing A ⊥) (LaurentSeries (AlgebraicClosure ℚ)) ⟨_, hc₁⟩ =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) t₁ := rfl
  have hcoe₂ : algebraMap (jRing A ⊥) (LaurentSeries (AlgebraicClosure ℚ)) ⟨_, hc₂⟩ =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) t₂ := rfl
  rw [hcoe₁, hcoe₂]
  have h0 : (c : AlgebraicClosure ℚ) ^ 2 - t₁ * (c : AlgebraicClosure ℚ) + t₂ = 0 := by
    rw [ht₁, ht₂]
    ring
  simpa only [map_add, map_sub, map_pow, map_mul, map_zero] using
    congrArg (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) h0

private theorem isIntegral_jRing_bot_of_adjoin {α' : AlgebraicClosure ℚ} {s p : ℤ}
    (hrel : α' * α' = (s : AlgebraicClosure ℚ) * α' - (p : AlgebraicClosure ℚ))
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσα : σ α' = (s : AlgebraicClosure ℚ) - α')
    (hσd : σ ∈ A.decompositionSubgroup ℚ) {z : LaurentSeries (AlgebraicClosure ℚ)}
    (hz : IsIntegral (jRing A (IntermediateField.adjoin ℚ {α'})) z) : IsIntegral (jRing A ⊥) z := by
  have hle : jRing A (IntermediateField.adjoin ℚ {α'}) ≤
      (integralClosure (jRing A ⊥) (LaurentSeries (AlgebraicClosure ℚ))).toSubring := by
    refine Subring.closure_le.mpr ?_
    rintro x (⟨c, rfl⟩ | rfl)
    · exact algebraMap_isIntegral_jRing_bot hrel hσα hσd c
    · exact isIntegral_algebraMap (x := (⟨_, Subring.subset_closure (Or.inr rfl)⟩ : jRing A ⊥))
  have hz' : IsIntegral (integralClosure (jRing A ⊥) (LaurentSeries (AlgebraicClosure ℚ))) z :=
    hz.map_of_comp_eq (RingHom.codRestrict (jRing A (IntermediateField.adjoin ℚ {α'})).subtype _ fun x => hle x.2)
      (RingHom.id _) (RingHom.ext fun _ => rfl)
  exact isIntegral_trans z hz'

omit [Fact q.Prime] [NeZero N] in

private theorem coe_arithmeticGalois_smul (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (f : ↥(modularFunctionFieldBar (N * q))) :
    ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ • f : ↥(modularFunctionFieldBar (N * q))) :
        LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) (f : LaurentSeries (AlgebraicClosure ℚ)) :=
  rfl

private theorem coeffMap_jqModC (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσK : ∀ z ∈ (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)), σ z = z) :
    coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) (jqModC (AlgebraicClosure ℚ)) =
        jqModC (AlgebraicClosure ℚ) ∧
      coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) (jqNModC (AlgebraicClosure ℚ) (N * q)) =
        jqNModC (AlgebraicClosure ℚ) (N * q) := by
  have hj : jqModC (AlgebraicClosure ℚ) ∈ fieldOver (N * q) ⊥ := Subfield.subset_closure (Or.inr (by simp))
  have hjN : jqNModC (AlgebraicClosure ℚ) (N * q) ∈ fieldOver (N * q) ⊥ := Subfield.subset_closure (Or.inr (by simp))
  constructor
  · exact congrArg Subtype.val (ModularCurve.arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver
      (N * q) ⊥ σ hσK ⟨_, fieldOver_le_modularFunctionFieldBar (N * q) ⊥ hj⟩ hj).1
  · exact congrArg Subtype.val (ModularCurve.arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver
      (N * q) ⊥ σ hσK ⟨_, fieldOver_le_modularFunctionFieldBar (N * q) ⊥ hjN⟩ hjN).1

private theorem coeffMap_mem_jRing_and_fieldOver {α' : AlgebraicClosure ℚ} {s : ℤ}
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσK : ∀ z ∈ (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)), σ z = z)
    (hσα : σ α' = (s : AlgebraicClosure ℚ) - α') (hσd : σ ∈ A.decompositionSubgroup ℚ) :
    (∀ x ∈ jRing A (IntermediateField.adjoin ℚ {α'}),
        coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) x ∈ jRing A (IntermediateField.adjoin ℚ {α'})) ∧
      ∀ x ∈ fieldOver (N * q) (IntermediateField.adjoin ℚ {α'}),
        coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) x ∈
          fieldOver (N * q) (IntermediateField.adjoin ℚ {α'}) := by
  obtain ⟨hj, hjN⟩ := coeffMap_jqModC (N := N) (q := q) σ hσK
  constructor
  · intro x hx
    have hle : jRing A (IntermediateField.adjoin ℚ {α'}) ≤
        (jRing A (IntermediateField.adjoin ℚ {α'})).comap
          (coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) := by
      refine Subring.closure_le.mpr ?_
      rintro y (⟨c, rfl⟩ | rfl)
      · rw [SetLike.mem_coe, Subring.mem_comap]
        show coeffMap _
          (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ)) ∈ _
        rw [coeffMap_algebraMap]
        exact Subring.subset_closure
          (Or.inl ⟨⟨σ c, smul_mem_of_mem_decompositionSubgroup hσd c.2.1, apply_mem_adjoin hσα c.2.2⟩, rfl⟩)
      · rw [SetLike.mem_coe, Subring.mem_comap, hj]
        exact Subring.subset_closure (Or.inr rfl)
    exact Subring.mem_comap.mp (hle hx)
  · intro x hx
    have hle : fieldOver (N * q) (IntermediateField.adjoin ℚ {α'}) ≤
        (fieldOver (N * q) (IntermediateField.adjoin ℚ {α'})).comap
          (coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) := by
      refine Subfield.closure_le.mpr ?_
      rintro y (⟨c, rfl⟩ | rfl | rfl)
      · rw [SetLike.mem_coe, Subfield.mem_comap]
        show coeffMap _
          (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ)) ∈ _
        rw [coeffMap_algebraMap]
        exact Subfield.subset_closure (Or.inl ⟨⟨σ c, apply_mem_adjoin hσα c.2⟩, rfl⟩)
      · rw [SetLike.mem_coe, Subfield.mem_comap, hj]
        exact Subfield.subset_closure (Or.inr (by simp))
      · rw [SetLike.mem_coe, Subfield.mem_comap, hjN]
        exact Subfield.subset_closure (Or.inr (by simp))
    exact Subfield.mem_comap.mp (hle hx)

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
include hqN in

private theorem exists_norm (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    {α' : AlgebraicClosure ℚ} {s p : ℤ} (hrel : α' * α' = (s : AlgebraicClosure ℚ) * α' - (p : AlgebraicClosure ℚ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσK : ∀ z ∈ (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)), σ z = z)
    (hσα : σ α' = (s : AlgebraicClosure ℚ) - α') (hσd : σ ∈ A.decompositionSubgroup ℚ)
    (g g₀ g₁ : ↥(modularFunctionFieldBar (N * q)))
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A (IntermediateField.adjoin ℚ {α'}))
    (hg₀ : (g₀ : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (N * q) ⊥)
    (hg₁ : (g₁ : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (N * q) ⊥)
    (hdec : (g : LaurentSeries (AlgebraicClosure ℚ)) =
      g₀ + algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) α' * g₁)
    (h₁ : g ∈ R.R₁.integers) (hgw : 0 < w.ord (R.residue₁ ⟨g, h₁⟩ : ↥(modularFunctionFieldC k N))) :
    ∃ n : ↥(modularFunctionFieldBar (N * q)),
      (n : LaurentSeries (AlgebraicClosure ℚ)) =
        (g₀ : LaurentSeries (AlgebraicClosure ℚ)) ^ 2 +
          (s : LaurentSeries (AlgebraicClosure ℚ)) * (g₀ : LaurentSeries (AlgebraicClosure ℚ)) *
            (g₁ : LaurentSeries (AlgebraicClosure ℚ)) +
          (p : LaurentSeries (AlgebraicClosure ℚ)) * (g₁ : LaurentSeries (AlgebraicClosure ℚ)) ^ 2 ∧
      (n : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A ⊥ ∧
      ∃ h₁ : n ∈ R.R₁.integers, w.HasValue (R.residue₁ ⟨n, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k) := by
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {α'}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) α').isIntegral
  have hrat : w.IsRational := ((mem_ssPlaces_iff q N k).mp hw).1
  refine ⟨g₀ ^ 2 + (s : ↥(modularFunctionFieldBar (N * q))) * g₀ * g₁ +
    (p : ↥(modularFunctionFieldBar (N * q))) * g₁ ^ 2, ?_, ?_, ?_⟩
  · push_cast
    ring
  ·

    have hn : ((g₀ ^ 2 + (s : ↥(modularFunctionFieldBar (N * q))) * g₀ * g₁ +
        (p : ↥(modularFunctionFieldBar (N * q))) * g₁ ^ 2 : ↥(modularFunctionFieldBar (N * q))) :
          LaurentSeries (AlgebraicClosure ℚ)) =
        (g₀ : LaurentSeries (AlgebraicClosure ℚ)) ^ 2 +
          (s : LaurentSeries (AlgebraicClosure ℚ)) * (g₀ : LaurentSeries (AlgebraicClosure ℚ)) *
            (g₁ : LaurentSeries (AlgebraicClosure ℚ)) +
          (p : LaurentSeries (AlgebraicClosure ℚ)) * (g₁ : LaurentSeries (AlgebraicClosure ℚ)) ^ 2 := by
      push_cast
      ring
    refine ⟨?_, ?_⟩
    · rw [hn]
      exact add_mem (add_mem (pow_mem hg₀ 2) (mul_mem (mul_mem (intCast_mem _ s) hg₀) hg₁))
        (mul_mem (intCast_mem _ p) (pow_mem hg₁ 2))
    · have hnorm := norm_eq_mul_smul hrel σ hσK hσα g g₀ g₁ _ hg₀ hg₁ hdec hn
      rw [hnorm]
      have hσg := (coeffMap_mem_jRing_and_fieldOver (N := N) (q := q) σ hσK hσα hσd).1
      have hτg : IsIntegral (jRing A (IntermediateField.adjoin ℚ {α'}))
          ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ • g : ↥(modularFunctionFieldBar (N * q))) :
            LaurentSeries (AlgebraicClosure ℚ)) := by
        rw [coe_arithmeticGalois_smul]
        exact hg.2.map_of_comp_eq
          (RingHom.codRestrict ((coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)).comp
            (jRing A (IntermediateField.adjoin ℚ {α'})).subtype) _ fun x => hσg x x.2)
          (coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) (RingHom.ext fun _ => rfl)
      exact isIntegral_jRing_bot_of_adjoin hrel hσα hσd (hg.2.mul hτg)
  ·

    have hn : ((g₀ ^ 2 + (s : ↥(modularFunctionFieldBar (N * q))) * g₀ * g₁ +
        (p : ↥(modularFunctionFieldBar (N * q))) * g₁ ^ 2 : ↥(modularFunctionFieldBar (N * q))) :
          LaurentSeries (AlgebraicClosure ℚ)) =
        (g₀ : LaurentSeries (AlgebraicClosure ℚ)) ^ 2 +
          (s : LaurentSeries (AlgebraicClosure ℚ)) * (g₀ : LaurentSeries (AlgebraicClosure ℚ)) *
            (g₁ : LaurentSeries (AlgebraicClosure ℚ)) +
          (p : LaurentSeries (AlgebraicClosure ℚ)) * (g₁ : LaurentSeries (AlgebraicClosure ℚ)) ^ 2 := by
      push_cast
      ring
    have hnorm := norm_eq_mul_smul hrel σ hσK hσα g g₀ g₁ _ hg₀ hg₁ hdec hn
    have hστ := coeffMap_mem_jRing_and_fieldOver (N := N) (q := q) σ hσK hσα hσd
    have hτgC : ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ • g : ↥(modularFunctionFieldBar (N * q))) :
        LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A (IntermediateField.adjoin ℚ {α'}) := by
      refine ⟨?_, ?_⟩
      · rw [coe_arithmeticGalois_smul]
        exact hστ.2 _ hg.1
      · rw [coe_arithmeticGalois_smul]
        exact hg.2.map_of_comp_eq
          (RingHom.codRestrict ((coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)).comp
            (jRing A (IntermediateField.adjoin ℚ {α'})).subtype) _ fun x => hστ.1 x x.2)
          (coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) (RingHom.ext fun _ => rfl)
    have hreg := R.mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure hqN _ w hw _ hτgC
    have hτ₁ : arithmeticGalois (modularFunctionFieldFull (N * q)) σ • g ∈ R.R₁.integers := hreg.1.1
    have hn₁ : g₀ ^ 2 + (s : ↥(modularFunctionFieldBar (N * q))) * g₀ * g₁ +
        (p : ↥(modularFunctionFieldBar (N * q))) * g₁ ^ 2 ∈ R.R₁.integers :=
      (congrArg (· ∈ R.R₁.integers) hnorm).mpr (mul_mem h₁ hτ₁)
    refine ⟨hn₁, ?_⟩
    have hres : (R.residue₁ ⟨_, hn₁⟩ : ↥(modularFunctionFieldC k N)) =
        R.residue₁ ⟨g, h₁⟩ * R.residue₁ ⟨_, hτ₁⟩ := map_mul_of_eq R.residue₁ (Subtype.ext hnorm)
    obtain ⟨c, hc⟩ := exists_hasValue_of_isRational hrat (hreg.2.1 hτ₁)
    exact hasValue_of_eq ((hasValue_zero_of_ord_pos w hgw).mul hc) hres (by simp)

set_option maxHeartbeats 3200000 in
omit [IsAlgClosed k] [DecidableEq k] in

private theorem hasValue_mem_or_of_norm {α' : AlgebraicClosure ℚ} {s p : ℤ}
    (hrel : α' * α' = (s : AlgebraicClosure ℚ) * α' - (p : AlgebraicClosure ℚ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσK : ∀ z ∈ (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)), σ z = z)
    (hσα : σ α' = (s : AlgebraicClosure ℚ) - α') (hσd : σ ∈ A.decompositionSubgroup ℚ)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (g g₀ g₁ n : ↥(modularFunctionFieldBar (N * q)))
    (hg₀ : (g₀ : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (N * q) ⊥)
    (hg₁ : (g₁ : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (N * q) ⊥)
    (hdec : (g : LaurentSeries (AlgebraicClosure ℚ)) =
      g₀ + algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) α' * g₁)
    (hn : (n : LaurentSeries (AlgebraicClosure ℚ)) =
      (g₀ : LaurentSeries (AlgebraicClosure ℚ)) ^ 2 +
        (s : LaurentSeries (AlgebraicClosure ℚ)) * (g₀ : LaurentSeries (AlgebraicClosure ℚ)) *
          (g₁ : LaurentSeries (AlgebraicClosure ℚ)) +
        (p : LaurentSeries (AlgebraicClosure ℚ)) * (g₁ : LaurentSeries (AlgebraicClosure ℚ)) ^ 2)
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) (hval : W.HasValue n (a : AlgebraicClosure ℚ)) :
    (∃ b : A, b ∈ IsLocalRing.maximalIdeal A ∧ W.HasValue g (b : AlgebraicClosure ℚ)) ∨
      ∃ b : A, b ∈ IsLocalRing.maximalIdeal A ∧
        (arithmeticGalois (modularFunctionFieldFull (N * q)) σ⁻¹ • W).HasValue g (b : AlgebraicClosure ℚ) := by
  have hnorm := norm_eq_mul_smul hrel σ hσK hσα g g₀ g₁ n hg₀ hg₁ hdec hn
  have hrat : W.IsRational := ModularCurve.isRational_place_modularFunctionFieldBar (N * q) W

  have htrans : ∀ {x : AlgebraicClosure ℚ},
      W.HasValue (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • g) x →
        (arithmeticGalois (modularFunctionFieldFull (N * q)) σ⁻¹ • W).HasValue g (σ⁻¹ x) := by
    intro x hx
    have h := hasValue_smul (arithmeticGalois (modularFunctionFieldFull (N * q)) σ⁻¹) hx
    rw [map_inv_smul_map_smul (arithmeticGalois (modularFunctionFieldFull (N * q))) σ g, baseAut_arithmeticGalois] at h
    exact h
  by_cases hreg : g ∈ W.toValuationSubring
  · obtain ⟨b₁, hb₁⟩ := exists_hasValue_of_isRational hrat hreg
    by_cases hb₁m : A.valuation b₁ < 1
    ·
      exact Or.inl ⟨⟨b₁, A.mem_of_valuation_le_one b₁ hb₁m.le⟩, (A.valuation_lt_one_iff _).mpr hb₁m, hb₁⟩
    ·
      have hb₁0 : b₁ ≠ 0 := by
        rintro rfl
        exact hb₁m (by simp)
      have hg0 : g ≠ 0 := hb₁.ne_zero hb₁0
      have hσg : W.HasValue (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • g)
          ((a : AlgebraicClosure ℚ) * b₁⁻¹) := by
        exact hasValue_of_eq (hval.mul (hb₁.inv hb₁0))
          ((eq_mul_inv_iff_mul_eq₀ hg0).mpr (hnorm.trans (mul_comm g _)).symm) rfl
      have hx : A.valuation ((a : AlgebraicClosure ℚ) * b₁⁻¹) < 1 := by
        refine not_le.mp fun hx1 => ?_
        have hb1 : 1 ≤ A.valuation b₁ := not_lt.mp hb₁m
        have ha' : A.valuation (a : AlgebraicClosure ℚ) < 1 := (A.valuation_lt_one_iff a).mp ha
        have hcalc : 1 ≤ A.valuation (a : AlgebraicClosure ℚ) := by
          calc (1 : _) ≤ A.valuation ((a : AlgebraicClosure ℚ) * b₁⁻¹) * A.valuation b₁ := one_le_mul hx1 hb1
            _ = A.valuation (a : AlgebraicClosure ℚ) := by rw [← map_mul, inv_mul_cancel_right₀ hb₁0]
        exact absurd hcalc (not_le.mpr ha')
      have hx' := valuation_inv_apply_lt_one hσd hx
      exact Or.inr ⟨⟨_, A.mem_of_valuation_le_one _ hx'.le⟩, (A.valuation_lt_one_iff _).mpr hx', htrans hσg⟩
  ·
    have hg0 : g ≠ 0 := fun h => hreg (by rw [h]; exact zero_mem _)
    have h0 : W.HasValue (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • g) 0 :=
      hasValue_of_eq (hval.mul (hasValue_inv_zero W hreg))
        ((eq_mul_inv_iff_mul_eq₀ hg0).mpr (hnorm.trans (mul_comm g _)).symm) (by simp)
    have h := htrans h0
    rw [map_zero] at h
    exact Or.inr ⟨0, zero_mem _, hasValue_of_eq h rfl (by simp)⟩

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
include hqN in

private theorem ord_pos_or_ord_pos_of_hasValue_mem (hO : R.OrderLawFixed)
    (K'' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K'']
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hv : P.reduceFst V ∈ ssPlaces q N k)
    (t : ↥(modularFunctionFieldBar (N * q)))
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K'')
    (h₁ : t ∈ R.R₁.integers) (h₂ : t ∈ R.R₂.integers) (hr₁ : R.R₁.residue ⟨t, h₁⟩ ≠ 0) (hr₂ : R.R₂.residue ⟨t, h₂⟩ ≠ 0)
    (b : A) (hb : b ∈ IsLocalRing.maximalIdeal A) (hval : V.HasValue t (b : AlgebraicClosure ℚ)) :
    0 < (P.reduceFst V).ord (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) ∨
      0 < (arithFrobC q k N • P.reduceFst V).ord (R.residue₂ ⟨t, h₂⟩ : ↥(modularFunctionFieldC k N)) := by
  classical
  haveI hPD : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  have hb0 : IsLocalRing.residue A b = 0 := (IsLocalRing.residue_eq_zero_iff b).mpr hb

  have hc₁ : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (b : AlgebraicClosure ℚ) ∈
      R.R₁.integers := (R.R₁.algebraMap_mem_iff _).mpr b.2
  have hc₂ : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (b : AlgebraicClosure ℚ) ∈
      R.R₂.integers := (R.R₂.algebraMap_mem_iff _).mpr b.2
  have hc₁0 : R.R₁.residue ⟨_, hc₁⟩ = 0 := (R.R₁.residue_algebraMap b).trans (by rw [hb0, map_zero])
  have hc₂0 : R.R₂.residue ⟨_, hc₂⟩ = 0 := (R.R₂.residue_algebraMap b).trans (by rw [hb0, map_zero])
  have hf₁ : t - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (b : AlgebraicClosure ℚ) ∈
      R.R₁.integers := sub_mem h₁ hc₁
  have hf₂ : t - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (b : AlgebraicClosure ℚ) ∈
      R.R₂.integers := sub_mem h₂ hc₂
  have hres₁ : R.R₁.residue ⟨_, hf₁⟩ = R.R₁.residue ⟨t, h₁⟩ :=
    map_sub_eq_of_map_eq_zero R.R₁.residue (x := ⟨t, h₁⟩) hc₁0
  have hres₂ : R.R₂.residue ⟨_, hf₂⟩ = R.R₂.residue ⟨t, h₂⟩ :=
    map_sub_eq_of_map_eq_zero R.R₂.residue (x := ⟨t, h₂⟩) hc₂0
  have hR₁ : R.R₁.residue ⟨_, hf₁⟩ ≠ 0 := fun h0 => hr₁ (hres₁.symm.trans h0)
  have hR₂ : R.R₂.residue ⟨_, hf₂⟩ ≠ 0 := fun h0 => hr₂ (hres₂.symm.trans h0)
  have hf0 : t - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (b : AlgebraicClosure ℚ) ≠ 0 :=
    fun h => hR₁ (by rw [show (⟨_, hf₁⟩ : R.R₁.integers) = 0 from Subtype.ext h, map_zero])

  obtain ⟨D, hD, -⟩ := hPD.exists_divisor _ hf0
  have hfix :=
    PlaceSpecialization.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces hqN P (P.reduceFst V) hv
  have haff : IsAffineGeomPlace k N (P.reduceFst V) := ((mem_ssPlaces_iff q N k).mp hv).2.1
  have hlaw := hO _ hf₁ hf₂ hR₁ hR₂ D hD (P.reduceFst V) hfix haff
  have ha : (P.reduceFst V).ord (R.residue₁ ⟨_, hf₁⟩ : ↥(modularFunctionFieldC k N)) =
      (P.reduceFst V).ord (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) :=
    congrArg (fun r => (P.reduceFst V).ord (R.ι r)) hres₁
  have hb₂ : (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V)).ord
        (R.residue₂ ⟨_, hf₂⟩ : ↥(modularFunctionFieldC k N)) =
      (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V)).ord (R.residue₂ ⟨t, h₂⟩ : ↥(modularFunctionFieldC k N)) :=
    congrArg (fun r => (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V)).ord (R.ι r)) hres₂
  have hφ : (arithFrobC q k N • P.reduceFst V).ord (R.residue₂ ⟨t, h₂⟩ : ↥(modularFunctionFieldC k N)) =
      (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V)).ord (R.residue₂ ⟨t, h₂⟩ : ↥(modularFunctionFieldC k N)) :=
    congrArg (fun u : Place k (modularFunctionFieldC k N) => u.ord (R.residue₂ ⟨t, h₂⟩ : ↥(modularFunctionFieldC k N)))
      (ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr (P.reduceFst V))

  have hV : 1 ≤ D V := by
    have h := hasValue_sub_algebraMap V hval (b : AlgebraicClosure ℚ)
    rw [sub_self] at h
    have hpos := ord_pos_of_hasValue_zero V hf0 h
    rw [hD]
    omega
  have hnonneg : ∀ V', P.reduceFst V' = P.reduceFst V → 0 ≤ D V' := fun V' hV' => by
    have htV' : t ∈ V'.toValuationSubring :=
      (R.mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure hqN K'' (P.reduceFst V) hv t ht).1.2.2 V' hV'
    rw [hD]
    exact V'.ord_nonneg_of_mem (sub_mem htV' (Place.hasValue_algebraMap (v := V') (b : AlgebraicClosure ℚ)).mem)
  have hshape : Finsupp.mapDomain P.reduceFst D (P.reduceFst V) =
      D.support.sum fun V' => Finsupp.single (P.reduceFst V') (D V') (P.reduceFst V) := by
    rw [Finsupp.mapDomain, Finsupp.sum_apply]
    rfl
  have hVs : V ∈ D.support := by
    rw [Finsupp.mem_support_iff]
    omega
  have hterm : ∀ V' ∈ D.support, (0 : ℤ) ≤ Finsupp.single (P.reduceFst V') (D V') (P.reduceFst V) := fun V' _ => by
    rw [Finsupp.single_apply]
    split_ifs with hV'
    · exact hnonneg V' hV'
    · exact le_rfl
  have hsum : Finsupp.single (P.reduceFst V) (D V) (P.reduceFst V) ≤
      D.support.sum fun V' => Finsupp.single (P.reduceFst V') (D V') (P.reduceFst V) := Finset.single_le_sum hterm hVs
  rw [Finsupp.single_apply, if_pos rfl] at hsum
  omega

private theorem map_smul_map_inv_smul {G H X : Type*} [Group G] [Group H] [MulAction H X] (f : G →* H) (σ : G)
    (x : X) : f σ • f σ⁻¹ • x = x := by
  rw [map_inv, smul_inv_smul]

include hqN in

private theorem reduceFst_inv_smul_eq (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {d : ℕ} (hodd : Odd d)
    (hσF : A.IsFrobeniusAt σ (q ^ d)) (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hw₂ : P.reduceFst W ∈ ssPlaces q N k) :
    P.reduceFst (arithmeticGalois (modularFunctionFieldFull (N * q)) σ⁻¹ • W) = arithFrobC q k N • P.reduceFst W := by
  have h := (P.reduceFst_and_reduceSnd_arithmeticGalois_smul_of_isFrobeniusAt_pow σ d hσF
    (arithmeticGalois (modularFunctionFieldFull (N * q)) σ⁻¹ • W)).1
  have hW : P.reduceFst W =
      arithFrobC q k N ^ d • P.reduceFst (arithmeticGalois (modularFunctionFieldFull (N * q)) σ⁻¹ • W) :=
    (congrArg P.reduceFst
      (map_smul_map_inv_smul (arithmeticGalois (modularFunctionFieldFull (N * q))) σ W)).symm.trans h
  have hφφ := frobC_smul_frobC_smul_reduceFst hqN W hw₂
  have hφ2 : arithFrobC q k N ^ 2 • P.reduceFst W = P.reduceFst W := by rw [pow_two, mul_smul, hφφ]
  have hpow : ∀ n : ℕ, (arithFrobC q k N ^ 2) ^ n • P.reduceFst W = P.reduceFst W := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_smul, hφ2, ih]
  obtain ⟨m, rfl⟩ := hodd
  have hd : arithFrobC q k N ^ (2 * m + 1) • (arithFrobC q k N • P.reduceFst W) = P.reduceFst W := by
    rw [← mul_smul, ← pow_succ, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, pow_mul]
    exact hpow (m + 1)
  exact smul_left_cancel _ (hW.symm.trans hd.symm)

end Assembly

set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k) (hO : R.OrderLawFixed)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hdict : ∀ (t : ↥(modularFunctionFieldBar (N * q)))
        (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K),
        ∃ a : A, W.HasValue t (a : AlgebraicClosure ℚ) ∧
          ((∃ h₁ : t ∈ R.R₁.integers, w.HasValue (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k)) ↔
            a ∈ IsLocalRing.maximalIdeal A)) :
    P.reduceFst W = w ∨ P.reduceFst W = arithFrobC q k N • w := by

  have hdict₀ := forall_hasValue_iff_bot R K w W hdict
  have hw₂ : P.reduceFst W ∈ ssPlaces q N k := reduceFst_mem_ssPlaces R hqN w hw W hdict₀

  obtain ⟨d, σ, hd, hcard, hσK, hσF⟩ :=
    ValuationSubring.exists_forall_apply_eq_and_isFrobeniusAt_natCard_of_liesOverPrime q A (liesOverPrime R) ⊥
  rcases Nat.even_or_odd d with hev | hodd
  ·
    exact Or.inl (reduceFst_eq_of_dict R hqN w hw hO ⊥
      (fun b hb => mem_range_redRestrict_of_even R ⊥ σ d hd hcard hσK hσF hev b hb) W hw₂ hdict₀)

  by_contra hne
  rw [not_or] at hne
  obtain ⟨hne₁, hne₂⟩ := hne
  have hφφ := frobC_smul_frobC_smul_reduceFst hqN W hw₂

  obtain ⟨s, p, α', hαA, hrel, hα2, hα1, hfd, hk₀⟩ := exists_quadratic_integer red
  have hσα : σ α' = (s : AlgebraicClosure ℚ) - α' := frobenius_apply_eq_sub R hodd hσF hαA hrel hα2 hα1
  have hαnot := algebraMap_notMem_fieldOver_bot (N := N) (q := q) σ hσK (frobenius_apply_ne R hodd hσF hαA hα2 hα1)

  haveI := hfd
  obtain ⟨g, hgC, h₁, h₂, hgw, hA₁, hB₂, hC₁, hD₂, hr₁, hr₂⟩ :=
    exists_separator R hqN (IntermediateField.adjoin ℚ {α'}) hk₀ w (P.reduceFst W) hw hw₂ (Ne.symm hne₁)
      (fun h => hne₂ (by rw [h, hφφ]))
  obtain ⟨g₀, g₁, hg₀, hg₁, hdec⟩ := exists_eq_add_mul_of_mem_jIntegralClosure_adjoin hrel hαnot g hgC
  obtain ⟨n, hn, hnC, hnw⟩ := exists_norm R hqN w hw hrel σ hσK hσα hσF.mem_decompositionSubgroup g g₀ g₁ hgC hg₀ hg₁
    hdec h₁ hgw

  obtain ⟨a, haval, haiff⟩ := hdict₀ n hnC
  have ha : a ∈ IsLocalRing.maximalIdeal A := haiff.mp hnw

  rcases hasValue_mem_or_of_norm hrel σ hσK hσα hσF.mem_decompositionSubgroup W g g₀ g₁ n hg₀ hg₁ hdec hn a ha haval
      with
    ⟨b, hb, hWb⟩ | ⟨b, hb, hVb⟩
  · rcases ord_pos_or_ord_pos_of_hasValue_mem R hqN hO (IntermediateField.adjoin ℚ {α'}) W hw₂ g hgC h₁ h₂
        hr₁ hr₂ b hb hWb with h | h
    · exact h.ne' hA₁
    · exact h.ne' hB₂
  · have hV := reduceFst_inv_smul_eq hqN σ hodd hσF W hw₂
    have hVss : P.reduceFst (arithmeticGalois (modularFunctionFieldFull (N * q)) σ⁻¹ • W) ∈ ssPlaces q N k := by
      rw [hV]
      exact ModularCurve.arithFrobC_smul_mem_ssPlaces_univ q N k _ hw₂
    rcases ord_pos_or_ord_pos_of_hasValue_mem R hqN hO (IntermediateField.adjoin ℚ {α'}) _ hVss g hgC h₁ h₂
        hr₁ hr₂ b hb hVb with h | h
    · rw [hV] at h
      exact h.ne' hC₁
    · rw [hV, hφφ] at h
      exact h.ne' hD₂

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceFst_eq_or_eq_arithFrobC_smul_of_forall_hasValue_iff
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceFst_eq_or_eq_arithFrobC_smul_of_forall_hasValue_iff (solution)
