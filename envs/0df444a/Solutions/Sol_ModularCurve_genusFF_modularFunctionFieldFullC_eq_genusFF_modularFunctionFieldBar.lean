-- Prove2me | solution 1 for ModularCurve.genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/148cc83b-c294-56da-a587-71bef0189af1

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le
import Theorems.Thm_ModularCurve_genusFormula_le_genusFF_modularFunctionFieldFullC_of_lt_five
import Theorems.Thm_ModularCurve_exists_regularProlongation_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_genus_modularFunctionFieldBar_eq_genusFormula
import Theorems.Thm_ModularCurve_genus_eq_genusFF_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasCanonicalDivisor_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_isAlgClosed
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_mul_mem_lSpace_add
import Theorems.Thm_AlgebraicCurve_RiemannGenusReachedAt_eq_of_ge
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin
import Theorems.Thm_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached
import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord
import Theorems.Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_monic_coeff_natDegree_le_of_forall_valuationSubring
import Theorems.Thm_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ModularCurve_exists_mem_integers_transcendental_residue_finrank_eq_of_regularProlongation_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
p2m_attr_erase "simp" "ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one"
p2m_attr_erase "simp" "TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

noncomputable section

section DeuringEngine

open AlgebraicCurve IsLocalRing Polynomial IntermediateField

namespace A1b2bGenusFF
namespace DeuringLE

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

noncomputable def placeOfValuationSubring (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (V : ValuationSubring F) (hK : ∀ a : K, algebraMap K F a ∈ V) (hV : V ≠ ⊤) : Place K F where
  toValuationSubring := V
  algebraMap_mem' := hK
  ne_top' := hV
  isPrincipalIdealRing' :=
    ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin x V hK hV

theorem ord_neg_of_not_mem (v : Place K F) {f : F} (hf : f ∉ v.toValuationSubring) :
    v.ord f < 0 := by
  have hf0 : f ≠ 0 := fun h => hf (h ▸ v.toValuationSubring.zero_mem)
  by_contra h
  exact hf ((v.mem_iff_ord_nonneg hf0).mpr (not_lt.mp h))

theorem mem_valuationSubring_of_mem_lSpace (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) (m : ℕ) {f : F}
    (hf : f ∈ LSpace (m • D)) (V : ValuationSubring F) (hK : ∀ a : K, algebraMap K F a ∈ V) :
    (x ∈ V → f ∈ V) ∧ (x ∉ V → f * (x ^ m)⁻¹ ∈ V) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp [V.zero_mem]
  by_cases hV : V = ⊤
  · subst hV
    exact ⟨fun _ => ValuationSubring.mem_top _, fun _ => ValuationSubring.mem_top _⟩
  set v : Place K F := placeOfValuationSubring x V hK hV with hv
  have hVv : v.toValuationSubring = V := rfl
  have hford : ∀ w : Place K F, -((m • D) w) ≤ w.ord f :=
    ((mem_lSpace_iff_ord.mp hf).resolve_left hf0)
  have hfv : -((m : ℤ) * D v) ≤ v.ord f := by
    have := hford v
    simpa [Finsupp.smul_apply, smul_eq_mul, nsmul_eq_mul] using this
  rw [hD v] at hfv
  constructor
  · intro hxV
    rcases eq_or_ne x 0 with rfl | hx0
    · have : (0 : ℤ) ≤ v.ord f := by simpa [Place.ord_zero] using hfv
      rw [← hVv]
      exact (v.mem_iff_ord_nonneg hf0).mpr this
    · have hxord : 0 ≤ v.ord x := (v.mem_iff_ord_nonneg hx0).mp (hVv ▸ hxV)
      have hmax : max 0 (-v.ord x) = 0 := max_eq_left (by linarith)
      rw [hmax, mul_zero, neg_zero] at hfv
      rw [← hVv]
      exact (v.mem_iff_ord_nonneg hf0).mpr hfv
  · intro hxV
    have hx0 : x ≠ 0 := fun h => hxV (h ▸ V.zero_mem)
    have hxord : v.ord x < 0 := ord_neg_of_not_mem v (hVv ▸ hxV)
    have hmax : max 0 (-v.ord x) = -v.ord x := max_eq_right (by linarith)
    rw [hmax] at hfv
    have hne : f * (x ^ m)⁻¹ ≠ 0 := mul_ne_zero hf0 (inv_ne_zero (pow_ne_zero _ hx0))
    rw [← hVv]
    refine (v.mem_iff_ord_nonneg hne).mpr ?_
    rw [v.ord_mul hf0 (inv_ne_zero (pow_ne_zero _ hx0)), v.ord_inv, ← zpow_natCast,
      v.ord_zpow]
    nlinarith

theorem exists_poleDivisor [HasPrincipalDivisors K F] {x : F} (hx : x ≠ 0) :
    ∃ D : Divisor K F, ∀ v : Place K F, D v = max 0 (-v.ord x) := by
  obtain ⟨P, hP, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) x hx
  exact ⟨Finsupp.mapRange (fun n => max 0 (-n)) (by simp) P, fun v => by simp [hP v]⟩

theorem nonempty_place_of_transcendental [IsAlgClosed K] {x : F} (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] : Nonempty (Place K F) := by
  by_contra h
  have hx' : x ∈ (algebraMap K F).range :=
    Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed x hx fun v => (h ⟨v⟩).elim
  obtain ⟨c, rfl⟩ := hx'
  exact hx (isAlgebraic_algebraMap c)

theorem finiteDimensional_lSpace_zero_of_constantsAreBase (hC : ConstantsAreBase K F) :
    FiniteDimensional K (LSpace (0 : Divisor K F)) := by
  have h : LSpace (0 : Divisor K F) = LinearMap.range (Algebra.linearMap K F) := hC
  rw [h]
  infer_instance

theorem genusFF_eq_of_riemannGenusReachedAt [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))] (hC : ConstantsAreBase K F)
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    (genusFF K F : ℤ) = γ := by
  have h1 := (indexOfSpecialty_eq_of_genusReached h 0).2
  rw [indexOfSpecialty_eq_finrank_H1, ell_zero_eq_one_of_constantsAreBase hC, map_zero] at h1
  rw [genusFF]
  push_cast at h1 ⊢
  linarith

end Generic

section Riemann

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mul_mem_lSpace_sub_of_forall_eq_ord {f : F} {P : Divisor K F}
    (hP : ∀ v : Place K F, P v = v.ord f) {E : Divisor K F} {g : F} (hg : g ∈ LSpace E) :
    g * f ∈ LSpace (E - P) := by
  have hfmem : f ∈ LSpace (-P) :=
    mem_lSpace_iff_ord.mpr (Or.inr fun v => by simp [hP v])
  simpa [sub_eq_add_neg] using mul_mem_lSpace_add hg hfmem

noncomputable def mulRight (f : F) (E E' : Divisor K F)
    (h : ∀ g ∈ LSpace E, g * f ∈ LSpace E') : LSpace E →ₗ[K] LSpace E' where
  toFun g := ⟨(g : F) * f, h g g.2⟩
  map_add' a b := Subtype.ext (by simp [add_mul])
  map_smul' c a := Subtype.ext (by simp)

theorem ell_sub_eq_of_forall_eq_ord {f : F} (hf0 : f ≠ 0) {P : Divisor K F}
    (hP : ∀ v : Place K F, P v = v.ord f) (E : Divisor K F) : ell (E - P) = ell E := by
  have h1 : ∀ g ∈ LSpace E, g * f ∈ LSpace (E - P) := fun g hg =>
    mul_mem_lSpace_sub_of_forall_eq_ord hP hg
  have hP' : ∀ v : Place K F, (-P) v = v.ord f⁻¹ := fun v => by simp [hP v, Place.ord_inv]
  have h2 : ∀ g ∈ LSpace (E - P), g * f⁻¹ ∈ LSpace E := fun g hg => by
    simpa using mul_mem_lSpace_sub_of_forall_eq_ord hP' hg
  let e : LSpace E ≃ₗ[K] LSpace (E - P) :=
    { mulRight f E (E - P) h1 with
      invFun := mulRight f⁻¹ (E - P) E h2
      left_inv := fun g => Subtype.ext (by simp [mulRight, mul_inv_cancel_right₀ hf0])
      right_inv := fun g => Subtype.ext (by simp [mulRight, inv_mul_cancel_right₀ hf0]) }
  exact (LinearEquiv.finrank_eq e).symm

theorem exists_forall_degree_nsmul_sub_ell_eq [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))] {γ : ℤ} {D₀ : Divisor K F}
    (h : RiemannGenusReachedAt γ D₀) {D : Divisor K F} (hD : 0 < Divisor.degree D) :
    ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m →
      Divisor.degree (m • D) - (ell (m • D) : ℤ) = γ - 1 := by
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : ℕ, Divisor.degree D₀ + γ ≤ (m₁ : ℤ) * Divisor.degree D := by
    refine ⟨(Divisor.degree D₀ + γ).toNat, ?_⟩
    calc Divisor.degree D₀ + γ ≤ ((Divisor.degree D₀ + γ).toNat : ℤ) := Int.self_le_toNat _
      _ = ((Divisor.degree D₀ + γ).toNat : ℤ) * 1 := (mul_one _).symm
      _ ≤ ((Divisor.degree D₀ + γ).toNat : ℤ) * Divisor.degree D :=
          mul_le_mul_of_nonneg_left (by omega) (by positivity)
  refine ⟨m₁, fun m hm => ?_⟩
  have hdegm : Divisor.degree (m • D) = (m : ℤ) * Divisor.degree D := by
    rw [map_nsmul, nsmul_eq_mul]
  have hineq := h.isMax (m • D - D₀)
  have hmm : (m₁ : ℤ) * Divisor.degree D ≤ (m : ℤ) * Divisor.degree D :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hD.le
  have hell_pos : 0 < ell (m • D - D₀) := by
    have : (1 : ℤ) ≤ ell (m • D - D₀) := by
      rw [map_sub, hdegm] at hineq
      linarith
    exact_mod_cast this
  haveI : FiniteDimensional K (LSpace (m • D - D₀)) := finiteDimensional_lSpace _
  obtain ⟨⟨f, hfmem⟩, hf0⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := K) (M := LSpace (m • D - D₀))).mp hell_pos
  have hf0 : f ≠ 0 := fun h0 => hf0 (Subtype.ext h0)
  obtain ⟨P, hP, hP0⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  have hle : D₀ - P ≤ m • D := fun v => by
    have := (mem_lSpace_iff_ord.mp hfmem).resolve_left hf0 v
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_smul, Pi.smul_apply] at this ⊢
    rw [hP v]
    linarith
  have h' : RiemannGenusReachedAt γ (D₀ - P) :=
    { finite := finiteDimensional_lSpace _
      eq := by
        rw [ell_sub_eq_of_forall_eq_ord hf0 hP, map_sub, hP0, sub_zero]
        exact h.eq
      isMax := h.isMax }
  exact h'.eq_of_ge hle

end Riemann

section Prolongation

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

def constHom (R : RegularProlongation A F Fbar) : A →+* R.integers where
  toFun a := ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem coe_constHom (R : RegularProlongation A F Fbar) (a : A) :
    ((constHom R a : R.integers) : F) = algebraMap L F a := rfl

theorem residue_constHom (R : RegularProlongation A F Fbar) (a : A) :
    R.residue (constHom R a) = algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) :=
  R.residue_algebraMap a

theorem transcendental_coe [IsAlgClosed L] (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x)) : Transcendental L (x : F) := by
  intro halg
  have hint : IsIntegral L (x : F) := halg.isIntegral
  have h1 : (minpoly L (x : F)).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible L (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one L (x : F) h1
  have hcA : c ∈ A := (R.algebraMap_mem_iff c).mp (hc ▸ x.2)
  apply hx
  have hxeq : x = constHom R ⟨c, hcA⟩ := Subtype.ext hc.symm
  rw [hxeq, residue_constHom]
  exact isAlgebraic_algebraMap _

theorem residue_mem_lSpace_nsmul (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    [FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F]
    {D : Divisor L F} (hD : ∀ v : Place L F, D v = max 0 (-v.ord (x : F)))
    {Dbar : Divisor (ResidueField A) Fbar}
    (hDbar : ∀ w : Place (ResidueField A) Fbar, Dbar w = max 0 (-w.ord (R.residue x)))
    (m : ℕ) {f : R.integers} (hf : (f : F) ∈ LSpace (m • D)) :
    R.residue f ∈ LSpace (m • Dbar) := by
  obtain ⟨p, hp, hpdeg, hroot⟩ :=
    AlgebraicCurve.RegularProlongation.exists_monic_coeff_natDegree_le_of_forall_valuationSubring
      A R x hx (f : F) m
      (fun V hV hxV => (mem_valuationSubring_of_mem_lSpace (x : F) D hD m hf V hV).1 hxV)
      (fun V hV hxV => (mem_valuationSubring_of_mem_lSpace (x : F) D hD m hf V hV).2 hxV)
      (fun V hV => by
        rw [AlgebraicCurve.RegularProlongation.eq_integers_of_forall_mem_adjoin_iff
          A R x hx hfin hdeg V hV]
        exact f.2)
  have hM := AlgebraicCurve.RegularProlongation.mul_min_ord_residue_le_of_monic
    A R x f m p hp hpdeg hroot
  refine mem_lSpace_iff_ord.mpr (Or.inr fun w => ?_)
  have h1 := hM w
  have h2 : -((m : ℤ) * Dbar w) = (m : ℤ) * min 0 (w.ord (R.residue x)) := by
    rw [hDbar w, ← mul_neg]
    congr 1
    rcases le_total 0 (w.ord (R.residue x)) with h0 | h0
    · rw [max_eq_left (by linarith), min_eq_left h0, neg_zero]
    · rw [max_eq_right (by linarith), min_eq_right h0, neg_neg]
  have h3 : (m • Dbar) w = (m : ℤ) * Dbar w := by simp
  rw [h3, h2]
  exact h1

end Prolongation

section GenusLE

variable {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
  [IsCurveOver (ResidueField A) Fbar]

theorem genusFF_le (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar) :
    genusFF (ResidueField A) Fbar ≤ genusFF L F := by
  classical

  haveI hk : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : PerfectField (ResidueField A) := IsAlgClosed.perfectField _
  haveI : PerfectField L := IsAlgClosed.perfectField _
  have hxL : Transcendental L (x : F) := transcendental_coe R x hx
  haveI hfdb : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar :=
    Module.finite_of_finrank_pos hfin
  haveI hfd : FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F :=
    Module.finite_of_finrank_pos (hdeg ▸ hfin)
  haveI : Nonempty (Place L F) := nonempty_place_of_transcendental hxL
  haveI : Nonempty (Place (ResidueField A) Fbar) := nonempty_place_of_transcendental hx
  have hC : ConstantsAreBase L F :=
    constantsAreBase_of_deg_eq_one (Classical.arbitrary (Place L F))
      (IsCurveOver.deg_eq_one_of_isAlgClosed _)
  have hCb : ConstantsAreBase (ResidueField A) Fbar :=
    constantsAreBase_of_deg_eq_one (Classical.arbitrary (Place (ResidueField A) Fbar))
      (IsCurveOver.deg_eq_one_of_isAlgClosed _)
  haveI : FiniteDimensional L (LSpace (0 : Divisor L F)) :=
    finiteDimensional_lSpace_zero_of_constantsAreBase hC
  haveI : FiniteDimensional (ResidueField A) (LSpace (0 : Divisor (ResidueField A) Fbar)) :=
    finiteDimensional_lSpace_zero_of_constantsAreBase hCb
  haveI : Algebra.EssFiniteType L F :=
    essFiniteType_of_transcendental_of_finiteDimensional hxL hfd
  haveI : Algebra.EssFiniteType (ResidueField A) Fbar :=
    essFiniteType_of_transcendental_of_finiteDimensional hx hfdb

  obtain ⟨-, -, γ, D₀, hR⟩ := stichtenothGenusExists_of_isCurveOver hC
  obtain ⟨-, -, γb, Db₀, hRb⟩ := stichtenothGenusExists_of_isCurveOver hCb
  have hγ : (genusFF L F : ℤ) = γ := genusFF_eq_of_riemannGenusReachedAt hC hR
  have hγb : (genusFF (ResidueField A) Fbar : ℤ) = γb :=
    genusFF_eq_of_riemannGenusReachedAt hCb hRb

  have hx0 : (x : F) ≠ 0 := fun h0 => hxL (h0 ▸ isAlgebraic_zero)
  have hxb0 : R.residue x ≠ 0 := fun h0 => hx (h0 ▸ isAlgebraic_zero)
  obtain ⟨D, hD⟩ := exists_poleDivisor (K := L) hx0
  obtain ⟨Db, hDb⟩ := exists_poleDivisor (K := ResidueField A) hxb0
  have hdegD := Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord (x : F) hxL D hD
  have hdegDb := Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord (R.residue x) hx Db hDb
  have hDD : Divisor.degree D = Divisor.degree Db := by rw [hdegD, hdegDb, hdeg]
  have hDbpos : 0 < Divisor.degree Db := by rw [hdegDb]; exact_mod_cast hfin

  obtain ⟨m, hm⟩ := exists_forall_degree_nsmul_sub_ell_eq hRb hDbpos
  have hexact : Divisor.degree (m • Db) - (ell (m • Db) : ℤ) = γb - 1 := hm m le_rfl

  have hRi : Divisor.degree (m • D) - (ell (m • D) : ℤ) ≤ γ - 1 := hR.isMax (m • D)
  have hdegm : Divisor.degree (m • D) = Divisor.degree (m • Db) := by
    rw [map_nsmul, map_nsmul, hDD]

  haveI : FiniteDimensional L (LSpace (m • D)) := finiteDimensional_lSpace _
  haveI : FiniteDimensional (ResidueField A) (LSpace (m • Db)) := finiteDimensional_lSpace _
  set S : Submodule (ResidueField A) Fbar := Submodule.span (ResidueField A)
    {h : Fbar | ∃ f : R.integers, (f : F) ∈ LSpace (m • D) ∧ R.residue f = h} with hS
  have hSle : S ≤ LSpace (m • Db) := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact residue_mem_lSpace_nsmul R x hx hfin hdeg hD hDb m hf
  have hfinS : Module.finrank (ResidueField A) S = Module.finrank L (LSpace (m • D)) :=
    AlgebraicCurve.RegularProlongation.finrank_span_residue_eq_finrank A R x hx hfin hdeg
      (LSpace (m • D))
  have hmono : Module.finrank (ResidueField A) S ≤
      Module.finrank (ResidueField A) (LSpace (m • Db)) := Submodule.finrank_mono hSle
  have hell : (ell (m • D) : ℤ) ≤ ell (m • Db) := by
    have : ell (m • D) ≤ ell (m • Db) := by
      change Module.finrank L (LSpace (m • D)) ≤ Module.finrank (ResidueField A) (LSpace (m • Db))
      rw [← hfinS]
      exact hmono
    exact_mod_cast this

  have hγle : γb ≤ γ := by linarith
  have : (genusFF (ResidueField A) Fbar : ℤ) ≤ genusFF L F := by rw [hγ, hγb]; exact hγle
  exact_mod_cast this

end GenusLE

end A1b2bGenusFF.DeuringLE
p2m_reactivate "P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.A1b2bGenusFF P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.A1b2bGenusFF.DeuringLE"
p2m_reactivate "P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.A1b2bGenusFF"

end DeuringEngine
p2m_reactivate "P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.A1b2bGenusFF P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.A1b2bGenusFF.DeuringLE"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve

namespace A1b2bGenusFF

section JJ

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

abbrev JJ : modularFunctionFieldFullC K N := ⟨jqModC K, jqModC_mem_full K N⟩

omit [NeZero N] in
theorem transcendental_JJ : Transcendental K (JJ K N) := by
  have h : Transcendental K
      (algebraMap (modularFunctionFieldFullC K N) (LaurentSeries K) (JJ K N)) :=
    ModularCurve.transcendental_jqModC K
  exact (transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective _ _)).mp h

theorem finrank_adjoin_JJ (hN : (N : K) ≠ 0) :
    Module.finrank (IntermediateField.adjoin K ({JJ K N} : Set (modularFunctionFieldFullC K N)))
      (modularFunctionFieldFullC K N) = dedekindPsi N :=
  ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K N hN

theorem finiteDimensional_adjoin_JJ (hN : (N : K) ≠ 0) :
    FiniteDimensional
      (IntermediateField.adjoin K ({JJ K N} : Set (modularFunctionFieldFullC K N)))
      (modularFunctionFieldFullC K N) :=
  Module.finite_of_finrank_pos
    (by rw [finrank_adjoin_JJ K N hN]; exact ModularCurve.dedekindPsi_pos N (NeZero.ne N))

end JJ
p2m_reactivate "P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.A1b2bGenusFF P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.A1b2bGenusFF.DeuringLE"

section Deuring

theorem genusFF_fullC_residueField_le (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) :
    genusFF (IsLocalRing.ResidueField A)
        (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) ≤
      genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := by
  haveI hk : IsAlgClosed (IsLocalRing.ResidueField A) :=
    ValuationSubring.isAlgClosed_residueField A
  haveI : PerfectField (IsLocalRing.ResidueField A) := IsAlgClosed.perfectField _
  haveI : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    ModularCurve.isCurveOver_modularFunctionFieldBar N
  haveI : IsCurveOver (IsLocalRing.ResidueField A)
      (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :=
    ModularCurve.isCurveOver_modularFunctionFieldFullC (IsLocalRing.ResidueField A) N

  obtain ⟨R, hspec⟩ := ModularCurve.exists_regularProlongation_modularFunctionFieldBar N hℓN A hA

  obtain ⟨x, hx, hfin, hdeg⟩ :=
    ModularCurve.exists_mem_integers_transcendental_residue_finrank_eq_of_regularProlongation_modularFunctionFieldBar
      N ℓ hℓN A hA R hspec
  exact DeuringLE.genusFF_le R x hx hfin hdeg

theorem genusFF_bar_eq_genusFormula (N : ℕ) [NeZero N] :
    (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℚ) = genusFormula N := by
  haveI := ModularCurve.hasCanonicalDivisor_modularFunctionFieldBar N
  rw [← ModularCurve.genus_eq_genusFF_modularFunctionFieldBar N]
  exact ModularCurve.genus_modularFunctionFieldBar_eq_genusFormula N

theorem charP_residueField {L : Type*} [Field L] (A : ValuationSubring L) {ℓ : ℕ} [Fact ℓ.Prime]
    (hA : A.LiesOverPrime ℓ) : CharP (IsLocalRing.ResidueField A) ℓ := by
  have hℓ : ((ℓ : A) : L) ∈ A.nonunits := by first | exact hA | simpa using hA | (simp at hA; exact hA) | (simp ; exact hA) | (simp at hA ⊢; exact hA)
  rw [ValuationSubring.coe_mem_nonunits_iff] at hℓ
  have h0 : (ℓ : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]
    exact hℓ
  exact (CharP.charP_iff_prime_eq_zero Fact.out).mpr h0

end Deuring
p2m_reactivate "P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.A1b2bGenusFF P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.A1b2bGenusFF.DeuringLE"

section Glue

variable {k K : Type*} [Field k] [Field K] (φ : k →+* K) (N : ℕ) [NeZero N]

theorem coeffMap_algebraMap_const (c : k) :
    coeffMap φ (algebraMap k (LaurentSeries k) c) = algebraMap K (LaurentSeries K) (φ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

omit [NeZero N] in

theorem coeffMap_mem_fullC {x : LaurentSeries k} (hx : x ∈ modularFunctionFieldFullC k N) :
    coeffMap φ x ∈ modularFunctionFieldFullC K N := by
  change x ∈ IntermediateField.adjoin k (divisorExpansionsC k N) at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨d, hd, hdN, rfl⟩ := hx
    rw [ModularCurve.coeffMap_qExpand, coeffMap_jqModC]
    exact jqModCd_mem_full K N hdN
  | algebraMap c =>
    rw [coeffMap_algebraMap_const]
    exact IntermediateField.algebraMap_mem _ _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | inv x _ hx =>
    rw [map_inv₀]
    exact inv_mem hx
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact mul_mem hx hy

def fullCMap : modularFunctionFieldFullC k N →+* modularFunctionFieldFullC K N :=
  ((coeffMap φ).comp (modularFunctionFieldFullC k N).val.toRingHom).codRestrict
    (modularFunctionFieldFullC K N) (fun x => coeffMap_mem_fullC φ N x.2)

omit [NeZero N] in
@[scoped simp] theorem coe_fullCMap (x : modularFunctionFieldFullC k N) :
    ((fullCMap φ N x : modularFunctionFieldFullC K N) : LaurentSeries K) = coeffMap φ x := rfl

include φ in

theorem genusFF_fullC_eq_of_ringHom [IsAlgClosed k] [IsAlgClosed K] (hN : (N : K) ≠ 0) :
    genusFF K (modularFunctionFieldFullC K N) = genusFF k (modularFunctionFieldFullC k N) := by
  have hNk : (N : k) ≠ 0 := by
    intro h
    apply hN
    have := congrArg φ h
    rwa [map_natCast, map_zero] at this
  letI : Algebra k K := φ.toAlgebra
  letI : Algebra (modularFunctionFieldFullC k N) (modularFunctionFieldFullC K N) :=
    (fullCMap φ N).toAlgebra
  letI : Algebra k (modularFunctionFieldFullC K N) :=
    ((algebraMap K (modularFunctionFieldFullC K N)).comp φ).toAlgebra
  haveI : IsScalarTower k K (modularFunctionFieldFullC K N) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower k (modularFunctionFieldFullC k N) (modularFunctionFieldFullC K N) := by
    refine IsScalarTower.of_algebraMap_eq (fun c => ?_)
    apply Subtype.ext
    show algebraMap K (LaurentSeries K) (φ c) = coeffMap φ (algebraMap k (LaurentSeries k) c)
    rw [coeffMap_algebraMap_const]
  haveI := ModularCurve.isCurveOver_modularFunctionFieldFullC k N
  haveI := ModularCurve.isCurveOver_modularFunctionFieldFullC K N
  refine AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_isAlgClosed
    k (modularFunctionFieldFullC k N) K (modularFunctionFieldFullC K N)
    ⟨JJ k N, transcendental_JJ k N, finiteDimensional_adjoin_JJ k N hNk⟩
    ⟨JJ K N, transcendental_JJ K N, finiteDimensional_adjoin_JJ K N hN⟩ ?_

  rw [eq_top_iff]
  intro x _
  have hle : modularFunctionFieldFullC K N ≤
      (IntermediateField.adjoin K (Set.range (algebraMap (modularFunctionFieldFullC k N)
        (modularFunctionFieldFullC K N)))).map (modularFunctionFieldFullC K N).val := by
    change IntermediateField.adjoin K (divisorExpansionsC K N) ≤ _
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨d, hd, hdN, rfl⟩
    haveI := hd
    refine (IntermediateField.mem_map _).mpr
      ⟨⟨qExpand K d (jqModC K), jqModCd_mem_full K N hdN⟩, ?_, rfl⟩
    apply IntermediateField.subset_adjoin
    refine ⟨⟨qExpand k d (jqModC k), jqModCd_mem_full k N hdN⟩, ?_⟩
    apply Subtype.ext
    show coeffMap φ (qExpand k d (jqModC k)) = qExpand K d (jqModC K)
    rw [ModularCurve.coeffMap_qExpand, coeffMap_jqModC]
  obtain ⟨y, hy, hyx⟩ := (IntermediateField.mem_map _).mp (hle x.2)
  rwa [← Subtype.ext hyx]

theorem natCast_ne_zero_of_charP {K R : Type*} [Field K] [Field R] {ℓ : ℕ} [CharP K ℓ]
    [CharP R ℓ] {N : ℕ} (hN : (N : K) ≠ 0) : (N : R) ≠ 0 := fun h =>
  hN ((CharP.cast_eq_zero_iff K ℓ N).mpr ((CharP.cast_eq_zero_iff R ℓ N).mp h))

end Glue
p2m_reactivate "P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.A1b2bGenusFF P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.A1b2bGenusFF.DeuringLE"

section BarFullC

variable (L : Type*) [Field L] [Algebra ℚ L]

theorem coeffEmb_qExpand_jq (d : ℕ) [NeZero d] :
    coeffEmb L (qExpand ℚ d jq) = qExpand L d (jqModC L) := by
  show coeffMap (algebraMap ℚ L) (qExpand ℚ d jq) = _
  rw [ModularCurve.coeffMap_qExpand, ← jqModC_rat, coeffMap_jqModC]

theorem laurentBaseChange_full_eq_fullC (N : ℕ) [NeZero N] :
    laurentBaseChange L (modularFunctionFieldFull N) = modularFunctionFieldFullC L N := by
  apply le_antisymm
  · intro y hy
    rw [mem_laurentBaseChange_iff] at hy
    refine (Subfield.closure_le (t := (modularFunctionFieldFullC L N).toSubfield)).mpr ?_ hy
    rintro z (⟨c, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact (modularFunctionFieldFullC L N).algebraMap_mem c
    · have hx' : x ∈ (modularFunctionFieldFull N).toSubfield := hx
      rw [modularFunctionFieldFull, IntermediateField.adjoin_toSubfield] at hx'
      refine (Subfield.closure_le
        (t := (modularFunctionFieldFullC L N).toSubfield.comap (coeffEmb L))).mpr ?_ hx'
      rintro w (⟨r, rfl⟩ | ⟨d, hd, hdN, rfl⟩)
      · show coeffEmb L (algebraMap ℚ _ r) ∈ modularFunctionFieldFullC L N
        rw [show coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) r) =
            algebraMap L (LaurentSeries L) (algebraMap ℚ L r) from
          coeffMap_algebraMap_const (algebraMap ℚ L) r]
        exact algebraMap_mem _ _
      · haveI := hd
        show coeffEmb L (qExpand ℚ d jq) ∈ modularFunctionFieldFullC L N
        rw [coeffEmb_qExpand_jq]
        exact jqModCd_mem_full L N hdN
  · rw [modularFunctionFieldFullC, IntermediateField.adjoin_le_iff]
    rintro y ⟨d, hd, hdN, rfl⟩
    haveI := hd
    show qExpand L d (jqModC L) ∈ laurentBaseChange L (modularFunctionFieldFull N)
    rw [← coeffEmb_qExpand_jq]
    exact coeffEmb_mem_laurentBaseChange L (jqd_mem_full N hdN)

theorem genusFF_bar_eq_genusFF_fullC (N : ℕ) [NeZero N] :
    genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) =
      genusFF (AlgebraicClosure ℚ) (modularFunctionFieldFullC (AlgebraicClosure ℚ) N) := by
  show genusFF (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) = _
  rw [laurentBaseChange_full_eq_fullC (AlgebraicClosure ℚ) N]

end BarFullC
p2m_reactivate "P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.A1b2bGenusFF P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.A1b2bGenusFF.DeuringLE"

section Cases

variable (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N]

theorem genusFF_fullC_eq_bar_of_charZero [CharZero K] (hN : (N : K) ≠ 0) :
    genusFF K (modularFunctionFieldFullC K N) =
      genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := by

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ
    all_goals first | rfl | skip
  let φ : AlgebraicClosure ℚ →+* K :=
    (IsAlgClosed.lift (R := ℚ) (S := AlgebraicClosure ℚ) (M := K)).toRingHom
  rw [genusFF_fullC_eq_of_ringHom φ N hN, genusFF_bar_eq_genusFF_fullC N]

theorem genusFF_fullC_le_bar_of_charP (hN : (N : K) ≠ 0) {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] :
    genusFF K (modularFunctionFieldFullC K N) ≤
      genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := by
  have hℓN : ¬ ℓ ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K ℓ N).mpr h)
  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨ℓ, Fact.out⟩
  haveI := ValuationSubring.isAlgClosed_residueField A
  haveI := charP_residueField A hA
  haveI : CharP (AlgebraicClosure (ZMod ℓ)) ℓ :=
    (Algebra.charP_iff (ZMod ℓ) (AlgebraicClosure (ZMod ℓ)) ℓ).mp inferInstance
  letI : Algebra (ZMod ℓ) K := ZMod.algebra K ℓ
  letI : Algebra (ZMod ℓ) (IsLocalRing.ResidueField A) := ZMod.algebra _ ℓ
  let φ₂ : AlgebraicClosure (ZMod ℓ) →+* K :=
    (IsAlgClosed.lift (R := ZMod ℓ) (S := AlgebraicClosure (ZMod ℓ)) (M := K)).toRingHom
  let φ₁ : AlgebraicClosure (ZMod ℓ) →+* IsLocalRing.ResidueField A :=
    (IsAlgClosed.lift (R := ZMod ℓ) (S := AlgebraicClosure (ZMod ℓ))
      (M := IsLocalRing.ResidueField A)).toRingHom
  have hNA : (N : IsLocalRing.ResidueField A) ≠ 0 := natCast_ne_zero_of_charP (K := K) hN
  rw [genusFF_fullC_eq_of_ringHom φ₂ N hN, ← genusFF_fullC_eq_of_ringHom φ₁ N hNA]
  exact genusFF_fullC_residueField_le N hℓN A hA

theorem genusFF_fullC_eq_bar_of_lt_five (hN : (N : K) ≠ 0) {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hℓ : ℓ < 5) :
    genusFF K (modularFunctionFieldFullC K N) =
      genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := by
  have hle := genusFF_fullC_le_bar_of_charP K N hN (ℓ := ℓ)
  have hge :=
    ModularCurve.genusFormula_le_genusFF_modularFunctionFieldFullC_of_lt_five K N hN hℓ
  rw [← genusFF_bar_eq_genusFormula N] at hge
  have hge' : genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ≤
      genusFF K (modularFunctionFieldFullC K N) := by exact_mod_cast hge
  omega

end Cases
p2m_reactivate "P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.A1b2bGenusFF P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.A1b2bGenusFF.DeuringLE"

end A1b2bGenusFF
p2m_reactivate "P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.A1b2bGenusFF P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.A1b2bGenusFF.DeuringLE"

open A1b2bGenusFF in
theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) :
    genusFF K (modularFunctionFieldFullC K N) =
      genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := by
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hprime | rfl
  · haveI : Fact p.Prime := ⟨hprime⟩
    by_cases h5 : 5 ≤ p
    ·
      exact ModularCurve.genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le
        K N hN h5
    ·
      exact genusFF_fullC_eq_bar_of_lt_five K N hN (ℓ := p) (by omega)
  ·
    haveI : CharZero K := CharP.charP_to_charZero K
    exact genusFF_fullC_eq_bar_of_charZero K N hN

end
end S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar
end P2MW
export P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar (solution)
