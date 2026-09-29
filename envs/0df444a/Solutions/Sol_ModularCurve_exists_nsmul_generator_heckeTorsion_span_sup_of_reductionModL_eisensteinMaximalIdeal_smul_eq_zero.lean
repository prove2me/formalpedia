-- Prove2me | solution 1 for ModularCurve.exists_nsmul_generator_heckeTorsion_span_sup_of_reductionModL_eisensteinMaximalIdeal_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/9cd3218e-65a1-5329-bbf0-709f5a495758

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_EisensteinIdeal
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_HeckeOperatorModL
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_reductionInputsModL_of_not_dvd
import Theorems.Thm_ModularCurve_reductionModL_heckeOperatorBar
import Theorems.Thm_ModularCurve_reductionModL_heckeOperatorBar_of_ne
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_heckeInputsFibre_of_prime
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_of_finrank_eq_dedekindPsi
import Theorems.Thm_ModularCurve_heckePic0Fibre_eq_neg_fricke_smul_of_prime
import Theorems.Thm_ModularCurve_eq_zero_or_exists_eq_nsmul_of_heckePic0Fibre_eq_eisenstein_of_heckeOperatorModL_eq_of_smul_eq_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_nsmul_generator_heckeTorsion_span_sup_of_reductionModL_eisensteinMaximalIdeal_smul_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree WeierstrassCurve.Affine.Point.instFinite ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU"
p2m_attr_erase "simp" "ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply"
p2m_attr_erase "simp" "ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def"
p2m_attr_erase "simp" "ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_nsmul_generator_heckeTorsion_span_sup_of_reductionModL_eisensteinMaximalIdeal_smul_eq_zero.ModularCurve AlgebraicCurve P2MW.S_ModularCurve_exists_nsmul_generator_heckeTorsion_span_sup_of_reductionModL_eisensteinMaximalIdeal_smul_eq_zero.AlgebraicCurve IntermediateField"
open scoped Pointwise

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Pic Pic0 Pic0.mk Pic0.mk_surjective Place.smul_toValuationSubring Divisor.smul_single Pic0.degZeroSMulHom Pic0.smul_mk Place.congrRingEquiv Place.congrRingEquiv_toValuationSubring Divisor.congr Divisor.congr_single Pic0.degZeroCongr Pic0.congr"
namespace CongrSmul
p2m_open "AlgebraicCurve"

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (e : F ≃ₐ[K] F') (τ : F ≃ₐ[K] F)

abbrev conj : F' ≃ₐ[K] F' := e.symm.trans (τ.trans e)

theorem conj_symm_apply (y : F') : (conj e τ).symm y = e (τ.symm (e.symm y)) := rfl

theorem he : ∀ a : K, e.toRingEquiv (algebraMap K F a) = algebraMap K F' a := fun a => e.commutes a

theorem place_congr_smul (v : Place K F) :
    Place.congrRingEquiv e.toRingEquiv (he e) (τ • v) = conj e τ • Place.congrRingEquiv e.toRingEquiv (he e) v := by
  ext x
  rw [Place.congrRingEquiv_toValuationSubring, Place.smul_toValuationSubring, Place.smul_toValuationSubring,
    Place.congrRingEquiv_toValuationSubring, ValuationSubring.mem_comap,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_comap]
  rw [AlgEquiv.smul_def, AlgEquiv.smul_def, AlgEquiv.aut_inv, AlgEquiv.aut_inv]
  change τ.symm (e.symm x) ∈ v.toValuationSubring ↔ e.symm ((conj e τ).symm x) ∈ v.toValuationSubring
  rw [conj_symm_apply, AlgEquiv.symm_apply_apply]

theorem divisor_congr_smul (D : Divisor K F) :
    Divisor.congr e.toRingEquiv (he e) (τ • D) = conj e τ • Divisor.congr e.toRingEquiv (he e) D := by
  induction D using Finsupp.induction with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | single_add v n D _ _ ih =>
      rw [smul_add, map_add, map_add, smul_add, ih, Divisor.smul_single, Divisor.congr_single,
        Divisor.congr_single, Divisor.smul_single, place_congr_smul]

theorem pic0_congr_smul (x : Pic0 K F) :
    Pic0.congr e.toRingEquiv (he e) (τ • x) = conj e τ • Pic0.congr e.toRingEquiv (he e) x := by
  obtain ⟨E, rfl⟩ := Pic0.mk_surjective x
  rw [Pic0.smul_mk]
  change Pic0.mk (Pic0.degZeroCongr e.toRingEquiv (he e) (Pic0.degZeroSMulHom τ E)) =
    conj e τ • Pic0.mk (Pic0.degZeroCongr e.toRingEquiv (he e) E)
  rw [Pic0.smul_mk]
  exact congrArg Pic0.mk (Subtype.ext (divisor_congr_smul e τ (E : Divisor K F)))

end AlgebraicCurve.CongrSmul

namespace ModularCurve
p2m_export "ModularCurve" "heckeOperatorBar HeckeOperatorsCommuteBar heckeModuleBar heckeModuleBar_heckeGen_smul heckeModuleBar_smul_of_not heckeModuleBar_C_smul JZero qExpand dedekindPsi HeckeAlg heckeGen heckeTorsion eisensteinSystem_of_not_dvd eisensteinSystem_of_dvd eisensteinEval eisensteinEval_heckeGen eisensteinMaximalIdeal mem_eisensteinMaximalIdeal_iff natCast_mem_eisensteinMaximalIdeal ReductionInputsModL reductionModL modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full JZeroC jqModC jqNModC modularFunctionFieldC jqModC_mem jqNModC_mem HeckeInputsFibre heckePic0Fibre heckeOperatorModL reductionInputsModL_of_not_dvd reductionModL_heckeOperatorBar reductionModL_heckeOperatorBar_of_ne modularFunctionFieldC_eq_modularFunctionFieldFullC heckeInputsFibre_of_prime finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi exists_algEquiv_swap_jqModC_jqNModC_of_finrank_eq_dedekindPsi heckePic0Fibre_eq_neg_fricke_smul_of_prime eq_zero_or_exists_eq_nsmul_of_heckePic0Fibre_eq_eisenstein_of_heckeOperatorModL_eq_of_smul_eq_neg"
namespace RankOneAsmDeg
p2m_open "ModularCurve"

variable (K : Type*) [Field K]

abbrev A0 : IntermediateField K (LaurentSeries K) :=
  IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))

theorem finrank_adjoin_mk_eq_relfinrank (X : IntermediateField K (LaurentSeries K))
    (x : LaurentSeries K) (hx : x ∈ X) :
    Module.finrank (IntermediateField.adjoin K ({(⟨x, hx⟩ : ↥X)} : Set ↥X)) X =
      IntermediateField.relfinrank (IntermediateField.adjoin K ({x} : Set (LaurentSeries K))) X := by
  have hle : IntermediateField.adjoin K ({x} : Set (LaurentSeries K)) ≤ X :=
    adjoin_simple_le_iff.mpr hx
  rw [relfinrank_eq_finrank_of_le hle]
  set A' : IntermediateField K ↥X := IntermediateField.adjoin K ({(⟨x, hx⟩ : ↥X)} : Set ↥X)
  have hlift : lift A' = IntermediateField.adjoin K ({x} : Set (LaurentSeries K)) :=
    IntermediateField.lift_adjoin_simple K X ⟨x, hx⟩
  let i : A' ≃+* IntermediateField.adjoin K ({x} : Set (LaurentSeries K)) :=
    ((liftAlgEquiv A').trans (equivOfEq hlift)).toRingEquiv
  let jj : X ≃+* extendScalars hle :=
    { toFun := fun y => ⟨y.1, y.2⟩
      invFun := fun y => ⟨y.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  refine Algebra.finrank_eq_of_equiv_equiv i jj ?_
  refine RingHom.ext fun a => Subtype.ext ?_
  rfl

theorem relfinrank_A0_fullC (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0) :
    IntermediateField.relfinrank (A0 K) (modularFunctionFieldFullC K M) = dedekindPsi M := by
  rw [← finrank_adjoin_mk_eq_relfinrank K (modularFunctionFieldFullC K M) (jqModC K)
    (jqModC_mem_full K M)]
  exact finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K M hM

theorem not_ringChar_dvd (M : ℕ) (hM : (M : K) ≠ 0) : ¬ ringChar K ∣ M := fun h =>
  hM ((ringChar.spec K M).mpr h)

theorem modularFunctionFieldC_eq_fullC (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0) :
    modularFunctionFieldC K M = modularFunctionFieldFullC K M :=
  haveI : CharP K (ringChar K) := ringChar.charP K
  modularFunctionFieldC_eq_modularFunctionFieldFullC K (ringChar K) M (not_ringChar_dvd K M hM)

theorem A0_le (M : ℕ) [NeZero M] : A0 K ≤ modularFunctionFieldC K M :=
  adjoin_simple_le_iff.mpr (jqModC_mem K M)

theorem adjoin_A0_eq_extendScalars (M : ℕ) [NeZero M] :
    IntermediateField.adjoin (A0 K) ({jqNModC K M} : Set (LaurentSeries K)) =
      extendScalars (A0_le K M) := by
  apply IntermediateField.restrictScalars_injective K
  erw [adjoin_adjoin_left]
  rw [Set.singleton_union]
  rfl

theorem finrank_A0_adjoin (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0) :
    Module.finrank (A0 K) (IntermediateField.adjoin (A0 K) ({jqNModC K M} : Set (LaurentSeries K))) =
      dedekindPsi M := by
  rw [adjoin_A0_eq_extendScalars, ← relfinrank_eq_finrank_of_le (A0_le K M),
    modularFunctionFieldC_eq_fullC K M hM]
  exact relfinrank_A0_fullC K M hM

end ModularCurve.RankOneAsmDeg

namespace ModularCurve
p2m_export "ModularCurve" "heckeOperatorBar HeckeOperatorsCommuteBar heckeModuleBar heckeModuleBar_heckeGen_smul heckeModuleBar_smul_of_not heckeModuleBar_C_smul JZero qExpand dedekindPsi HeckeAlg heckeGen heckeTorsion eisensteinSystem_of_not_dvd eisensteinSystem_of_dvd eisensteinEval eisensteinEval_heckeGen eisensteinMaximalIdeal mem_eisensteinMaximalIdeal_iff natCast_mem_eisensteinMaximalIdeal ReductionInputsModL reductionModL modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full JZeroC jqModC jqNModC modularFunctionFieldC jqModC_mem jqNModC_mem HeckeInputsFibre heckePic0Fibre heckeOperatorModL reductionInputsModL_of_not_dvd reductionModL_heckeOperatorBar reductionModL_heckeOperatorBar_of_ne modularFunctionFieldC_eq_modularFunctionFieldFullC heckeInputsFibre_of_prime finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi exists_algEquiv_swap_jqModC_jqNModC_of_finrank_eq_dedekindPsi heckePic0Fibre_eq_neg_fricke_smul_of_prime eq_zero_or_exists_eq_nsmul_of_heckePic0Fibre_eq_eisenstein_of_heckeOperatorModL_eq_of_smul_eq_neg"
p2m_open "ModularCurve"

namespace RankOneAsm

attribute [local instance] ModularCurve.heckeModuleBar

variable {p : ℕ} [Fact p.Prime]

theorem heckeGen_sub_C_mem_eisensteinMaximalIdeal (q : ℕ) (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) ≠ p) :
    heckeGen ℓ - MvPolynomial.C (((ℓ : ℕ) : ℤ) + 1) ∈ eisensteinMaximalIdeal p q := by
  rw [mem_eisensteinMaximalIdeal_iff, map_sub, eisensteinEval_heckeGen]
  have hnd : ¬ (ℓ : ℕ) ∣ p := fun h =>
    hℓ (((Nat.prime_dvd_prime_iff_eq ℓ.2 (Fact.out)).mp h))
  rw [eisensteinSystem_of_not_dvd hnd, eisensteinEval, MvPolynomial.aeval_C]
  have h0 : (1 : ℤ) + ((ℓ : ℕ) : ℤ) - (algebraMap ℤ ℤ (((ℓ : ℕ) : ℤ) + 1)) = 0 := by simp; ring
  rw [h0]
  exact dvd_zero _

theorem heckeGen_self_sub_one_mem_eisensteinMaximalIdeal (q : ℕ) :
    heckeGen ⟨p, Fact.out⟩ - MvPolynomial.C 1 ∈ eisensteinMaximalIdeal p q := by
  rw [mem_eisensteinMaximalIdeal_iff, map_sub, eisensteinEval_heckeGen,
    eisensteinSystem_of_dvd (dvd_refl p), eisensteinEval, MvPolynomial.aeval_C]
  simp

variable (p) in

def kerSocle (q : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ)) : AddSubgroup (JZero p) where
  carrier := {y | ∀ g ∈ eisensteinMaximalIdeal p q, reductionModL A p (g • y) = 0}
  zero_mem' := fun g _ => by rw [smul_zero, map_zero]
  add_mem' := fun {a b} ha hb g hg => by rw [smul_add, map_add, ha g hg, hb g hg, add_zero]
  neg_mem' := fun {a} ha g hg => by rw [smul_neg, map_neg, ha g hg, neg_zero]

variable {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}

theorem mem_kerSocle {y : JZero p} :
    y ∈ kerSocle p q A ↔ ∀ g ∈ eisensteinMaximalIdeal p q, reductionModL A p (g • y) = 0 :=
  Iff.rfl

theorem natCast_smul_reduction_eq_zero {y : JZero p} (hy : y ∈ kerSocle p q A) :
    (q : ℤ) • reductionModL A p y = 0 := by
  have h := hy _ (natCast_mem_eisensteinMaximalIdeal p q)
  have hC : ((q : ℕ) : HeckeAlg) = MvPolynomial.C ((q : ℕ) : ℤ) := by
    rw [map_natCast]
  rw [hC, heckeModuleBar_C_smul, map_zsmul] at h
  exact h

theorem reduction_eq_zero_of_not (hc : ¬ HeckeOperatorsCommuteBar p) {y : JZero p}
    (hy : y ∈ kerSocle p q A) : reductionModL A p y = 0 := by
  have h := hy _ (heckeGen_self_sub_one_mem_eisensteinMaximalIdeal (p := p) q)
  rw [heckeModuleBar_smul_of_not hc, map_sub, heckeGen, MvPolynomial.constantCoeff_X,
    MvPolynomial.constantCoeff_C, zero_sub, neg_smul, one_smul, map_neg, neg_eq_zero] at h
  exact h

theorem reduction_heckeOperatorBar (hc : HeckeOperatorsCommuteBar p) {y : JZero p}
    (hy : y ∈ kerSocle p q A) (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) ≠ p) :
    reductionModL A p (heckeOperatorBar p ℓ y) =
      (((ℓ : ℕ) : ℤ) + 1) • reductionModL A p y := by
  have h := hy _ (heckeGen_sub_C_mem_eisensteinMaximalIdeal (p := p) q ℓ hℓ)
  rw [sub_smul, map_sub, sub_eq_zero, heckeModuleBar_heckeGen_smul hc, heckeModuleBar_C_smul,
    map_zsmul] at h
  exact h

theorem reduction_heckeOperatorBar_self (hc : HeckeOperatorsCommuteBar p) {y : JZero p}
    (hy : y ∈ kerSocle p q A) :
    reductionModL A p (heckeOperatorBar p ⟨p, Fact.out⟩ y) = reductionModL A p y := by
  have h := hy _ (heckeGen_self_sub_one_mem_eisensteinMaximalIdeal (p := p) q)
  rw [sub_smul, map_sub, sub_eq_zero, heckeModuleBar_heckeGen_smul hc, heckeModuleBar_C_smul,
    one_smul] at h
  exact h

section SpecialFibre

variable [Fact q.Prime]

theorem charP_residueField (hA : A.LiesOverPrime q) : CharP (IsLocalRing.ResidueField A) q :=
  ValuationSubring.residueField_charP_of_liesOverPrime A (Fact.out) hA

theorem not_dvd (hqp : q ≠ p) : ¬ q ∣ p := fun h =>
  hqp ((Nat.prime_dvd_prime_iff_eq (Fact.out) (Fact.out)).mp h)

theorem natCast_level_ne_zero (hqp : q ≠ p) (hA : A.LiesOverPrime q) :
    ((p : ℕ) : IsLocalRing.ResidueField A) ≠ 0 := by
  haveI := charP_residueField (A := A) hA
  rw [Ne, CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A) q]
  exact not_dvd hqp

theorem fieldC_eq (hqp : q ≠ p) (hA : A.LiesOverPrime q) :
    modularFunctionFieldC (IsLocalRing.ResidueField A) p =
    modularFunctionFieldFullC (IsLocalRing.ResidueField A) p := by
  haveI := charP_residueField (A := A) hA
  exact modularFunctionFieldC_eq_modularFunctionFieldFullC (IsLocalRing.ResidueField A) q p
    (not_dvd hqp)

def cg (hqp : q ≠ p) (hA : A.LiesOverPrime q) :
    Pic0 (IsLocalRing.ResidueField A) (modularFunctionFieldC (IsLocalRing.ResidueField A) p) ≃+
    JZeroC (IsLocalRing.ResidueField A) p :=
  Pic0.congr (IntermediateField.equivOfEq (fieldC_eq (p := p) hqp hA)).toRingEquiv
    (fun a => (IntermediateField.equivOfEq (fieldC_eq (p := p) hqp hA)).commutes a)

def imageZ (hqp : q ≠ p) (hA : A.LiesOverPrime q) : AddSubgroup (Pic0 (IsLocalRing.ResidueField A)
    (modularFunctionFieldC (IsLocalRing.ResidueField A) p)) :=
  ((kerSocle p q A).map (reductionModL A p)).map (cg (p := p) hqp hA).symm.toAddMonoidHom

theorem mem_imageZ (hqp : q ≠ p) (hA : A.LiesOverPrime q) {z : Pic0 (IsLocalRing.ResidueField A)
    (modularFunctionFieldC (IsLocalRing.ResidueField A) p)} :
    z ∈ imageZ (p := p) hqp hA ↔ ∃ y ∈ kerSocle p q A, (cg hqp hA).symm (reductionModL A p y) = z := by
  constructor
  · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨reductionModL A p y, ⟨y, hy, rfl⟩, rfl⟩

theorem symm_reduction_mem_imageZ (hqp : q ≠ p) (hA : A.LiesOverPrime q) {y : JZero p}
    (hy : y ∈ kerSocle p q A) :
    (cg hqp hA).symm (reductionModL A p y) ∈ imageZ (p := p) hqp hA :=
  (mem_imageZ hqp hA).mpr ⟨y, hy, rfl⟩

theorem imageZ_conditions (hqp : q ≠ p) (hA : A.LiesOverPrime q) (hc : HeckeOperatorsCommuteBar p) :
    (∀ z ∈ imageZ (p := p) hqp hA, (q : ℤ) • z = 0) ∧
    (∀ z ∈ imageZ (p := p) hqp hA, ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ p →
      ((ℓ : ℕ) : IsLocalRing.ResidueField A) ≠ 0 →
      (letI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩;
        heckePic0Fibre (IsLocalRing.ResidueField A) p ℓ z) = (((ℓ : ℕ) + 1 : ℕ) : ℤ) • z) ∧
    (∀ z ∈ imageZ (p := p) hqp hA, heckePic0Fibre (IsLocalRing.ResidueField A) p p z = z) ∧
    (∀ z ∈ imageZ (p := p) hqp hA,
      (haveI := charP_residueField (A := A) hA
       heckeOperatorModL (IsLocalRing.ResidueField A) p q
          (Pic0.congr (IntermediateField.equivOfEq (fieldC_eq (p := p) hqp hA)).toRingEquiv
            (fun a => (IntermediateField.equivOfEq (fieldC_eq (p := p) hqp hA)).commutes a) z)) =
        Pic0.congr (IntermediateField.equivOfEq (fieldC_eq (p := p) hqp hA)).toRingEquiv
          (fun a => (IntermediateField.equivOfEq (fieldC_eq (p := p) hqp hA)).commutes a) z) := by
  haveI := charP_residueField (A := A) hA
  have hinp : ReductionInputsModL A p := reductionInputsModL_of_not_dvd p (not_dvd hqp) A hA
  have hpk := natCast_level_ne_zero (p := p) hqp hA
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := (mem_imageZ hqp hA).mp hz
    rw [← map_zsmul, natCast_smul_reduction_eq_zero hy, map_zero]
  · intro z hz ℓ hℓp hℓk
    obtain ⟨y, hy, rfl⟩ := (mem_imageZ hqp hA).mp hz
    letI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
    haveI : Fact (Nat.Prime (ℓ : ℕ)) := ⟨ℓ.2⟩
    have hℓq : (ℓ : ℕ) ≠ q := by
      rintro h
      rw [h] at hℓk
      exact hℓk (CharP.cast_eq_zero _ q)
    have hf : HeckeInputsFibre (IsLocalRing.ResidueField A) p ℓ :=
      heckeInputsFibre_of_prime (IsLocalRing.ResidueField A) p ℓ hpk hℓk
    have h := reductionModL_heckeOperatorBar_of_ne p (not_dvd hqp) A hA hinp ℓ ℓ.2 hℓq
      (fieldC_eq (p := p) hqp hA) hf y
    simp only [Subtype.coe_eta] at h
    rw [reduction_heckeOperatorBar hc hy ℓ hℓp] at h

    have h' := congrArg (cg (p := p) hqp hA).symm h
    change (cg hqp hA).symm ((((ℓ : ℕ) : ℤ) + 1) • reductionModL A p y) =
      (cg hqp hA).symm ((cg hqp hA) (heckePic0Fibre (IsLocalRing.ResidueField A) p ℓ
        ((cg hqp hA).symm (reductionModL A p y)))) at h'
    rw [AddEquiv.symm_apply_apply, map_zsmul] at h'
    rw [← h']
    congr 1
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := (mem_imageZ hqp hA).mp hz
    have hf : HeckeInputsFibre (IsLocalRing.ResidueField A) p p :=
      heckeInputsFibre_of_prime (IsLocalRing.ResidueField A) p p hpk hpk
    have h := reductionModL_heckeOperatorBar_of_ne p (not_dvd hqp) A hA hinp p (Fact.out)
      (Ne.symm hqp) (fieldC_eq (p := p) hqp hA) hf y
    rw [reduction_heckeOperatorBar_self hc hy] at h
    have h' := congrArg (cg (p := p) hqp hA).symm h
    change (cg hqp hA).symm (reductionModL A p y) =
      (cg hqp hA).symm ((cg hqp hA) (heckePic0Fibre (IsLocalRing.ResidueField A) p p
        ((cg hqp hA).symm (reductionModL A p y)))) at h'
    rw [AddEquiv.symm_apply_apply] at h'
    exact h'.symm
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := (mem_imageZ hqp hA).mp hz
    change heckeOperatorModL (IsLocalRing.ResidueField A) p q
        ((cg hqp hA) ((cg hqp hA).symm (reductionModL A p y))) =
      (cg hqp hA) ((cg hqp hA).symm (reductionModL A p y))
    rw [AddEquiv.apply_symm_apply]
    have h := reductionModL_heckeOperatorBar p (not_dvd hqp) A hA hinp y
    rw [reduction_heckeOperatorBar hc hy ⟨q, Fact.out⟩ hqp] at h
    rw [← h, add_zsmul, one_zsmul]
    change ((q : ℕ) : ℤ) • reductionModL A p y + reductionModL A p y = reductionModL A p y
    rw [natCast_smul_reduction_eq_zero hy, zero_add]

theorem exists_fricke (hqp : q ≠ p) (hA : A.LiesOverPrime q) :
    ∃ τ : modularFunctionFieldC (IsLocalRing.ResidueField A) p ≃ₐ[IsLocalRing.ResidueField A]
        modularFunctionFieldC (IsLocalRing.ResidueField A) p,
      τ ⟨jqModC (IsLocalRing.ResidueField A), jqModC_mem (IsLocalRing.ResidueField A) p⟩ =
          ⟨jqNModC (IsLocalRing.ResidueField A) p, jqNModC_mem (IsLocalRing.ResidueField A) p⟩ ∧
      τ ⟨jqNModC (IsLocalRing.ResidueField A) p, jqNModC_mem (IsLocalRing.ResidueField A) p⟩ =
          ⟨jqModC (IsLocalRing.ResidueField A), jqModC_mem (IsLocalRing.ResidueField A) p⟩ :=
  exists_algEquiv_swap_jqModC_jqNModC_of_finrank_eq_dedekindPsi (IsLocalRing.ResidueField A) p
    (RankOneAsmDeg.finrank_A0_adjoin (IsLocalRing.ResidueField A) p (natCast_level_ne_zero (p := p) hqp hA))

def frickeFull (hqp : q ≠ p) (hA : A.LiesOverPrime q)
    (τ : modularFunctionFieldC (IsLocalRing.ResidueField A) p ≃ₐ[IsLocalRing.ResidueField A]
      modularFunctionFieldC (IsLocalRing.ResidueField A) p) :
    modularFunctionFieldFullC (IsLocalRing.ResidueField A) p ≃ₐ[IsLocalRing.ResidueField A]
      modularFunctionFieldFullC (IsLocalRing.ResidueField A) p :=
  AlgebraicCurve.CongrSmul.conj (IntermediateField.equivOfEq (fieldC_eq (p := p) hqp hA)) τ

theorem frickeFull_apply (hqp : q ≠ p) (hA : A.LiesOverPrime q)
    (τ : modularFunctionFieldC (IsLocalRing.ResidueField A) p ≃ₐ[IsLocalRing.ResidueField A]
      modularFunctionFieldC (IsLocalRing.ResidueField A) p)
    (y : modularFunctionFieldFullC (IsLocalRing.ResidueField A) p) :
    frickeFull (p := p) hqp hA τ y =
      IntermediateField.equivOfEq (fieldC_eq (p := p) hqp hA)
        (τ ((IntermediateField.equivOfEq (fieldC_eq (p := p) hqp hA)).symm y)) := rfl

theorem imageZ_fricke (hqp : q ≠ p) (hA : A.LiesOverPrime q) (hc : HeckeOperatorsCommuteBar p)
    (τ : modularFunctionFieldC (IsLocalRing.ResidueField A) p ≃ₐ[IsLocalRing.ResidueField A]
      modularFunctionFieldC (IsLocalRing.ResidueField A) p)
    (hτ₁ : τ ⟨jqModC (IsLocalRing.ResidueField A), jqModC_mem (IsLocalRing.ResidueField A) p⟩ =
      ⟨jqNModC (IsLocalRing.ResidueField A) p, jqNModC_mem (IsLocalRing.ResidueField A) p⟩)
    (hτ₂ : τ ⟨jqNModC (IsLocalRing.ResidueField A) p, jqNModC_mem (IsLocalRing.ResidueField A) p⟩ =
      ⟨jqModC (IsLocalRing.ResidueField A), jqModC_mem (IsLocalRing.ResidueField A) p⟩) :
    ∀ z ∈ imageZ (p := p) hqp hA, τ • z = -z := by
  haveI := charP_residueField (A := A) hA

  have h1 : frickeFull (p := p) hqp hA τ
      ⟨jqModC (IsLocalRing.ResidueField A), jqModC_mem_full (IsLocalRing.ResidueField A) p⟩ =
      ⟨qExpand (IsLocalRing.ResidueField A) p (jqModC (IsLocalRing.ResidueField A)),
        jqModCd_mem_full (IsLocalRing.ResidueField A) p dvd_rfl⟩ := by
    apply Subtype.ext
    have hs : (IntermediateField.equivOfEq (fieldC_eq (p := p) hqp hA)).symm
        ⟨jqModC (IsLocalRing.ResidueField A), jqModC_mem_full (IsLocalRing.ResidueField A) p⟩ =
        ⟨jqModC (IsLocalRing.ResidueField A), jqModC_mem (IsLocalRing.ResidueField A) p⟩ := Subtype.ext rfl
    rw [frickeFull_apply, hs, hτ₁]
    rfl
  have h2 : frickeFull (p := p) hqp hA τ
      ⟨qExpand (IsLocalRing.ResidueField A) p (jqModC (IsLocalRing.ResidueField A)),
        jqModCd_mem_full (IsLocalRing.ResidueField A) p dvd_rfl⟩ =
      ⟨jqModC (IsLocalRing.ResidueField A), jqModC_mem_full (IsLocalRing.ResidueField A) p⟩ := by
    apply Subtype.ext
    have hs : (IntermediateField.equivOfEq (fieldC_eq (p := p) hqp hA)).symm
        ⟨qExpand (IsLocalRing.ResidueField A) p (jqModC (IsLocalRing.ResidueField A)),
          jqModCd_mem_full (IsLocalRing.ResidueField A) p dvd_rfl⟩ =
        ⟨jqNModC (IsLocalRing.ResidueField A) p, jqNModC_mem (IsLocalRing.ResidueField A) p⟩ := Subtype.ext rfl
    rw [frickeFull_apply, hs, hτ₂]
    rfl
  obtain ⟨-, -, c3, -⟩ := imageZ_conditions (p := p) hqp hA hc
  intro z hz
  have hUz := c3 z hz

  have hM8 := heckePic0Fibre_eq_neg_fricke_smul_of_prime p (not_dvd hqp) A hA (fieldC_eq (p := p) hqp hA)
    (frickeFull (p := p) hqp hA τ) h1 h2 (cg (p := p) hqp hA z)
  have hzz : (Pic0.congr (IntermediateField.equivOfEq (fieldC_eq (p := p) hqp hA)).toRingEquiv
      (fun a => (IntermediateField.equivOfEq (fieldC_eq (p := p) hqp hA)).commutes a)).symm
        (cg (p := p) hqp hA z) = z :=
    AddEquiv.symm_apply_apply (cg (p := p) hqp hA) z
  rw [hzz, hUz] at hM8

  have ht : cg (p := p) hqp hA (τ • z) = frickeFull (p := p) hqp hA τ • cg (p := p) hqp hA z :=
    AlgebraicCurve.CongrSmul.pic0_congr_smul (IntermediateField.equivOfEq (fieldC_eq (p := p) hqp hA)) τ z
  have h4 : cg (p := p) hqp hA z = -(frickeFull (p := p) hqp hA τ • cg (p := p) hqp hA z) := hM8
  apply (cg (p := p) hqp hA).injective
  rw [map_neg, ht]
  exact ((neg_eq_iff_eq_neg).mpr h4).symm

theorem reduction_eq_zero_or_exists (hqp : q ≠ p) (hA : A.LiesOverPrime q)
    (hc : HeckeOperatorsCommuteBar p) {y₁ y₂ : JZero p} (h₁ : y₁ ∈ kerSocle p q A)
    (h₂ : y₂ ∈ kerSocle p q A) :
    reductionModL A p y₁ = 0 ∨ ∃ m : ℕ, reductionModL A p y₂ = m • reductionModL A p y₁ := by
  haveI := charP_residueField (A := A) hA
  haveI : IsAlgClosed (IsLocalRing.ResidueField A) :=
    ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  obtain ⟨c1, c2, c3, c4⟩ := imageZ_conditions (p := p) hqp hA hc
  obtain ⟨τ, hτ₁, hτ₂⟩ := exists_fricke (p := p) hqp hA
  have c5 := imageZ_fricke (p := p) hqp hA hc τ hτ₁ hτ₂
  have key :=
    eq_zero_or_exists_eq_nsmul_of_heckePic0Fibre_eq_eisenstein_of_heckeOperatorModL_eq_of_smul_eq_neg
      (IsLocalRing.ResidueField A) q p (natCast_level_ne_zero (p := p) hqp hA)
      (fieldC_eq (p := p) hqp hA) τ hτ₁ hτ₂ (imageZ (p := p) hqp hA) c1 c2 c3 c5 c4
      _ (symm_reduction_mem_imageZ hqp hA h₁) _ (symm_reduction_mem_imageZ hqp hA h₂)
  rcases key with h0 | ⟨m, hm⟩
  · left
    have := congrArg (cg (p := p) hqp hA) h0
    rwa [AddEquiv.apply_symm_apply, map_zero] at this
  · right
    refine ⟨m, ?_⟩
    have := congrArg (cg (p := p) hqp hA) hm
    rwa [AddEquiv.apply_symm_apply, map_nsmul, AddEquiv.apply_symm_apply] at this

end SpecialFibre

theorem main (q : ℕ) [Fact q.Prime] (hqp : q ≠ p)
    (Aq : ValuationSubring (AlgebraicClosure ℚ)) (hAq : Aq.LiesOverPrime q) (k M : ℕ) :
    ∃ y₀ ∈ heckeTorsion (JZero p)
        (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M),
      (∀ g ∈ eisensteinMaximalIdeal p q, reductionModL Aq p (g • y₀) = 0) ∧
      ∀ y ∈ heckeTorsion (JZero p)
          (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M),
        (∀ g ∈ eisensteinMaximalIdeal p q, reductionModL Aq p (g • y) = 0) →
        ∃ m : ℕ, reductionModL Aq p (y - m • y₀) = 0 := by
  classical
  set T := heckeTorsion (JZero p)
    (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M) with hT
  by_cases hex : ∃ y₀ ∈ T, y₀ ∈ kerSocle p q Aq ∧ reductionModL Aq p y₀ ≠ 0
  · obtain ⟨y₀, hy₀T, hy₀S, hy₀ne⟩ := hex
    refine ⟨y₀, hy₀T, hy₀S, fun y _ hyS => ?_⟩

    have hc : HeckeOperatorsCommuteBar p := by
      by_contra hc
      exact hy₀ne (reduction_eq_zero_of_not hc hy₀S)
    rcases reduction_eq_zero_or_exists (p := p) hqp hAq hc hy₀S hyS with h0 | ⟨m, hm⟩
    · exact absurd h0 hy₀ne
    · exact ⟨m, by rw [map_sub, map_nsmul, hm, sub_self]⟩
  · push Not at hex
    refine ⟨0, Submodule.zero_mem _, fun g _ => by rw [smul_zero, map_zero], fun y hyT hyS => ?_⟩
    exact ⟨0, by rw [zero_nsmul, sub_zero]; exact hex y hyT hyS⟩

end RankOneAsm

end ModularCurve

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_exists_nsmul_generator_heckeTorsion_span_sup_of_reductionModL_eisensteinMaximalIdeal_smul_eq_zero.ModularCurve in
theorem solution
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hqp : q ≠ p)
    (Aq : ValuationSubring (AlgebraicClosure ℚ)) (hAq : Aq.LiesOverPrime q) :
    letI := heckeModuleBar p
    ∀ k M : ℕ,
      ∃ y₀ ∈ heckeTorsion (JZero p)
          (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M),
        (∀ g ∈ eisensteinMaximalIdeal p q, reductionModL Aq p (g • y₀) = 0) ∧
        ∀ y ∈ heckeTorsion (JZero p)
            (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M),
          (∀ g ∈ eisensteinMaximalIdeal p q, reductionModL Aq p (g • y) = 0) →
          ∃ m : ℕ, reductionModL Aq p (y - m • y₀) = 0 :=
  fun k M => ModularCurve.RankOneAsm.main q hqp Aq hAq k M

end S_ModularCurve_exists_nsmul_generator_heckeTorsion_span_sup_of_reductionModL_eisensteinMaximalIdeal_smul_eq_zero
end P2MW
export P2MW.S_ModularCurve_exists_nsmul_generator_heckeTorsion_span_sup_of_reductionModL_eisensteinMaximalIdeal_smul_eq_zero (solution)
