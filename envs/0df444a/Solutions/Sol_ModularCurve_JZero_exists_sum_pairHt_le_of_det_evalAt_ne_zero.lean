-- Prove2me | solution 1 for ModularCurve.JZero.exists_sum_pairHt_le_of_det_evalAt_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/149371db-3afe-5cc6-8350-fad6db682c27

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_ModularCurve_JZero_sum_pairHt_le_of_isUnit_det_jetMatrix
import Theorems.Thm_ModularCurve_JZero_jensen_good_at_le
import Theorems.Thm_ModularCurve_JZero_jensen_arch_at_le_of_nonCuspidal
import Theorems.Thm_ModularCurve_JZero_jensen_bad_at_le
import Theorems.Thm_ModularCurve_JZero_riemannRochSpace_embDivisor_mul_self
import Theorems.Thm_ModularCurve_JZero_riemannRochSpace_embDivisor_mul_eq
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_exists_sum_pairHt_le_of_det_evalAt_ne_zero
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec AlgebraicCurve.chowForm_zero AlgebraicCurve.secProd_zero"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one MvPolynomial.logMahlerMeasure_C MvPolynomial.logMahlerMeasure_X MvPolynomial.logMahlerMeasure_zero MvPolynomial.volume_torusBox MvPolynomial.logMahlerMeasure_monomial MvPolynomial.logMahlerMeasure_one MvPolynomial.norm_circleMap_zero_one MvPolynomial.volume_real_torusBox"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

namespace ConfLedgerAdapter

open AlgebraicCurve ModularCurve

section Split

variable {M : ℕ} (p : Fin M → Prop) [DecidablePred p]

def nP : ℕ := (Finset.univ.filter p).card

theorem nP_le : nP p ≤ M := by
  simpa [nP] using (Finset.univ.filter p).card_le_univ

theorem card_subtype_eq : Fintype.card {i // p i} = nP p := by
  rw [Fintype.card_subtype]; rfl

theorem card_subtype_not_eq : Fintype.card {i // ¬p i} = M - nP p := by
  rw [Fintype.card_subtype_compl, card_subtype_eq, Fintype.card_fin]

noncomputable def splitEquiv : Fin (nP p + (M - nP p)) ≃ Fin M :=
  (finSumFinEquiv.symm.trans
    (Equiv.sumCongr (Fintype.equivFinOfCardEq (card_subtype_eq p)).symm
      (Fintype.equivFinOfCardEq (card_subtype_not_eq p)).symm)).trans
    (Equiv.sumCompl p)

theorem splitEquiv_castAdd (a : Fin (nP p)) :
    splitEquiv p (Fin.castAdd (M - nP p) a)
      = ((Fintype.equivFinOfCardEq (card_subtype_eq p)).symm a : Fin M) := by
  simp [splitEquiv]

theorem splitEquiv_natAdd (a : Fin (M - nP p)) :
    splitEquiv p (Fin.natAdd (nP p) a)
      = ((Fintype.equivFinOfCardEq (card_subtype_not_eq p)).symm a : Fin M) := by
  simp [splitEquiv]

theorem p_splitEquiv_castAdd (a : Fin (nP p)) : p (splitEquiv p (Fin.castAdd (M - nP p) a)) := by
  rw [splitEquiv_castAdd]; exact ((Fintype.equivFinOfCardEq (card_subtype_eq p)).symm a).2

theorem not_p_splitEquiv_natAdd (a : Fin (M - nP p)) : ¬p (splitEquiv p (Fin.natAdd (nP p) a)) := by
  rw [splitEquiv_natAdd]; exact ((Fintype.equivFinOfCardEq (card_subtype_not_eq p)).symm a).2

theorem sum_filter_eq_sum_castAdd {β : Type*} [AddCommMonoid β] (g : Fin M → β) :
    ∑ i ∈ Finset.univ.filter p, g i = ∑ a : Fin (nP p), g (splitEquiv p (Fin.castAdd (M - nP p) a)) := by
  rw [Finset.sum_subtype (Finset.univ.filter p) (p := p) (by simp)]
  rw [← Equiv.sum_comp (Fintype.equivFinOfCardEq (card_subtype_eq p)).symm]
  exact Finset.sum_congr rfl fun a _ => by rw [splitEquiv_castAdd]

theorem sum_filter_not_eq_sum_natAdd {β : Type*} [AddCommMonoid β] (g : Fin M → β) :
    ∑ i ∈ Finset.univ.filter (fun i => ¬p i), g i
      = ∑ a : Fin (M - nP p), g (splitEquiv p (Fin.natAdd (nP p) a)) := by
  rw [Finset.sum_subtype (Finset.univ.filter fun i => ¬p i) (p := fun i => ¬p i) (by simp)]
  rw [← Equiv.sum_comp (Fintype.equivFinOfCardEq (card_subtype_not_eq p)).symm]
  exact Finset.sum_congr rfl fun a _ => by rw [splitEquiv_natAdd]

end Split

section Det

variable {K : Type*} [Field K] [CharZero K] {M n : ℕ}

theorem det_submatrix_equiv_ne_zero (A : Matrix (Fin M) (Fin M) K)
    (e₁ e₂ : Fin n ≃ Fin M) (hA : A.det ≠ 0) : (A.submatrix e₁ e₂).det ≠ 0 := by
  have h : A.submatrix e₁ e₂ = (A.submatrix e₁ e₁).submatrix id (e₂.trans e₁.symm) := by
    ext i j; simp
  rw [h, Matrix.det_permute', Matrix.det_submatrix_equiv_self]
  refine mul_ne_zero ?_ hA
  rcases Int.units_eq_one_or (Equiv.Perm.sign (e₂.trans e₁.symm)) with h1 | h1 <;> simp [h1]

end Det

section LevelN

variable {K F : Type*} [Field K] [Field F] [Algebra K F] in
theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf0 : f ≠ 0) (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  have h1 : v.adicValuation f ≤ 1 := by
    have := v.adicValuation_coe ⟨f, hf⟩
    rw [show ((⟨f, hf⟩ : v.toValuationSubring) : F) = f from rfl] at this
    rw [this]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  have hne := v.adicValuation_ne_zero hf0
  have h2 : WithZero.exp (WithZero.log (v.adicValuation f)) ≤ WithZero.exp 0 := by
    rw [WithZero.exp_log hne, WithZero.exp_zero]; exact h1
  rw [WithZero.exp_le_exp] at h2
  show 0 ≤ -(WithZero.log (v.adicValuation f))
  omega

variable {K F : Type*} [Field K] [Field F] [Algebra K F] in
theorem evalAt_add_of_mem (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

variable {K F : Type*} [Field K] [Field F] [Algebra K F] in
theorem ord_pos_of_evalAt_eq_zero (v : Place K F) (hv : v.IsRational) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ v.toValuationSubring) (h : v.evalAt f = 0) : 0 < v.ord f := by
  rcases (ord_nonneg_of_mem v hf0 hf).lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd h (v.evalAt_ne_zero_of_ord_eq_zero hv hf0 heq.symm)

variable (N : ℕ) [NeZero N]

theorem isRational_bar (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : v.IsRational :=
  (Place.isRational_iff_deg_eq_one v).mpr (ModularCurve.deg_eq_one_modularFunctionFieldBar N v)

theorem embDivisor_apply_of_ne {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hv : v ≠ cuspInftyBar N) : embDivisor N v = 0 := by
  classical
  simp [embDivisor, Finsupp.single_apply, Ne.symm hv]

theorem mem_toValuationSubring_of_mem_riemannRochSpace
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} {f : modularFunctionFieldBar N}
    (hf : f ∈ riemannRochSpace D) {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hD : D v = 0) : f ∈ v.toValuationSubring := by
  by_cases hf0 : f = 0
  · rw [hf0]; exact zero_mem _
  rcases (mem_riemannRochSpace_iff.mp hf) v with h0 | h
  · exact absurd h0 hf0
  · rw [hD, neg_zero] at h
    exact v.mem_toValuationSubring_of_ord_nonneg_alt hf0 h

theorem exists_eq_algebraMap_of_mem_riemannRochSpace_zero {f : modularFunctionFieldBar N}
    (hf : f ∈ riemannRochSpace (0 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))) :
    ∃ a : AlgebraicClosure ℚ, f = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a := by
  classical
  by_cases hf0 : f = 0
  · exact ⟨0, by rw [hf0, map_zero]⟩
  have hreg : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), f ∈ v.toValuationSubring :=
    fun v => mem_toValuationSubring_of_mem_riemannRochSpace N hf (Finsupp.zero_apply)
  set v₀ := cuspInftyBar N with hv₀
  set a := v₀.evalAt f with ha
  refine ⟨a, ?_⟩
  by_contra hne
  set w := f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a with hw
  have hw0 : w ≠ 0 := sub_ne_zero.mpr hne
  have hwreg : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w ∈ v.toValuationSubring :=
    fun v => sub_mem (hreg v) (v.algebraMap_mem' a)
  have hw_eval : v₀.evalAt w = 0 := by
    rw [hw, sub_eq_add_neg, ← map_neg, evalAt_add_of_mem v₀ (isRational_bar N v₀) (hreg v₀) (v₀.algebraMap_mem' _),
      v₀.evalAt_algebraMap_eq, ha, add_neg_cancel]
  have hpos : 0 < v₀.ord w := ord_pos_of_evalAt_eq_zero v₀ (isRational_bar N v₀) hw0 (hwreg v₀) hw_eval
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  obtain ⟨D, hD, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) w hw0
  have hDnn : ∀ v, 0 ≤ D v := fun v => by rw [hD v]; exact ord_nonneg_of_mem v hw0 (hwreg v)
  have hdeg' : Divisor.degree D = ∑ v ∈ D.support, D v := by
    simp only [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum, AddMonoidHom.mulRight_apply,
      ModularCurve.deg_eq_one_modularFunctionFieldBar N, Nat.cast_one, mul_one]
  have hv₀supp : v₀ ∈ D.support := by
    rw [Finsupp.mem_support_iff, hD v₀]; exact ne_of_gt hpos
  have hlt : 0 < Divisor.degree D := by
    rw [hdeg']
    have h1 : D v₀ ≤ ∑ v ∈ D.support, D v :=
      Finset.single_le_sum (f := fun v => D v) (fun v _ => hDnn v) hv₀supp
    have h2 : 0 < D v₀ := by rw [hD v₀]; exact hpos
    exact lt_of_lt_of_le h2 h1
  rw [hdeg] at hlt
  exact lt_irrefl _ hlt

variable {N}

open scoped Pointwise

noncomputable def monomial {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (k : ℕ) (φ : Fin k → Fin r) :
    modularFunctionFieldBar N := ∏ l, s (φ l)

theorem range_s_mul_range_monomial {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (k : ℕ) :
    Set.range s * Set.range (monomial s k) = Set.range (monomial s (k + 1)) := by
  ext x
  simp only [Set.mem_mul, Set.mem_range, monomial]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, _, ⟨φ, rfl⟩, rfl⟩
    exact ⟨Fin.cons i φ, by simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]⟩
  · rintro ⟨ψ, rfl⟩
    exact ⟨s (ψ 0), ⟨ψ 0, rfl⟩, ∏ l, s (Fin.tail ψ l), ⟨Fin.tail ψ, rfl⟩, by rw [Fin.prod_univ_succ]; rfl⟩

theorem riemannRochSpace_smul_eq_span_monomial {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (hs : IsEmbBasis N s) (k : ℕ) (hk : 1 ≤ k) :
    riemannRochSpace ((k : ℤ) • embDivisor N)
      = Submodule.span (AlgebraicClosure ℚ) (Set.range (monomial s k)) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 1 with hk0 | hk1
    ·
      have hk0' : k = 0 := by omega
      subst hk0'
      have h1 : (((0 + 1 : ℕ) : ℤ) • embDivisor N) = embDivisor N := by simp
      rw [h1, ← hs.2]
      congr 1
      ext x
      simp only [Set.mem_range, monomial, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨fun _ => i, rfl⟩
      · rintro ⟨φ, rfl⟩; exact ⟨φ 0, rfl⟩
    · have hmul : riemannRochSpace (embDivisor N) * riemannRochSpace ((k : ℤ) • embDivisor N)
          = riemannRochSpace (((k + 1 : ℕ) : ℤ) • embDivisor N) := by
        rcases Nat.lt_or_ge k 2 with hk2 | hk2
        · have hk1' : k = 1 := by omega
          subst hk1'
          have := ModularCurve.JZero.riemannRochSpace_embDivisor_mul_self N
          simpa using this
        · have := ModularCurve.JZero.riemannRochSpace_embDivisor_mul_eq N k hk2
          push_cast at this ⊢
          exact this
      rw [← hmul, ih hk1, ← hs.2, Submodule.span_mul_span, range_s_mul_range_monomial]

theorem exists_presentation {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (k : ℕ) (u : modularFunctionFieldBar N) (hu : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N)) :
    ∃ c : (Fin k → Fin r) → AlgebraicClosure ℚ, u = ∑ φ : Fin k → Fin r, c φ • ∏ l, s (φ l) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hu' : u ∈ riemannRochSpace (0 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) := by
      simpa using hu
    obtain ⟨a, ha⟩ := exists_eq_algebraMap_of_mem_riemannRochSpace_zero N hu'
    refine ⟨fun _ => a, ?_⟩
    rw [Fintype.sum_unique]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, ha, Algebra.algebraMap_eq_smul_one]
  · have hmem : u ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range (monomial s k)) := by
      rw [← riemannRochSpace_smul_eq_span_monomial s hs k hk]; exact hu
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (AlgebraicClosure ℚ)).mp hmem
    exact ⟨c, by rw [← hc]; rfl⟩

end LevelN

end ConfLedgerAdapter

open AlgebraicCurve ModularCurve ConfLedgerAdapter

open Classical in

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (k M : ℕ)
    (u : Fin M → modularFunctionFieldBar N) (hu0 : ∀ j, u j ≠ 0)
    (hu : ∀ j, u j ∈ riemannRochSpace ((k : ℤ) • embDivisor N))
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hB : 0 ≤ B)
    (hBu : ∀ j w, B w ≤ w.ord (u j) + ((k : ℤ) • embDivisor N) w)
    (F : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))
    (hF : ∀ v, v ∉ F → v ≠ cuspInftyBar N →
      (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) ∈ v.toValuationSubring) :
    ∃ C : ℝ, ∀ R : Fin M → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      Function.Injective R → (∀ i, R i ≠ cuspInftyBar N) → (∀ i, B (R i) = 0) →
      (Matrix.of fun i j => (R i).evalAt (u j)).det ≠ 0 →
      (∑ i ∈ Finset.univ.filter (fun i => R i ∉ F),
          ∑ i' ∈ (Finset.univ.filter (fun i => R i ∉ F)).erase i, pairHt s (R i) (R i')) / 2
        + ∑ i ∈ Finset.univ.filter (fun i => R i ∉ F),
            ∑ i' ∈ Finset.univ.filter (fun i => R i ∈ F), pairHt s (R i) (R i')
        + ∑ i ∈ Finset.univ.filter (fun i => R i ∉ F), B.sum (fun w n => (n : ℝ) * pairHt s (R i) w)
        ≤ (k : ℝ) * ∑ i ∈ Finset.univ.filter (fun i => R i ∉ F), pointHt s (R i) + C := by
  classical

  have hJgood := ModularCurve.JZero.jensen_good_at_le N s hs
  have hJarch := ModularCurve.JZero.jensen_arch_at_le_of_nonCuspidal N s hs

  choose c₀ hc₀ using fun j => exists_presentation s hs k (u j) (hu j)

  have hκ : ∀ m : Fin (M + 1), (m : ℕ) + (M - m) = M := fun m => Nat.add_sub_of_le (Nat.lt_succ_iff.mp m.2)
  let κ : ∀ m : Fin (M + 1), Fin (m + (M - m)) ≃ Fin M := fun m => finCongr (hκ m)
  let Hf : Fin (M + 1) → ℝ := fun m =>
    absLogHeight (fun q : Fin (m + (M - m)) × (Fin k → Fin r) => c₀ (κ m q.1) q.2)

  choose Cf hCf using fun m : Fin (M + 1) =>
    ModularCurve.JZero.sum_pairHt_le_of_isUnit_det_jetMatrix N s hs k m (M - m) hJgood
      (fun S₀ => ModularCurve.JZero.jensen_bad_at_le N s hs S₀) hJarch (Hf m)

  let hrow : Fin (M + 1) → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → ℝ := fun m v =>
    absLogHeight (fun j : Fin (m + (M - m)) => v.evalAt (u (κ m j)))
  let Cfix : Fin (M + 1) → ℝ := fun m => ∑ v ∈ F, |hrow m v|
  refine ⟨∑ m : Fin (M + 1), (|Cf m| + Cfix m), ?_⟩
  intro R hRinj hRoo hRB hdetA

  set p : Fin M → Prop := fun i => R i ∉ F with hp
  set m : ℕ := nP p with hmdef
  have hmM : m ≤ M := nP_le p
  let m₀ : Fin (M + 1) := ⟨m, Nat.lt_succ_of_le hmM⟩

  let e : Fin (m + (M - m)) ≃ Fin M := splitEquiv p
  let Rm : Fin m → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := fun a => R (e (Fin.castAdd (M - m) a))
  let Rf : Fin (M - m) → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := fun a => R (e (Fin.natAdd m a))
  have hRm : ∀ a, Rm a ∉ F := fun a => p_splitEquiv_castAdd p a
  have hRf : ∀ a, Rf a ∈ F := fun a => not_not.mp (not_p_splitEquiv_natAdd p a)
  have hRe_inj : Function.Injective (fun i => R (e i)) := hRinj.comp e.injective
  have hRm_inj : Function.Injective Rm := fun a a' h =>
    Fin.castAdd_injective _ _ (e.injective (hRinj h))
  have happR : Fin.append Rm Rf = fun i => R (e i) := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · rw [Fin.append_left]
    · rw [Fin.append_right]
  have happ_t : Fin.append (fun _ : Fin m => (0 : modularFunctionFieldBar N)) (fun _ : Fin (M - m) => 0)
      = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · rw [Fin.append_left]
    · rw [Fin.append_right]
  have happ_e : Fin.append (fun _ : Fin m => (0 : ℕ)) (fun _ : Fin (M - m) => 0) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · rw [Fin.append_left]
    · rw [Fin.append_right]

  let u' : Fin (m + (M - m)) → modularFunctionFieldBar N := fun j => u (κ m₀ j)
  have hu'0 : ∀ j, u' j ≠ 0 := fun j => hu0 _
  have hu'pres : ∀ j, u' j = ∑ φ : Fin k → Fin r, c₀ (κ m₀ j) φ • ∏ l, s (φ l) := fun j => hc₀ _
  have hBnn : ∀ w, 0 ≤ B w := fun w => by simpa using (Finsupp.le_def.mp hB) w
  have hBu' : ∀ j w, B w ≤ w.ord (u' j) + ((k : ℤ) • embDivisor N) w := fun j w => hBu _ w

  have hconf : IsConfluentPattern (Fin.append Rm Rf)
      (Fin.append (fun _ : Fin m => (0 : modularFunctionFieldBar N)) (fun _ : Fin (M - m) => 0))
      (Fin.append (fun _ : Fin m => (0 : ℕ)) (fun _ : Fin (M - m) => 0)) := by
    rw [happR, happ_t, happ_e]
    refine ⟨fun _ _ _ => rfl, fun i i' h _ => hRe_inj h, fun i => ?_⟩
    show 0 < jetMult (fun i => R (e i)) (R (e i))
    unfold jetMult
    exact Finset.card_pos.mpr ⟨i, by simp⟩
  have hdisj : ∀ a a', Rm a ≠ Rf a' := fun a a' h => hRm a (h ▸ hRf a')
  have hRmoo : ∀ a, Rm a ≠ cuspInftyBar N := fun a => hRoo _
  have hRfoo : ∀ a, Rf a ≠ cuspInftyBar N := fun a => hRoo _
  have hadm : ∀ a, (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) ∈ (Rm a).toValuationSubring := fun a => hF _ (hRm a) (hRmoo a)
  have hRmB : ∀ a, B (Rm a) = 0 := fun a => hRB _
  have hRfB : ∀ a, B (Rf a) = 0 := fun a => hRB _
  have hord : ∀ a : Fin m, 0 < (0 : ℕ) → (Rm a).ord (0 : modularFunctionFieldBar N) = 1 :=
    fun a h => absurd h (lt_irrefl 0)
  have hord' : ∀ a : Fin (M - m), 0 < (0 : ℕ) → (Rf a).ord (0 : modularFunctionFieldBar N) = 1 :=
    fun a h => absurd h (lt_irrefl 0)
  have hjet : jetMatrix (Fin.append Rm Rf)
      (Fin.append (fun _ : Fin m => (0 : modularFunctionFieldBar N)) (fun _ : Fin (M - m) => 0))
      (Fin.append (fun _ : Fin m => (0 : ℕ)) (fun _ : Fin (M - m) => 0)) u'
      = (Matrix.of fun i j => (R i).evalAt (u j)).submatrix e (κ m₀) := by
    rw [happ_e, jetMatrix_order_zero, happR]
    rfl
  have hunit : IsUnit (jetMatrix (Fin.append Rm Rf)
      (Fin.append (fun _ : Fin m => (0 : modularFunctionFieldBar N)) (fun _ : Fin (M - m) => 0))
      (Fin.append (fun _ : Fin m => (0 : ℕ)) (fun _ : Fin (M - m) => 0)) u').det := by
    rw [hjet]
    exact isUnit_iff_ne_zero.mpr (det_submatrix_equiv_ne_zero _ e (κ m₀) hdetA)

  have key := hCf m₀ u' (fun j => c₀ (κ m₀ j)) hu'0 hu'pres le_rfl B hBnn hBu' Rm (fun _ => 0) (fun _ => 0)
    Rf (fun _ => 0) (fun _ => 0) hconf hdisj hRmoo hRfoo hadm hRmB hRfB hord hord' hunit
  simp only [Nat.cast_zero, mul_zero, sub_zero, zero_mul, add_zero, Place.taylorCoeff_zero] at key

  have hinF : ∀ g : Fin M → ℝ, ∑ i' ∈ Finset.univ.filter (fun i => R i ∈ F), g i'
      = ∑ a' : Fin (M - m), g (e (Fin.natAdd m a')) := by
    intro g
    rw [show Finset.univ.filter (fun i => R i ∈ F) = Finset.univ.filter (fun i => ¬p i) from
      Finset.filter_congr (fun i _ => by rw [hp]; exact not_not.symm)]
    exact sum_filter_not_eq_sum_natAdd p g
  have hR1 : ∑ i ∈ Finset.univ.filter p, pointHt s (R i) = ∑ a : Fin m, pointHt s (Rm a) :=
    sum_filter_eq_sum_castAdd p _
  have hL3 : ∑ i ∈ Finset.univ.filter p, B.sum (fun w n => (n : ℝ) * pairHt s (R i) w)
      = ∑ a : Fin m, B.sum (fun w n => (n : ℝ) * pairHt s (Rm a) w) :=
    sum_filter_eq_sum_castAdd p _
  have hL2 : ∑ i ∈ Finset.univ.filter p, ∑ i' ∈ Finset.univ.filter (fun i => R i ∈ F), pairHt s (R i) (R i')
      = ∑ a : Fin m, ∑ a' : Fin (M - m), pairHt s (Rm a) (Rf a') := by
    rw [sum_filter_eq_sum_castAdd p]
    exact Finset.sum_congr rfl fun a _ => hinF _
  have hL1 : ∑ i ∈ Finset.univ.filter p, ∑ i' ∈ (Finset.univ.filter p).erase i, pairHt s (R i) (R i')
      = ∑ a : Fin m, ∑ a' ∈ Finset.univ.filter (fun a' : Fin m => Rm a' ≠ Rm a), pairHt s (Rm a) (Rm a') := by
    rw [sum_filter_eq_sum_castAdd p]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hmem : e (Fin.castAdd (M - m) a) ∈ Finset.univ.filter p :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, p_splitEquiv_castAdd p a⟩
    rw [Finset.sum_erase_eq_sub hmem, sum_filter_eq_sum_castAdd p]
    have hfilt : Finset.univ.filter (fun a' : Fin m => Rm a' ≠ Rm a) = Finset.univ.erase a := by
      ext a'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true, ne_eq,
        hRm_inj.eq_iff]
    rw [hfilt, Finset.sum_erase_eq_sub (Finset.mem_univ a)]

  have hfixle : ∑ a' : Fin (M - m), absLogHeight (fun j : Fin (m + (M - m)) => (Rf a').evalAt (u' j))
      ≤ Cfix m₀ := by
    calc ∑ a' : Fin (M - m), hrow m₀ (Rf a')
        ≤ ∑ a' : Fin (M - m), |hrow m₀ (Rf a')| := Finset.sum_le_sum fun a' _ => le_abs_self _
      _ = ∑ i' ∈ Finset.univ.filter (fun i => R i ∈ F), |hrow m₀ (R i')| :=
          (hinF (fun i => |hrow m₀ (R i)|)).symm
      _ = ∑ v ∈ (Finset.univ.filter (fun i => R i ∈ F)).image R, |hrow m₀ v| := by
          rw [Finset.sum_image (fun i _ i' _ h => hRinj h)]
      _ ≤ ∑ v ∈ F, |hrow m₀ v| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro v hv
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
            exact (Finset.mem_filter.mp hi).2
          · exact fun v _ _ => abs_nonneg _

  have hC : Cf m₀ + Cfix m₀ ≤ ∑ m : Fin (M + 1), (|Cf m| + Cfix m) := by
    have h1 : |Cf m₀| + Cfix m₀ ≤ ∑ m : Fin (M + 1), (|Cf m| + Cfix m) :=
      Finset.single_le_sum (f := fun m => |Cf m| + Cfix m)
        (fun m _ => add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun v _ => abs_nonneg _)) (Finset.mem_univ m₀)
    linarith [le_abs_self (Cf m₀)]

  rw [hL1, hL2, hL3, hR1, Finset.mul_sum]
  linarith [key, hfixle, hC]

end S_ModularCurve_JZero_exists_sum_pairHt_le_of_det_evalAt_ne_zero
end P2MW
export P2MW.S_ModularCurve_JZero_exists_sum_pairHt_le_of_det_evalAt_ne_zero (solution)
