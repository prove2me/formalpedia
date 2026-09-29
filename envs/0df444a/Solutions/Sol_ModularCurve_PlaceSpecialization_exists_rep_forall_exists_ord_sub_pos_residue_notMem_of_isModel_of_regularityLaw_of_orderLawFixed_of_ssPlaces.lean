-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_rep_forall_exists_ord_sub_pos_residue_notMem_of_isModel_of_regularityLaw_of_orderLawFixed_of_ssPlaces
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/720199b7-76bc-5cad-a1f0-7d728bfd2790

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isInftySide_or_isZeroSide_of_isCuspidal
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isInftySide_of_isZeroSide
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceSnd_eq_frobOnPlacesGeomLevel_reduceFst_of_isInftySide
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_reduceFst_of_regularityLaw
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_reduceSnd_of_regularityLaw
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_of_reduceFst_fixed_ordinary_of_regularityLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_rep_forall_exists_ord_sub_pos_residue_notMem_of_isModel_of_regularityLaw_of_orderLawFixed_of_ssPlaces
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.numberField_of_finiteDimensional"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.symPoly_zero ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false
set_option autoImplicit false
p2m_open "AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~jFun~IsCuspidal~IsZeroSide~IsCuspidal'"

private noncomputable abbrev algebraFullCShortcut (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    Algebra K ↥(modularFunctionFieldFullC K N) := inferInstance

example (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    algebraFullCShortcut K N = (inferInstance : Algebra K ↥(modularFunctionFieldFullC K N)) := rfl

private noncomputable abbrev algebraCShortcut (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    Algebra K ↥(modularFunctionFieldC K N) := inferInstance

example (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    algebraCShortcut K N = (inferInstance : Algebra K ↥(modularFunctionFieldC K N)) := rfl

private noncomputable abbrev algebraBarShortcut (M : ℕ) [NeZero M] :
    Algebra (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M) := inferInstance

example (M : ℕ) [NeZero M] :
    algebraBarShortcut M
      = (inferInstance : Algebra (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M)) := rfl

private theorem hasPrincipalDivisorsBarShortcut (M : ℕ) [NeZero M] :
    HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M) :=
  ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional M

attribute [local instance high] algebraFullCShortcut algebraCShortcut algebraBarShortcut
  hasPrincipalDivisorsBarShortcut

private theorem ne_zero_of_ord_pos {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (h : 0 < v.ord f) : f ≠ 0 := by
  rintro rfl
  rw [Place.ord_zero] at h
  exact lt_irrefl 0 h

private theorem ramificationIndexAlong_pos {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') : 0 < Place.ramificationIndexAlong φ w := by
  unfold Place.ramificationIndexAlong
  letI := algebraAlong φ
  haveI := isIntegral_along φ hφ
  exact w.ramificationIndex_pos (F := F)

private theorem sep_ord_pos_gen {N : ℕ} [NeZero N] {A : ValuationSubring (AlgebraicClosure ℚ)}
    (v : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))
    (g : modularFunctionFieldC (ResidueField A) N) {c₁ c₂ : ResidueField A}
    (h₁ : 0 < v.ord (g - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c₁))
    (h₂ : 0 < v.ord (g - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c₂)) : c₁ = c₂ := by
  by_contra hne
  have hsub : (g - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c₂)
      - (g - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c₁)
      = algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) (c₁ - c₂) := by
    rw [map_sub]
    ring
  have hv₁ : v.adicValuation (g - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c₁) < 1 := by
    rw [v.adicValuation_eq_exp_neg_ord (ne_zero_of_ord_pos v h₁), ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hv₂ : v.adicValuation (g - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c₂) < 1 := by
    rw [v.adicValuation_eq_exp_neg_ord (ne_zero_of_ord_pos v h₂), ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hval : v.adicValuation (algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) (c₁ - c₂)) < 1 := by
    rw [← hsub]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hv₂ hv₁)
  have hord0 : v.ord (algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) (c₁ - c₂)) = 0 :=
    ConstantReduction.ord_algebraMap v (sub_ne_zero.mpr hne)
  rw [v.adicValuation_eq_exp_neg_ord ((map_ne_zero _).mpr (sub_ne_zero.mpr hne)), hord0] at hval
  simp at hval

open Classical in
private noncomputable def valOf {N : ℕ} [NeZero N] {A : ValuationSubring (AlgebraicClosure ℚ)}
    (g : modularFunctionFieldC (ResidueField A) N)
    (t : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)) : ResidueField A :=
  if h : ∃ c, 0 < t.ord (g - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c) then h.choose else 0

private theorem valOf_eq {N : ℕ} [NeZero N] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {g : modularFunctionFieldC (ResidueField A) N}
    {t : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)}
    {c : ResidueField A}
    (h : 0 < t.ord (g - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c)) : valOf g t = c := by
  have hex : ∃ c', 0 < t.ord (g - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c') := ⟨c, h⟩
  unfold valOf
  rw [dif_pos hex]
  exact sep_ord_pos_gen t g hex.choose_spec h

private theorem mapDomain_pos_of_mem_fiber {σ τ : Type*}
    (g : σ → τ) (D : σ →₀ ℤ) (t : τ) (V : σ)
    (hgV : g V = t) (hpos : 0 < D V)
    (hnn : ∀ V', g V' = t → 0 ≤ D V') :
    0 < Finsupp.mapDomain g D t := by
  classical
  have happ : Finsupp.mapDomain g D t = ∑ a ∈ D.support, if g a = t then D a else 0 := by
    simp [Finsupp.mapDomain, Finsupp.sum, Finsupp.single_apply]
  rw [happ]
  have hVmem : V ∈ D.support := Finsupp.mem_support_iff.mpr (by omega)
  refine Finset.sum_pos' ?_ ⟨V, hVmem, ?_⟩
  · intro a _
    by_cases hga : g a = t
    · simpa [hga] using hnn a hga
    · simp [hga]
  · simpa [hgV] using hpos

private theorem iota_algebraMap
    {N q : ℕ} [NeZero N] [NeZero q] [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [CharP (ResidueField A) q]
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (R : ProlongationTuple P) (c : A) :
    R.ι (algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N)
        (IsLocalRing.residue A c))
      = algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
          (IsLocalRing.residue A c) := by
  refine Subtype.ext ?_
  rw [R.ι_coe]

  show coeffMap R.redBar
      ((algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N)
          (IsLocalRing.residue A c) : modularFunctionFieldFullC (ResidueField A) N) :
        LaurentSeries (ResidueField A))
    = ((algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
          (IsLocalRing.residue A c) : modularFunctionFieldC (ResidueField A) N) :
        LaurentSeries (ResidueField A))

  have hLHScoe : ((algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N)
          (IsLocalRing.residue A c) : modularFunctionFieldFullC (ResidueField A) N) :
        LaurentSeries (ResidueField A))
      = algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue A c) :=
    rfl
  have hRHScoe : ((algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
          (IsLocalRing.residue A c) : modularFunctionFieldC (ResidueField A) N) :
        LaurentSeries (ResidueField A))
      = algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue A c) :=
    rfl
  rw [hLHScoe, hRHScoe, algebraMap_laurentSeries_eq_single, coeffMap_single, R.redBar_residue]

private theorem constant_commonUnit
    {N q : ℕ} [NeZero N] [NeZero q] [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [CharP (ResidueField A) q]
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (R : ProlongationTuple P) (c : A) :
    ∃ (h₁ : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
        (c : AlgebraicClosure ℚ) ∈ R.R₁.integers)
      (h₂ : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
        (c : AlgebraicClosure ℚ) ∈ R.R₂.integers),
      R.residue₁ ⟨_, h₁⟩
          = algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
              (IsLocalRing.residue A c) ∧
        R.residue₂ ⟨_, h₂⟩
          = algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
              (IsLocalRing.residue A c) := by

  have h₁ : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
      (c : AlgebraicClosure ℚ) ∈ R.R₁.integers :=
    (R.R₁.algebraMap_mem_iff (c : AlgebraicClosure ℚ)).mpr c.2

  have hAL : ProlongationTuple.atkinLehnerBar N q
      (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ))
    = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) :=
    (ProlongationTuple.atkinLehnerBar N q).commutes (c : AlgebraicClosure ℚ)
  have h₂ : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
      (c : AlgebraicClosure ℚ) ∈ R.R₂.integers := by
    rw [R.mem_integers₂_iff, hAL]; exact h₁
  refine ⟨h₁, h₂, ?_, ?_⟩
  ·
    rw [R.residue₁_apply]
    have hR₁ : R.R₁.residue ⟨_, h₁⟩
        = algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N)
            (IsLocalRing.residue A c) := by
      have := R.R₁.residue_algebraMap c
      convert this using 2
    rw [hR₁]
    exact iota_algebraMap P R c
  ·
    rw [R.residue₂_apply, R.residue₂_eq _ h₂]
    have hR₁' : R.R₁.residue ⟨ProlongationTuple.atkinLehnerBar N q
          (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ)),
        (R.mem_integersFst_iff _).mpr ((R.mem_integersSnd_iff _).mp h₂)⟩
        = algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N)
            (IsLocalRing.residue A c) := by
      have := R.R₁.residue_algebraMap c
      refine (congrArg R.R₁.residue (Subtype.ext ?_)).trans this
      exact hAL
    rw [hR₁']
    exact iota_algebraMap P R c

private theorem goodJ_of_reduceFst_affine_goodVal
    (N q : ℕ) [NeZero N] (hq : q.Prime) (_hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (S : Finset (ResidueField A))
      (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      ¬ (P.reduceFst V).ord
          (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩
            : modularFunctionFieldC (ResidueField A) N) < 0 →
      (∀ s ∈ S, ¬ 0 < (P.reduceFst V).ord
          (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩
            - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) s)) →
      ∃ a : A,
        0 < V.ord
            (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                  (modularFunctionField_le_full (N * q) (jq_mem (N * q)))⟩
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
                  (a : AlgebraicClosure ℚ)) ∧
          IsLocalRing.residue A a ∉ S := by
  intro data hKr hα hβ P S V hnopole hnoval
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  by_cases hex : ∃ a : A,
      0 < V.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (N * q) (jq_mem (N * q)))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
                (a : AlgebraicClosure ℚ))
  · obtain ⟨a, ha⟩ := hex
    refine ⟨a, ha, fun hmem => ?_⟩
    have htrans : heckeAlphaBar (AlgebraicClosure ℚ) N q
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
        = (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full (N * q) (jq_mem (N * q)))⟩ : modularFunctionFieldBar (N * q))
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) := by
      rw [map_sub]
      congr 1
    have hord := Place.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V
      ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
    rw [htrans] at hord
    rw [hord] at ha
    have hre : 0 < (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) := by
      by_contra hle
      push Not at hle
      have h0 : (Place.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) V : ℤ) *
          (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord
            ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
          ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hle
      omega
    exact hnoval (IsLocalRing.residue A a) hmem (P.d0_j _ a hre)
  ·
    push Not at hex
    refine absurd ?_ hnopole
    refine P.d0_j_pole (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) (fun a => ?_)
    by_contra hlt
    push Not at hlt
    have hpos' : 0 < (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) := hlt
    have htrans : heckeAlphaBar (AlgebraicClosure ℚ) N q
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
        = (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full (N * q) (jq_mem (N * q)))⟩ : modularFunctionFieldBar (N * q))
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) := by
      rw [map_sub]
      congr 1
    have hord := Place.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V
      ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
    rw [htrans] at hord
    have hup : 0 < V.ord
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full (N * q) (jq_mem (N * q)))⟩ : modularFunctionFieldBar (N * q))
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) := by
      rw [hord]
      exact mul_pos
        (Int.natCast_pos.mpr (ramificationIndexAlong_pos (heckeAlphaBar (AlgebraicClosure ℚ) N q)
          hα V))
        hpos'
    exact absurd hup (not_lt.mpr (hex a))

private theorem ord_nonneg_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F]
    {w : Place K F} {f : F} (hf : f ∈ w.toValuationSubring) : 0 ≤ w.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp [Place.ord_zero]
  · by_contra hneg
    push Not at hneg
    haveI : IsDiscreteValuationRing w.toValuationSubring := by
      refine ⟨?_⟩
      intro hbot
      exact ValuationSubring.not_isField_of_ne_top (F := F) (A := w.toValuationSubring) w.ne_top'
        (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot)
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
    obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf0 hπ
    have hπF : (π : F) ≠ 0 := by
      simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
    set m : ℕ := (-(w.ord f)).toNat with hm_def
    have hmZ : (m : ℤ) = -(w.ord f) := by
      rw [hm_def]
      exact Int.toNat_of_nonneg (by omega)
    have hm1 : m ≠ 0 := by omega

    have hfm : (π : F) ^ m * f = ((u : w.toValuationSubring) : F) := by
      rw [hu, mul_comm ((u : w.toValuationSubring) : F) _, ← mul_assoc,
        ← zpow_natCast ((π : F)) m, ← zpow_add₀ hπF, hmZ]
      simp

    have hO : (π ^ m) * (⟨f, hf⟩ : w.toValuationSubring) = (u : w.toValuationSubring) := by
      ext
      push_cast
      exact hfm
    have hdvd : π ∣ (u : w.toValuationSubring) := by
      refine dvd_trans (dvd_pow_self π hm1) ⟨⟨f, hf⟩, hO.symm⟩
    exact hπ.not_isUnit (isUnit_of_dvd_unit hdvd u.isUnit)

private theorem jNGeomGen_mem_of_jGeomGen_mem {k : Type*} [Field k] {N : ℕ} [NeZero N]
    (dataN : ModularPolynomialData N)
    (w : Place k (modularFunctionFieldC k N))
    (hj : jGeomGen k N ∈ w.toValuationSubring) :
    jNGeomGen k N ∈ w.toValuationSubring := by
  set O := w.toValuationSubring with hO_def

  set f : Polynomial ℤ →+* O :=
    Polynomial.eval₂RingHom (Int.castRingHom O) (⟨jGeomGen k N, hj⟩ : O) with hf_def

  have hcomp : (algebraMap O (modularFunctionFieldC k N)).comp f
      = Polynomial.eval₂RingHom (Int.castRingHom (modularFunctionFieldC k N)) (jGeomGen k N) := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp [hf_def]
  have hint : IsIntegral O (jNGeomGen k N) := by
    refine ⟨(dataN.Φ).map f, dataN.monic.map f, ?_⟩
    rw [Polynomial.eval₂_map, hcomp]
    exact evalModularPair_jGeomGen_eq_zero k N dataN
  haveI : IsFractionRing O (modularFunctionFieldC k N) := inferInstance
  haveI : IsIntegrallyClosed O := inferInstance
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact SetLike.coe_mem y

private theorem place_trichotomy
    (N q : ℕ) [NeZero N] (hq : q.Prime) (_hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      ProlongationTuple.IsCuspidal P V ∨
        frobOnPlacesGeomLevel (ResidueField A) N data hKr
            (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V))
          = P.reduceFst V ∨
        P.IsStrictFst V ∨ P.IsStrictSnd V := by
  intro data hKr hα hβ P V
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  classical
  by_cases hcusp : ProlongationTuple.IsCuspidal P V
  · exact Or.inl hcusp
  by_cases hfix : frobOnPlacesGeomLevel (ResidueField A) N data hKr
      (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V)) = P.reduceFst V
  · exact Or.inr (Or.inl hfix)
  refine Or.inr (Or.inr ?_)
  rcases P.d1 V with h1 | h2
  ·
    have h1' : P.reduceFst V
        = frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceSnd V) := h1
    refine Or.inr ⟨h1', fun hsndfix => hfix ?_⟩
    calc frobOnPlacesGeomLevel (ResidueField A) N data hKr
          (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V))
        = frobOnPlacesGeomLevel (ResidueField A) N data hKr
            (frobOnPlacesGeomLevel (ResidueField A) N data hKr
              (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceSnd V))) := by
          rw [h1']
      _ = frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceSnd V) := by
          rw [hsndfix]
      _ = P.reduceFst V := h1'.symm
  ·
    have h2' : frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V)
        = P.reduceSnd V := h2
    exact Or.inl ⟨h2', hfix⟩

private theorem ord_sub_eq_of_ord_lt {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (h : v.ord x < v.ord y) :
    v.ord (x - y) = v.ord x := by
  have hne : x ≠ y := fun he => absurd (he ▸ rfl) (ne_of_lt h)
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hyx : v.adicValuation y < v.adicValuation x := by
    rw [v.adicValuation_eq_exp_neg_ord hx, v.adicValuation_eq_exp_neg_ord hy]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hle : v.adicValuation (x - y) ≤ v.adicValuation x :=
    le_trans (Valuation.map_sub _ _ _) (max_le le_rfl hyx.le)
  have hge : v.adicValuation x ≤ v.adicValuation (x - y) := by
    by_contra hlt
    push Not at hlt
    have hx' : v.adicValuation x ≤ max (v.adicValuation (x - y)) (v.adicValuation y) := by
      have : x = (x - y) + y := by ring
      calc v.adicValuation x = v.adicValuation ((x - y) + y) := by rw [← this]
        _ ≤ max (v.adicValuation (x - y)) (v.adicValuation y) := Valuation.map_add _ _ _
    exact absurd hx' (not_le.mpr (max_lt hlt hyx))
  have hval : v.adicValuation (x - y) = v.adicValuation x := le_antisymm hle hge
  rw [v.adicValuation_eq_exp_neg_ord hsub, v.adicValuation_eq_exp_neg_ord hx] at hval
  have := WithZero.exp_injective hval
  omega

private theorem ord_sub_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (hne : x ≠ y)
    (h0x : 0 ≤ v.ord x) (h0y : 0 ≤ v.ord y) : 0 ≤ v.ord (x - y) := by
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hle : v.adicValuation (x - y) ≤ 1 := by
    refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_) <;>
      [rw [v.adicValuation_eq_exp_neg_ord hx, ← WithZero.exp_zero];
       rw [v.adicValuation_eq_exp_neg_ord hy, ← WithZero.exp_zero]] <;>
      exact WithZero.exp_le_exp.mpr (by omega)
  rw [v.adicValuation_eq_exp_neg_ord hsub, ← WithZero.exp_zero] at hle
  have := WithZero.exp_le_exp.mp hle
  omega

private theorem Avoidance.avoid_exists_isPrincipal_degree_forall_support
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (good : Place K F → Prop)
    (surgery : ∀ V₀ : Place K F, ¬ good V₀ →
      ∃ p : Divisor K F, Divisor.IsPrincipal p ∧ p V₀ = -1 ∧ Divisor.degree p = 0 ∧
        ∀ V ∈ p.support, V ≠ V₀ → good V)
    (D : Divisor K F) :
    ∃ e : Divisor K F, Divisor.IsPrincipal e ∧ Divisor.degree e = 0 ∧
      ∀ V ∈ (D + e).support, good V := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, ∑ V ∈ D.support.filter (fun V => ¬ good V), (D V).natAbs = n :=
    ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing D with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn0
    ·
      refine ⟨0, ⟨1, one_ne_zero, fun v => by simp⟩, by simp, ?_⟩
      intro V hV
      rw [add_zero] at hV
      by_contra hbad
      have hVmem : V ∈ D.support.filter (fun V => ¬ good V) :=
        Finset.mem_filter.mpr ⟨hV, hbad⟩
      have hne : (D V).natAbs ≠ 0 := by
        simpa [Int.natAbs_ne_zero] using Finsupp.mem_support_iff.mp hV
      have hle : (D V).natAbs ≤ ∑ V ∈ D.support.filter (fun V => ¬ good V), (D V).natAbs :=
        Finset.single_le_sum (f := fun V => (D V).natAbs) (fun _ _ => Nat.zero_le _) hVmem
      omega
    ·
      have hex : ∃ V₀ ∈ D.support.filter (fun V => ¬ good V), (D V₀).natAbs ≠ 0 := by
        by_contra hall
        push Not at hall
        have : ∑ V ∈ D.support.filter (fun V => ¬ good V), (D V).natAbs = 0 :=
          Finset.sum_eq_zero fun V hV => hall V hV
        omega
      obtain ⟨V₀, hV₀mem, hV₀ne⟩ := hex
      obtain ⟨hV₀supp, hV₀bad⟩ := Finset.mem_filter.mp hV₀mem
      obtain ⟨p, hp, hpV₀, hpdeg, hpgood⟩ := surgery V₀ hV₀bad

      set D' : Divisor K F := D + (D V₀) • p with hD'
      have hD'V₀ : D' V₀ = 0 := by
        have h1 : D' V₀ = D V₀ + (D V₀) * (p V₀) := by
          simp [hD', Finsupp.add_apply, Finsupp.smul_apply]
        rw [h1, hpV₀]
        ring
      have hD'eq : ∀ V, V ≠ V₀ → ¬ good V → D' V = D V := by
        intro V hne hbad
        have hpV : p V = 0 := by
          by_contra hpne
          exact hbad (hpgood V (Finsupp.mem_support_iff.mpr hpne) hne)
        simp [hD', Finsupp.add_apply, Finsupp.smul_apply, hpV]

      have hsub : D'.support.filter (fun V => ¬ good V)
          ⊆ (D.support.filter (fun V => ¬ good V)).erase V₀ := by
        intro V hV
        obtain ⟨hVs, hVbad⟩ := Finset.mem_filter.mp hV
        have hne : V ≠ V₀ := by
          rintro rfl
          exact Finsupp.mem_support_iff.mp hVs hD'V₀
        refine Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr ⟨?_, hVbad⟩⟩
        have hD'V := Finsupp.mem_support_iff.mp hVs
        rw [hD'eq V hne hVbad] at hD'V
        exact Finsupp.mem_support_iff.mpr hD'V
      have hMD' : ∑ V ∈ D'.support.filter (fun V => ¬ good V), (D' V).natAbs < n := by
        have h1 : ∑ V ∈ D'.support.filter (fun V => ¬ good V), (D' V).natAbs
            ≤ ∑ V ∈ (D.support.filter (fun V => ¬ good V)).erase V₀, (D' V).natAbs :=
          Finset.sum_le_sum_of_subset hsub
        have h2 : ∑ V ∈ (D.support.filter (fun V => ¬ good V)).erase V₀, (D' V).natAbs
            = ∑ V ∈ (D.support.filter (fun V => ¬ good V)).erase V₀, (D V).natAbs := by
          refine Finset.sum_congr rfl fun V hV => ?_
          obtain ⟨hne, hVmem⟩ := Finset.mem_erase.mp hV
          rw [hD'eq V hne (Finset.mem_filter.mp hVmem).2]
        have h3 : ∑ V ∈ (D.support.filter (fun V => ¬ good V)).erase V₀, (D V).natAbs
            + (D V₀).natAbs = ∑ V ∈ D.support.filter (fun V => ¬ good V), (D V).natAbs :=
          Finset.sum_erase_add _ _ hV₀mem
        omega
      obtain ⟨e', he'p, he'deg, he'good⟩ := ih _ hMD' D' rfl
      refine ⟨(D V₀) • p + e', ?_, ?_, ?_⟩
      · exact AddSubgroup.add_mem _ (AddSubgroup.zsmul_mem _
          (Divisor.mem_principal.mpr hp) _) (Divisor.mem_principal.mpr he'p)
      · rw [map_add, he'deg, map_zsmul, hpdeg]
        simp
      · intro V hV
        have harr : D + ((D V₀) • p + e') = D' + e' := by
          rw [hD']
          abel
        rw [harr] at hV
        exact he'good V hV

private def goodJS (N q : ℕ) [NeZero N] [NeZero q]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (S : Finset (ResidueField A))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : Prop :=
  ∃ a : A,
    0 < V.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full (N * q) (jq_mem (N * q)))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
              (a : AlgebraicClosure ℚ)) ∧
      IsLocalRing.residue A a ∉ S

open Classical in

private noncomputable def badPoints
    (N q : ℕ) [NeZero N] [NeZero q] [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField A) q]
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)))
    (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)) :=
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  let base := T ∪ {P.reduceFst V₀, P.reduceSnd V₀}
  (base ∪ base.image (frobOnPlacesGeomLevel (ResidueField A) N data hKr)) ∪
    base.preimage (frobOnPlacesGeomLevel (ResidueField A) N data hKr)
      ((frobOnPlacesGeomLevel_injective (ResidueField A) N data hKr).injOn)

open Classical in

private noncomputable def forbiddenSet
    (N q : ℕ) [NeZero N] [NeZero q] [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField A) q]
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (R : ProlongationTuple P)
    (F : modularFunctionFieldBar (N * q))
    (hF₁ : F ∈ R.R₁.integers) (hF₂ : F ∈ R.R₂.integers)
    (T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)))
    (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    Finset (ResidueField A) :=
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  let pts := badPoints N q A data hKr P T V₀
  (pts.image (valOf (R.residue₁ ⟨F, hF₁⟩)) ∪ pts.image (valOf (R.residue₂ ⟨F, hF₂⟩))) ∪
    ((if h : ∃ x : ResidueField A, R.residue₁ ⟨F, hF₁⟩
        = algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) x
      then {h.choose} else ∅) ∪
      (if h : ∃ x : ResidueField A, R.residue₂ ⟨F, hF₂⟩
          = algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) x
        then {h.choose} else ∅))

private theorem ord_neg_of_notMem {K F : Type*} [Field K] [Field F] [Algebra K F]
    {w : Place K F} {f : F} (hf : f ∉ w.toValuationSubring) : w.ord f < 0 := by
  have hf0 : f ≠ 0 := fun h => hf (h ▸ zero_mem _)
  have hinv : f⁻¹ ∈ w.toValuationSubring :=
    (w.toValuationSubring.mem_or_inv_mem f).resolve_left hf
  have h1 : 0 ≤ w.ord f⁻¹ := ord_nonneg_of_mem hinv
  rw [Place.ord_inv] at h1
  rcases (show w.ord f ≤ 0 by omega).lt_or_eq with h | h
  · exact h
  · exfalso
    haveI : IsDiscreteValuationRing w.toValuationSubring := by
      refine ⟨?_⟩
      intro hbot
      exact ValuationSubring.not_isField_of_ne_top (F := F) (A := w.toValuationSubring) w.ne_top'
        (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot)
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
    obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow (inv_ne_zero hf0) hπ
    have hordinv : w.ord f⁻¹ = 0 := by
      rw [Place.ord_inv, h, neg_zero]
    rw [hordinv, zpow_zero, mul_one] at hu
    have h2F : (((u⁻¹ : w.toValuationSubringˣ) : w.toValuationSubring) : F)
        * (((u : w.toValuationSubringˣ) : w.toValuationSubring) : F) = 1 := by
      have h2 := u.inv_mul
      have h3 := congrArg (fun z : w.toValuationSubring => (z : F)) h2
      push_cast at h3
      exact h3
    have hfval : f = (((u⁻¹ : w.toValuationSubringˣ) : w.toValuationSubring) : F) := by
      have h4 := congrArg Inv.inv hu
      rw [inv_inv] at h4
      rw [h4, eq_comm]
      exact eq_inv_of_mul_eq_one_left h2F
    rw [hfval] at hf
    exact hf (SetLike.coe_mem _)

private theorem ne_algebraMap_of_coeff_neg_one_eq_one {L : Type*} [Field L]
    {S : IntermediateField L (LaurentSeries L)} {x : ↥S}
    (hx : (x : LaurentSeries L).coeff (-1 : ℤ) = 1) (c : L) : x ≠ algebraMap L ↥S c := by
  intro h
  have hamb : (x : LaurentSeries L) = algebraMap L (LaurentSeries L) c := by
    rw [h]
    rfl
  have h5 : (algebraMap L (LaurentSeries L)) c = HahnSeries.single (0 : ℤ) c := by
    rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, HahnSeries.ofPowerSeries_C]
    rfl
  rw [hamb, h5, HahnSeries.coeff_single_of_ne (by norm_num : (-1 : ℤ) ≠ 0)] at hx
  exact zero_ne_one hx
private theorem exists_badSet
    (N q : ℕ) [NeZero N] (hq : q.Prime) (_hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ S : Finset (ResidueField A),
      ∃ T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)),
        ∀ t : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N),
          ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩
              : modularFunctionFieldC (ResidueField A) N) ∉ t.toValuationSubring ∨
            ∃ s ∈ S, 0 < t.ord
              ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩
                  : modularFunctionFieldC (ResidueField A) N)
                - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) s)) →
          t ∈ T := by
  intro S
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  classical
  haveI hICO : IsCurveOver (ResidueField A) (modularFunctionFieldC (ResidueField A) N) :=
    isCurveOver_modularFunctionFieldC_of_perfectField (ResidueField A) N
  set jel : ↥(modularFunctionFieldC (ResidueField A) N) :=
    ⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ with hjel_def
  have hjcoeff : ((jel : ↥(modularFunctionFieldC (ResidueField A) N)) : LaurentSeries (ResidueField A)).coeff (-1 : ℤ) = 1 := by
    rw [hjel_def]
    exact coeff_jqModC_neg_one (ResidueField A)
  have hnc : ∀ c : ResidueField A, jel ≠ algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) c :=
    fun c => ne_algebraMap_of_coeff_neg_one_eq_one hjcoeff c
  have hjne : jel ≠ 0 := by
    intro h0
    exact hnc 0 (by rw [h0, map_zero])
  obtain ⟨Dinf, hDinf, hDinfdeg⟩ :=
    HasPrincipalDivisors.exists_divisor (K := ResidueField A)
      (F := ↥(modularFunctionFieldC (ResidueField A) N)) jel hjne
  set Ds : ResidueField A → Divisor (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) :=
    fun s => if h : jel - algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) s ≠ 0 then
        (HasPrincipalDivisors.exists_divisor (K := ResidueField A)
          (F := ↥(modularFunctionFieldC (ResidueField A) N)) _ h).choose
      else 0 with hDs_def
  have hDs_spec : ∀ s
      (v : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))
      (h : jel - algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) s ≠ 0),
      (Ds s) v = v.ord (jel - algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) s) := by
    intro s v h
    rw [hDs_def]
    simp only [dif_pos h]
    exact ((HasPrincipalDivisors.exists_divisor (K := ResidueField A)
      (F := ↥(modularFunctionFieldC (ResidueField A) N)) _ h).choose_spec).1 v
  refine ⟨Dinf.support ∪ S.biUnion (fun s => (Ds s).support), ?_⟩
  intro t ht
  rcases ht with hpole | ⟨s, hs, hzero⟩
  · refine Finset.mem_union_left _ ?_
    rw [Finsupp.mem_support_iff, hDinf t]
    have hneg := ord_neg_of_notMem hpole
    omega
  · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨s, hs, ?_⟩)
    have hne : jel - algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) s ≠ 0 := by
      intro h0
      rw [h0, Place.ord_zero] at hzero
      omega
    rw [Finsupp.mem_support_iff, hDs_spec s t hne]
    omega

private theorem ord_algebraMap_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    {w : Place K F} {c : K} (_hc : c ≠ 0) : w.ord (algebraMap K F c) = 0 := by
  have h1 := ord_nonneg_of_mem (w.algebraMap_mem' c)
  have h2 : (algebraMap K F c)⁻¹ ∈ w.toValuationSubring := by
    rw [← map_inv₀]
    exact w.algebraMap_mem' c⁻¹
  have h3 := ord_nonneg_of_mem h2
  rw [Place.ord_inv] at h3
  omega

open Classical in

open Classical in
private theorem mapDomain_filtered_pin {σ τ : Type*}
    (r : σ → τ) (D : σ →₀ ℤ) (sf : σ → Prop) (t : τ) (V₀ V' : σ)
    (hV't : r V' = t) (hne : V' ≠ V₀)
    (hD₀ : -1 ≤ D V₀)
    (hmates : ∀ V'', V'' ≠ V₀ → r V'' = t → 0 ≤ D V'')
    (hD' : 0 < D V') (hsf' : sf V')
    (hlaw : Finsupp.mapDomain r (Finsupp.filter sf D) t = -1) : False := by
  classical
  have happ : Finsupp.mapDomain r (Finsupp.filter sf D) t
      = ∑ a ∈ (Finsupp.filter sf D).support, if r a = t then (Finsupp.filter sf D) a else 0 := by
    simp [Finsupp.mapDomain, Finsupp.sum, Finsupp.single_apply]
  have hV'val : (Finsupp.filter sf D) V' = D V' := by
    rw [Finsupp.filter_apply, if_pos hsf']
  have hV'mem : V' ∈ (Finsupp.filter sf D).support := by
    rw [Finsupp.mem_support_iff, hV'val]
    omega

  have hbound : ∀ a ∈ (Finsupp.filter sf D).support.erase V',
      (if a = V₀ then (-1 : ℤ) else 0) ≤ (if r a = t then (Finsupp.filter sf D) a else 0) := by
    intro a ha
    by_cases hat : r a = t
    · rw [if_pos hat]
      by_cases haV₀ : a = V₀
      · subst haV₀
        rw [if_pos rfl, Finsupp.filter_apply]
        split
        · exact hD₀
        · omega
      · rw [if_neg haV₀, Finsupp.filter_apply]
        have h0 : 0 ≤ D a := hmates a haV₀ hat
        split
        · exact h0
        · omega
    · rw [if_neg hat]
      split <;> omega
  have hsum₀ : ∑ a ∈ (Finsupp.filter sf D).support.erase V',
      (if a = V₀ then (-1 : ℤ) else 0) ≤ ∑ a ∈ (Finsupp.filter sf D).support.erase V',
      (if r a = t then (Finsupp.filter sf D) a else 0) := Finset.sum_le_sum hbound
  have hind : ∑ a ∈ (Finsupp.filter sf D).support.erase V',
      (if a = V₀ then (-1 : ℤ) else 0) = if V₀ ∈ (Finsupp.filter sf D).support.erase V'
        then (-1 : ℤ) else 0 := Finset.sum_ite_eq' _ _ _
  have hsplit : ∑ a ∈ (Finsupp.filter sf D).support,
        (if r a = t then (Finsupp.filter sf D) a else 0)
      = (if r V' = t then (Finsupp.filter sf D) V' else 0)
        + ∑ a ∈ (Finsupp.filter sf D).support.erase V',
          (if r a = t then (Finsupp.filter sf D) a else 0) :=
    (Finset.add_sum_erase _ _ hV'mem).symm
  rw [happ, hsplit, if_pos hV't, hV'val] at hlaw
  have : (-1 : ℤ) ≤ ∑ a ∈ (Finsupp.filter sf D).support.erase V',
      (if r a = t then (Finsupp.filter sf D) a else 0) := by
    calc (-1 : ℤ) ≤ if V₀ ∈ (Finsupp.filter sf D).support.erase V' then (-1 : ℤ) else 0 := by
          split <;> omega
      _ = _ := hind.symm
      _ ≤ _ := hsum₀
  omega

private theorem mapDomain_pin {σ τ : Type*}
    (r : σ → τ) (D : σ →₀ ℤ) (t : τ) (V₀ V' : σ)
    (hV't : r V' = t) (hne : V' ≠ V₀)
    (hD₀ : -1 ≤ D V₀)
    (hmates : ∀ V'', V'' ≠ V₀ → r V'' = t → 0 ≤ D V'')
    (hD' : 0 < D V')
    (hlaw : Finsupp.mapDomain r D t = -1) : False := by
  classical
  have happ : Finsupp.mapDomain r D t = ∑ a ∈ D.support, if r a = t then D a else 0 := by
    simp [Finsupp.mapDomain, Finsupp.sum, Finsupp.single_apply]
  have hV'mem : V' ∈ D.support := by
    rw [Finsupp.mem_support_iff]
    omega
  have hbound : ∀ a ∈ D.support.erase V',
      (if a = V₀ then (-1 : ℤ) else 0) ≤ (if r a = t then D a else 0) := by
    intro a _
    by_cases hat : r a = t
    · rw [if_pos hat]
      by_cases haV₀ : a = V₀
      · subst haV₀
        rw [if_pos rfl]
        exact hD₀
      · rw [if_neg haV₀]
        exact hmates a haV₀ hat
    · rw [if_neg hat]
      split <;> omega
  have hsum₀ : ∑ a ∈ D.support.erase V', (if a = V₀ then (-1 : ℤ) else 0)
      ≤ ∑ a ∈ D.support.erase V', (if r a = t then D a else 0) := Finset.sum_le_sum hbound
  have hind : ∑ a ∈ D.support.erase V', (if a = V₀ then (-1 : ℤ) else 0)
      = if V₀ ∈ D.support.erase V' then (-1 : ℤ) else 0 := Finset.sum_ite_eq' _ _ _
  have hsplit : ∑ a ∈ D.support, (if r a = t then D a else 0)
      = (if r V' = t then D V' else 0)
        + ∑ a ∈ D.support.erase V', (if r a = t then D a else 0) :=
    (Finset.add_sum_erase _ _ hV'mem).symm
  rw [happ, hsplit, if_pos hV't] at hlaw
  have : (-1 : ℤ) ≤ ∑ a ∈ D.support.erase V', (if r a = t then D a else 0) := by
    calc (-1 : ℤ) ≤ if V₀ ∈ D.support.erase V' then (-1 : ℤ) else 0 := by
          split <;> omega
      _ = _ := hind.symm
      _ ≤ _ := hsum₀
  omega

private theorem Avoidance.commonUnit_fst
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : ProlongationTuple P), R.IsModel → R.OrderLawFixed →
      ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N))),
      R.RegularityLaw W → (∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A)) →
      ∀ (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
        ProlongationTuple.IsInftySide P V₀ ∨ P.IsStrictFst V₀ →
        ∀ (S : Finset (ResidueField A))
          (B : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))),
        ∃ (g : modularFunctionFieldBar (N * q))
          (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers),
          R.R₁.residue ⟨g, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨g, h₂⟩ ≠ 0 ∧ V₀.ord g = -1 ∧
          (∀ V, V ≠ V₀ → V.ord g < 0 →
            (∃ a : A, 0 < V.ord (ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ)
                (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) ∧
              IsLocalRing.residue A a ∉ S) ∧
              P.reduceFst V ∉ B ∧ P.reduceSnd V ∉ B) ∧
          (P.reduceFst V₀).ord (R.residue₁ ⟨g, h₁⟩) = -1 := by
  intro data hKr hα hβ P R hM hO W hRL hW V₀ hV₀ S B
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  exact ProlongationTuple.exists_commonUnit_pole_reduceFst_of_regularityLaw
    q A N (ResidueField A) (IsLocalRing.residue A) data hKr hα hβ P R hM hO W hRL hW hqN V₀ hV₀ S B

private theorem Avoidance.commonUnit_snd
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : ProlongationTuple P), R.IsModel → R.OrderLawFixed →
      ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N))),
      R.RegularityLaw W → (∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A)) →
      ∀ (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
        ProlongationTuple.IsZeroSide P V₀ ∨ P.IsStrictSnd V₀ →
        ∀ (S : Finset (ResidueField A))
          (B : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))),
        ∃ (g : modularFunctionFieldBar (N * q))
          (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers),
          R.R₁.residue ⟨g, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨g, h₂⟩ ≠ 0 ∧ V₀.ord g = -1 ∧
          (∀ V, V ≠ V₀ → V.ord g < 0 →
            (∃ a : A, 0 < V.ord (ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ)
                (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) ∧
              IsLocalRing.residue A a ∉ S) ∧
              P.reduceFst V ∉ B ∧ P.reduceSnd V ∉ B) ∧
          (P.reduceSnd V₀).ord (R.residue₂ ⟨g, h₂⟩) = -1 := by
  intro data hKr hα hβ P R hM hO W hRL hW V₀ hV₀ S B
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  exact ProlongationTuple.exists_commonUnit_pole_reduceSnd_of_regularityLaw
    q A N (ResidueField A) (IsLocalRing.residue A) data hKr hα hβ P R hM hO W hRL hW hqN V₀ hV₀ S B

namespace Avoidance

open ModularCurve.PlaceSpecialization.ProlongationTuple

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
  {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

omit [IsAlgClosed k] [DecidableEq k] in

private theorem heckeAlphaBar_jN_sub (a : A) :
    heckeAlphaBar (AlgebraicClosure ℚ) N q
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
      = jFun N q
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
              (a : AlgebraicClosure ℚ) := by
  rw [map_sub]
  congr 1

omit [IsAlgClosed k] [DecidableEq k] in

private theorem heckeBetaBar_jN_sub (a : A) :
    heckeBetaBar (AlgebraicClosure ℚ) N q
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
      = jQFun N q
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
              (a : AlgebraicClosure ℚ) := by
  rw [map_sub, AlgHom.commutes]
  congr 1
  apply Subtype.ext
  rw [coe_heckeBetaBar]
  exact (ModularCurve.coeffSemilinearAut.coeffMap_qExpand
    (algebraMap ℚ (AlgebraicClosure ℚ)) q jq).symm

private theorem ord_restrictAlong_nonpos {K₀ F₀ F₁ : Type*} [Field K₀] [Field F₀] [Field F₁]
    [Algebra K₀ F₀] [Algebra K₀ F₁] (ψ : F₀ →ₐ[K₀] F₁) (hψ : ψ.toRingHom.IsIntegral)
    (c : Place K₀ F₁) (x : F₀)
    (hc : c.ord (ψ x) ≤ 0) : (c.restrictAlong ψ hψ).ord x ≤ 0 := by
  have hord := Place.ord_restrictAlong ψ hψ c x
  have he := ramificationIndexAlong_pos ψ hψ c
  by_contra hlt
  push Not at hlt
  have hprod := mul_pos (Int.natCast_pos.mpr he) hlt
  rw [← hord] at hprod
  exact absurd hc (not_le.mpr hprod)

private theorem ord_restrictAlong_pos {K₀ F₀ F₁ : Type*} [Field K₀] [Field F₀] [Field F₁]
    [Algebra K₀ F₀] [Algebra K₀ F₁] (ψ : F₀ →ₐ[K₀] F₁) (hψ : ψ.toRingHom.IsIntegral)
    (c : Place K₀ F₁) (x : F₀)
    (hc : 0 < c.ord (ψ x)) : 0 < (c.restrictAlong ψ hψ).ord x := by
  have hord := Place.ord_restrictAlong ψ hψ c x
  by_contra hle
  push Not at hle
  have hprod := mul_nonpos_of_nonneg_of_nonpos
    (Int.natCast_nonneg (Place.ramificationIndexAlong ψ c)) hle
  rw [← hord] at hprod
  exact absurd hc (not_lt.mpr hprod)

omit [IsAlgClosed k] [DecidableEq k] in

private theorem reduceFst_ord_lt_zero_of_isCuspidal
    (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hc : IsCuspidal P c) :
    (P.reduceFst c).ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0 := by
  refine P.d0_j_pole _ (fun a => ?_)
  refine ord_restrictAlong_nonpos (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα c _ ?_
  rw [heckeAlphaBar_jN_sub]
  exact hc a

omit [IsAlgClosed k] [DecidableEq k] in

private theorem reduceSnd_ord_lt_zero_of_isCuspidal'
    (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hc : IsCuspidal' P c) :
    (P.reduceSnd c).ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0 := by
  refine P.d0_j_pole _ (fun a => ?_)
  refine ord_restrictAlong_nonpos (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ c _ ?_
  rw [heckeBetaBar_jN_sub]
  exact hc a

omit [IsAlgClosed k] [DecidableEq k] in

private theorem isCuspidal_of_reduceFst_ord_lt_zero
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hV : (P.reduceFst V).ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0) :
    IsCuspidal P V := by
  intro a
  by_contra hpos
  push Not at hpos
  rw [← heckeAlphaBar_jN_sub] at hpos
  have hup := ord_restrictAlong_pos (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V _ hpos
  have hdown : 0 < (P.reduceFst V).ord ((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
      - algebraMap k (modularFunctionFieldC k N) (red a)) := P.d0_j _ a hup
  have hne : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
      - algebraMap k (modularFunctionFieldC k N) (red a) ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at hdown
    exact lt_irrefl _ hdown
  have hmem := (P.reduceFst V).mem_of_ord_nonneg hne hdown.le
  have hj : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
      ∈ (P.reduceFst V).toValuationSubring := by
    have h := add_mem hmem ((P.reduceFst V).algebraMap_mem' (red a))
    rwa [sub_add_cancel] at h
  exact absurd hV (not_lt.mpr ((P.reduceFst V).ord_nonneg_of_mem hj))

omit [DecidableEq k] in

private theorem ord_frob_jGeom_eq (w : Place k (modularFunctionFieldC k N)) :
    (frobOnPlacesGeomLevel k N data hKr w).ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
      = w.ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) := by
  have hperf : ∀ x : k, ∃ d : k, d ^ q = x := fun x =>
    IsAlgClosed.exists_pow_nat_eq x (Fact.out : q.Prime).pos
  exact ord_frobOnPlaces_of_pow_eq k N data hKr hperf (frobeniusGeomLevel_jq k N data hKr) w

omit [DecidableEq k] in

private theorem ord_jGeom_reduceSnd_eq_reduceFst
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    (P.reduceSnd V).ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
      = (P.reduceFst V).ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) := by
  rcases P.d1 V with h1 | h2
  · have h1' : P.reduceFst V = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd V) := h1
    rw [h1', ord_frob_jGeom_eq]
  · have h2' : frobOnPlacesGeomLevel k N data hKr (P.reduceFst V) = P.reduceSnd V := h2
    rw [← h2', ord_frob_jGeom_eq]

omit [Fact q.Prime] [IsAlgClosed k] [DecidableEq k] in
private theorem not_isAffineGeomPlace_of_ord_jGeom_lt_zero (v : Place k (modularFunctionFieldC k N))
    (hv : v.ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0) :
    ¬ IsAffineGeomPlace k N v :=
  fun haff => absurd hv (not_lt.mpr (v.ord_nonneg_of_mem haff.1))

omit [Fact q.Prime] [IsAlgClosed k] [DecidableEq k] in
private theorem isAffineGeomPlace_of_ord_jGeom_nonneg (dataN : ModularPolynomialData N)
    (v : Place k (modularFunctionFieldC k N))
    (hv : 0 ≤ v.ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)) :
    IsAffineGeomPlace k N v := by
  have hj : jGeomGen k N ∈ v.toValuationSubring := by
    by_cases h0 : jGeomGen k N = 0
    · rw [h0]; exact zero_mem _
    · exact v.mem_of_ord_nonneg h0 hv
  exact ⟨hj, jNGeomGen_mem_of_jGeomGen_mem dataN v hj⟩

end Avoidance

private theorem Avoidance.affine_of_noncusp
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      ¬ ProlongationTuple.IsCuspidal P V' →
        IsAffineGeomPlace (ResidueField A) N (P.reduceFst V') ∧
          IsAffineGeomPlace (ResidueField A) N (P.reduceSnd V') := by
  intro data hKr hα hβ P V' hnc
  have _ := hqN
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  obtain ⟨dataN⟩ := ModularCurve.nonempty_modularPolynomialData N
  have hfst : 0 ≤ (P.reduceFst V').ord
      (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩
        : modularFunctionFieldC (ResidueField A) N) := by
    by_contra hlt
    push Not at hlt
    exact hnc (Avoidance.isCuspidal_of_reduceFst_ord_lt_zero V' hlt)

  have hsnd : 0 ≤ (P.reduceSnd V').ord
      (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩
        : modularFunctionFieldC (ResidueField A) N) := by
    rw [Avoidance.ord_jGeom_reduceSnd_eq_reduceFst (P := P) V']
    exact hfst
  exact ⟨Avoidance.isAffineGeomPlace_of_ord_jGeom_nonneg dataN _ hfst,
    Avoidance.isAffineGeomPlace_of_ord_jGeom_nonneg dataN _ hsnd⟩

private theorem Avoidance.nonaffine_of_cusp
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      ProlongationTuple.IsCuspidal P V' ∨ ProlongationTuple.IsCuspidal' P V' →
        ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceFst V') ∧
          ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceSnd V') := by
  intro data hKr hα hβ P V' hc
  have _ := hqN
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N

  have hfst : (P.reduceFst V').ord
      (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩
        : modularFunctionFieldC (ResidueField A) N) < 0 := by
    rcases hc with h | h'
    · exact Avoidance.reduceFst_ord_lt_zero_of_isCuspidal V' h
    · rw [← Avoidance.ord_jGeom_reduceSnd_eq_reduceFst (P := P) V']
      exact Avoidance.reduceSnd_ord_lt_zero_of_isCuspidal' V' h'
  have hsnd : (P.reduceSnd V').ord
      (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩
        : modularFunctionFieldC (ResidueField A) N) < 0 := by
    rw [Avoidance.ord_jGeom_reduceSnd_eq_reduceFst (P := P) V']
    exact hfst
  exact ⟨Avoidance.not_isAffineGeomPlace_of_ord_jGeom_lt_zero _ hfst,
    Avoidance.not_isAffineGeomPlace_of_ord_jGeom_lt_zero _ hsnd⟩

private theorem Avoidance.componentLawFst
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      ProlongationTuple.IsInftySide P V →
        frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V) = P.reduceSnd V := by
  intro data hKr hα hβ P V hV
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  exact (ProlongationTuple.reduceSnd_eq_frobOnPlacesGeomLevel_reduceFst_of_isInftySide P hqN V hV).symm

private theorem Avoidance.componentLawSnd
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      ProlongationTuple.IsZeroSide P V →
        P.reduceFst V = frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceSnd V) := by
  intro data hKr hα hβ P V hV
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  exact ProlongationTuple.reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide P hqN V hV

private theorem Avoidance.badTypology_nonnode
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (S : Finset (ResidueField A))
      (T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)))
      (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      (P.reduceFst V₀ ∈ T ∨ P.reduceSnd V₀ ∈ T ∨ ¬ goodJS N q A S V₀) →
      ¬ (frobOnPlacesGeomLevel (ResidueField A) N data hKr
            (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V₀))
          = P.reduceFst V₀ ∧
        IsAffineGeomPlace (ResidueField A) N (P.reduceFst V₀)) →
      (ProlongationTuple.IsInftySide P V₀ ∨ P.IsStrictFst V₀) ∨
        (ProlongationTuple.IsZeroSide P V₀ ∨ P.IsStrictSnd V₀) := by
  intro data hKr hα hβ P S T V₀ _hbad hnn
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  have _ := S
  have _ := T
  by_cases hcusp : ProlongationTuple.IsCuspidal P V₀
  ·
    rcases ProlongationTuple.isInftySide_or_isZeroSide_of_isCuspidal P hqN V₀ hcusp with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
  ·
    have haff := (Avoidance.affine_of_noncusp N q hq hqN A hA data hKr hα hβ P V₀ hcusp).1
    have hnfix : frobOnPlacesGeomLevel (ResidueField A) N data hKr
        (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V₀)) ≠ P.reduceFst V₀ :=
      fun hfix => hnn ⟨hfix, haff⟩
    rcases P.d1 V₀ with h1 | h2
    ·
      have h1' : P.reduceFst V₀
          = frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceSnd V₀) := h1
      refine Or.inr (Or.inr ⟨h1', fun hsndfix => hnfix ?_⟩)
      calc frobOnPlacesGeomLevel (ResidueField A) N data hKr
            (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V₀))
          = frobOnPlacesGeomLevel (ResidueField A) N data hKr
              (frobOnPlacesGeomLevel (ResidueField A) N data hKr
                (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceSnd V₀))) := by
            rw [h1']
        _ = frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceSnd V₀) := by
            rw [hsndfix]
        _ = P.reduceFst V₀ := h1'.symm
    ·
      have h2' : frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V₀)
          = P.reduceSnd V₀ := h2
      exact Or.inl (Or.inr ⟨h2', hnfix⟩)
private theorem zeros_good
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    letI := Classical.decEq (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : ProlongationTuple P)
      (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N))),
      R.IsModel → R.RegularityLaw W → R.OrderLawFixed →
      ∀ (S : Finset (ResidueField A))
        (T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))),
        (∀ t : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N),
          ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩
              : modularFunctionFieldC (ResidueField A) N) ∉ t.toValuationSubring ∨
            ∃ s ∈ S, 0 < t.ord
              ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩
                  : modularFunctionFieldC (ResidueField A) N)
                - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) s)) →
          t ∈ T) →
        ∀ (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
          (f₀ U : ↥(modularFunctionFieldBar (N * q))) (c : A),
          (∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V' ≠ V₀ →
            P.reduceFst V' ∈ T ∪ {P.reduceFst V₀, P.reduceSnd V₀} →
            ¬ 0 < V'.ord (U * f₀ - algebraMap (AlgebraicClosure ℚ)
                (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ))) →
          ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
            0 < V.ord (U * f₀ - algebraMap (AlgebraicClosure ℚ)
                (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ)) →
            V ≠ V₀ → goodJS N q A S V := by
  intro data hKr hα hβ P R W _ _ _ S T hT V₀ f₀ U c hnz V hpos hVne
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  classical

  have houtFst : P.reduceFst V ∉ T ∪ {P.reduceFst V₀, P.reduceSnd V₀} := by
    intro hmem
    exact hnz V hVne hmem hpos

  have houtT : P.reduceFst V ∉ T := by
    intro hmemT
    exact houtFst (Finset.mem_union_left _ hmemT)

  have hTc : ¬ (((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩
        : modularFunctionFieldC (ResidueField A) N) ∉ (P.reduceFst V).toValuationSubring) ∨
      ∃ s ∈ S, 0 < (P.reduceFst V).ord
        ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩
            : modularFunctionFieldC (ResidueField A) N)
          - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) s)) := by
    intro hcase
    exact houtT (hT _ hcase)
  push Not at hTc
  obtain ⟨hmemVS, hnoval⟩ := hTc
  have hnopole : ¬ (P.reduceFst V).ord
      (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩
        : modularFunctionFieldC (ResidueField A) N) < 0 :=
    not_lt.mpr (ord_nonneg_of_mem hmemVS)
  exact goodJ_of_reduceFst_affine_goodVal N q hq hqN A hA data hKr hα hβ P S V hnopole
    (fun s hs => not_lt.mpr (hnoval s hs))

private theorem Avoidance.sectionKit
    (N q : ℕ) [NeZero N] (hq : q.Prime) (_hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : ProlongationTuple P)
      (S : Finset (ResidueField A))
      (T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)))
      (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
      (g : modularFunctionFieldBar (N * q))
      (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers),
      V₀.ord g = -1 →
      (∀ V, V ≠ V₀ → V.ord g < 0 →
        (∃ a : A, 0 < V.ord (ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ)
            (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) ∧
          IsLocalRing.residue A a ∉ S) ∧
          P.reduceFst V ∉ badPoints N q A data hKr P T V₀ ∧
          P.reduceSnd V ∉ badPoints N q A data hKr P T V₀) →
      ∃ (c : A)
        (h₁' : g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
          (c : AlgebraicClosure ℚ) ∈ R.R₁.integers)
        (h₂' : g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
          (c : AlgebraicClosure ℚ) ∈ R.R₂.integers),
        (R.residue₁ ⟨g - algebraMap (AlgebraicClosure ℚ)
            (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ), h₁'⟩
          = R.residue₁ ⟨g, h₁⟩
            - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
                (IsLocalRing.residue A c)) ∧
        (R.residue₂ ⟨g - algebraMap (AlgebraicClosure ℚ)
            (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ), h₂'⟩
          = R.residue₂ ⟨g, h₂⟩
            - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
                (IsLocalRing.residue A c)) ∧
        (R.R₁.residue ⟨g - algebraMap (AlgebraicClosure ℚ)
            (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ), h₁'⟩ ≠ 0) ∧
        (R.R₂.residue ⟨g - algebraMap (AlgebraicClosure ℚ)
            (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ), h₂'⟩ ≠ 0) ∧
        (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
            (c : AlgebraicClosure ℚ) ≠ 0) ∧
        (V₀.ord (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
            (c : AlgebraicClosure ℚ)) = -1) ∧
        (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
          V.ord (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
            (c : AlgebraicClosure ℚ)) < 0 → V.ord g < 0) ∧
        (∀ V, V.ord g < 0 → V = V₀ ∨ goodJS N q A S V) ∧
        P.reduceFst V₀ ∈ badPoints N q A data hKr P T V₀ ∧
        P.reduceSnd V₀ ∈ badPoints N q A data hKr P T V₀ ∧
        (∀ t' , t' ∈ badPoints N q A data hKr P T V₀ →
          ∀ V'' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V'' ≠ V₀ →
          P.reduceFst V'' = t' →
          0 ≤ V''.ord (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
            (c : AlgebraicClosure ℚ))) ∧
        (∀ t' , t' ∈ badPoints N q A data hKr P T V₀ →
          ∀ V'' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V'' ≠ V₀ →
          P.reduceSnd V'' = t' →
          0 ≤ V''.ord (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
            (c : AlgebraicClosure ℚ))) ∧
        (∀ t', t' ∈ badPoints N q A data hKr P T V₀ →
          0 < t'.ord (R.residue₁ ⟨g, h₁⟩
            - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
                (IsLocalRing.residue A c)) → False) ∧
        (∀ t', t' ∈ badPoints N q A data hKr P T V₀ →
          0 < t'.ord (R.residue₂ ⟨g, h₂⟩
            - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
                (IsLocalRing.residue A c)) → False) ∧
        ∃ p : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
          (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
            p V = V.ord (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
              (c : AlgebraicClosure ℚ))) ∧
          Divisor.degree p = 0 := by
  intro data hKr hα hβ P R S T V₀ g h₁ h₂ hgord hfused
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  classical
  have hgood : ∀ V, V.ord g < 0 → V = V₀ ∨ goodJS N q A S V := by
    intro V hV
    by_cases hVe : V = V₀
    · exact Or.inl hVe
    · obtain ⟨⟨a, ha, hs⟩, _, _⟩ := hfused V hVe hV
      have ha' : 0 < V.ord
          ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (N * q) (jq_mem (N * q)))⟩
            : ↥(modularFunctionFieldBar (N * q)))
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
                (a : AlgebraicClosure ℚ)) := ha
      exact Or.inr ⟨a, ha', hs⟩
  have hpoleB : ∀ V, V ≠ V₀ → V.ord g < 0 →
      P.reduceFst V ∉ badPoints N q A data hKr P T V₀ ∧
        P.reduceSnd V ∉ badPoints N q A data hKr P T V₀ :=
    fun V hne hV => (hfused V hne hV).2
  have hgne : g ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at hgord
    omega

  have hexc : ∃ x : ResidueField A,
      x ∉ forbiddenSet N q A data hKr P R g h₁ h₂ T V₀ ∪ {0} := by
    by_contra hall
    push Not at hall
    exact Set.infinite_univ (α := ResidueField A)
      (Set.Finite.subset
        (forbiddenSet N q A data hKr P R g h₁ h₂ T V₀ ∪ {0}).finite_toSet
        (fun x _ => Finset.mem_coe.mpr (hall x)))
  obtain ⟨cbar, hcbar⟩ := hexc
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective cbar
  obtain ⟨hc₁, hc₂, hcd₁, hcd₂⟩ := constant_commonUnit P R c
  have h₁' : g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
      (c : AlgebraicClosure ℚ) ∈ R.R₁.integers := sub_mem h₁ hc₁
  have h₂' : g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
      (c : AlgebraicClosure ℚ) ∈ R.R₂.integers := sub_mem h₂ hc₂
  have hsub₁ : (⟨g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
      (c : AlgebraicClosure ℚ), h₁'⟩ : R.R₁.integers)
      = ⟨g, h₁⟩ - ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
          (c : AlgebraicClosure ℚ), hc₁⟩ := by
    ext
    rfl
  have hsub₂ : (⟨g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
      (c : AlgebraicClosure ℚ), h₂'⟩ : R.R₂.integers)
      = ⟨g, h₂⟩ - ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
          (c : AlgebraicClosure ℚ), hc₂⟩ := by
    ext
    rfl
  have hd₁ : R.residue₁ ⟨g - algebraMap (AlgebraicClosure ℚ)
      (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ), h₁'⟩
      = R.residue₁ ⟨g, h₁⟩
        - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
            (IsLocalRing.residue A c) := by
    rw [hsub₁, RingHom.map_sub, hcd₁]
  have hd₂ : R.residue₂ ⟨g - algebraMap (AlgebraicClosure ℚ)
      (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ), h₂'⟩
      = R.residue₂ ⟨g, h₂⟩
        - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
            (IsLocalRing.residue A c) := by
    rw [hsub₂, RingHom.map_sub, hcd₂]
  have hner₁ : R.R₁.residue ⟨g - algebraMap (AlgebraicClosure ℚ)
      (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ), h₁'⟩ ≠ 0 := by
    intro h0
    have hres0 : R.residue₁ ⟨g - algebraMap (AlgebraicClosure ℚ)
        (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ), h₁'⟩ = 0 := by
      unfold ProlongationTuple.residue₁
      rw [RingHom.comp_apply, h0, map_zero]
    rw [hd₁] at hres0
    have heq : R.residue₁ ⟨g, h₁⟩
        = algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
            (IsLocalRing.residue A c) := sub_eq_zero.mp hres0
    refine hcbar (Finset.mem_union_left _ ?_)
    unfold forbiddenSet
    refine Finset.mem_union_right _ (Finset.mem_union_left _ ?_)
    have hex : ∃ x : ResidueField A,
        R.residue₁ ⟨g, h₁⟩
          = algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) x :=
      ⟨IsLocalRing.residue A c, heq⟩
    rw [dif_pos hex]
    have hch : algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
        hex.choose
        = algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
            (IsLocalRing.residue A c) := by
      rw [← hex.choose_spec, heq]
    exact Finset.mem_singleton.mpr
      ((algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)).injective
        hch).symm
  have hner₂ : R.R₂.residue ⟨g - algebraMap (AlgebraicClosure ℚ)
      (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ), h₂'⟩ ≠ 0 := by
    intro h0
    have hres0 : R.residue₂ ⟨g - algebraMap (AlgebraicClosure ℚ)
        (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ), h₂'⟩ = 0 := by
      unfold ProlongationTuple.residue₂
      rw [RingHom.comp_apply, h0, map_zero]
    rw [hd₂] at hres0
    have heq : R.residue₂ ⟨g, h₂⟩
        = algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
            (IsLocalRing.residue A c) := sub_eq_zero.mp hres0
    refine hcbar (Finset.mem_union_left _ ?_)
    unfold forbiddenSet
    refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
    have hex : ∃ x : ResidueField A,
        R.residue₂ ⟨g, h₂⟩
          = algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) x :=
      ⟨IsLocalRing.residue A c, heq⟩
    rw [dif_pos hex]
    have hch : algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
        hex.choose
        = algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
            (IsLocalRing.residue A c) := by
      rw [← hex.choose_spec, heq]
    exact Finset.mem_singleton.mpr
      ((algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)).injective
        hch).symm

  have hpair : (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
        (c : AlgebraicClosure ℚ) ≠ 0) ∧
      V₀.ord (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
        (c : AlgebraicClosure ℚ)) = -1 := by
    by_cases hc0 : (c : AlgebraicClosure ℚ) = 0
    · rw [hc0, map_zero, sub_zero]
      exact ⟨hgne, hgord⟩
    · have hcne : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
          (c : AlgebraicClosure ℚ) ≠ 0 := (map_ne_zero _).mpr hc0
      have hordc : V₀.ord (algebraMap (AlgebraicClosure ℚ)
          (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ)) = 0 :=
        ConstantReduction.ord_algebraMap V₀ hc0
      have hord : V₀.ord (g - algebraMap (AlgebraicClosure ℚ)
          (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ)) = -1 := by
        rw [ord_sub_eq_of_ord_lt V₀ hgne hcne (by rw [hgord, hordc]; omega)]
        exact hgord
      refine ⟨fun h0 => ?_, hord⟩
      rw [h0, Place.ord_zero] at hord
      omega
  obtain ⟨hne, hordV₀⟩ := hpair

  have hpole_of : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      V.ord (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
        (c : AlgebraicClosure ℚ)) < 0 → V.ord g < 0 := by
    intro V hneg
    by_contra hge
    push Not at hge
    rcases eq_or_ne (c : AlgebraicClosure ℚ) 0 with hc0' | hc0'
    · rw [hc0', map_zero, sub_zero] at hneg
      omega
    · have h0c : V.ord (algebraMap (AlgebraicClosure ℚ)
          (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ)) = 0 :=
        ConstantReduction.ord_algebraMap V hc0'
      have hxy : g ≠ algebraMap (AlgebraicClosure ℚ)
          (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) := by
        intro he
        exact hne (by rw [he, sub_self])
      have := ord_sub_nonneg V hgne ((map_ne_zero _).mpr hc0') hxy hge (by omega)
      omega
  obtain ⟨p, hp, hpdeg⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) _ hne
  have hbase₁ : P.reduceFst V₀ ∈ badPoints N q A data hKr P T V₀ := by
    unfold badPoints
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_insert_self _ _)))
  have hbase₂ : P.reduceSnd V₀ ∈ badPoints N q A data hKr P T V₀ := by
    unfold badPoints
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
  have hmates_fst : ∀ t' , t' ∈ badPoints N q A data hKr P T V₀ →
      ∀ V'' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V'' ≠ V₀ →
      P.reduceFst V'' = t' →
      0 ≤ V''.ord (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
        (c : AlgebraicClosure ℚ)) := by
    intro t' hmem V'' hne'' hred
    by_contra hneg
    push Not at hneg
    have hgp := hpole_of V'' hneg
    exact (hpoleB V'' hne'' hgp).1 (hred ▸ hmem)
  have hmates_snd : ∀ t' , t' ∈ badPoints N q A data hKr P T V₀ →
      ∀ V'' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V'' ≠ V₀ →
      P.reduceSnd V'' = t' →
      0 ≤ V''.ord (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
        (c : AlgebraicClosure ℚ)) := by
    intro t' hmem V'' hne'' hred
    by_contra hneg
    push Not at hneg
    have hgp := hpole_of V'' hneg
    exact (hpoleB V'' hne'' hgp).2 (hred ▸ hmem)

  have hbridge₁ : ∀ t', t' ∈ badPoints N q A data hKr P T V₀ →
      0 < t'.ord (R.residue₁ ⟨g, h₁⟩
        - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
            (IsLocalRing.residue A c)) → False := by
    intro t' hmem hpos'
    refine hcbar (Finset.mem_union_left _ ?_)
    unfold forbiddenSet
    refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
    exact valOf_eq hpos' ▸ Finset.mem_image_of_mem _ hmem
  have hbridge₂ : ∀ t', t' ∈ badPoints N q A data hKr P T V₀ →
      0 < t'.ord (R.residue₂ ⟨g, h₂⟩
        - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
            (IsLocalRing.residue A c)) → False := by
    intro t' hmem hpos'
    refine hcbar (Finset.mem_union_left _ ?_)
    unfold forbiddenSet
    refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
    exact valOf_eq hpos' ▸ Finset.mem_image_of_mem _ hmem
  exact ⟨c, h₁', h₂', hd₁, hd₂, hner₁, hner₂, hne, hordV₀, hpole_of, hgood, hbase₁, hbase₂,
    hmates_fst, hmates_snd, hbridge₁, hbridge₂, p, hp, hpdeg⟩

private theorem Avoidance.commonUnit_fixed
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : ProlongationTuple P), R.IsModel → R.OrderLawFixed →
      ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N))),
      R.RegularityLaw W → (∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A)) →
      ∀ (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
        frobOnPlacesGeomLevel (ResidueField A) N data hKr
            (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V₀))
          = P.reduceFst V₀ →
        IsAffineGeomPlace (ResidueField A) N (P.reduceFst V₀) →
        P.reduceFst V₀ ∉ ssPlaces q N (ResidueField A) →
        ∀ (S : Finset (ResidueField A))
          (B : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))),
        ∃ (g : modularFunctionFieldBar (N * q))
          (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers),
          R.R₁.residue ⟨g, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨g, h₂⟩ ≠ 0 ∧ V₀.ord g = -1 ∧
          (∀ V, V ≠ V₀ → V.ord g < 0 →
            (∃ a : A, 0 < V.ord (ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ)
                (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) ∧
              IsLocalRing.residue A a ∉ S) ∧
              P.reduceFst V ∉ B ∧ P.reduceSnd V ∉ B) ∧
          (((P.reduceFst V₀).ord (R.residue₁ ⟨g, h₁⟩) = -1 ∧
              (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V₀)).ord
                (R.residue₂ ⟨g, h₂⟩) = 0) ∨
            ((P.reduceFst V₀).ord (R.residue₁ ⟨g, h₁⟩) = 0 ∧
              (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V₀)).ord
                (R.residue₂ ⟨g, h₂⟩) = -1)) := by
  intro data hKr hα hβ P R hM hO W hRL hW V₀ hfix haff hord S B
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  exact ProlongationTuple.exists_commonUnit_pole_of_reduceFst_fixed_ordinary_of_regularityLaw
    q A N (ResidueField A) (IsLocalRing.residue A) data hKr hα hβ P R hM hO W hRL hW hqN V₀ hfix haff hord S B

private theorem Avoidance.fixed_residual
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : ProlongationTuple P)
      (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N))),
      R.IsModel → R.RegularityLaw W → (∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A)) → R.OrderLawFixed →
      ∀ (S : Finset (ResidueField A)) (_ : ∀ s ∈ S, s ∉ ssJSet q (ResidueField A))
        (T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))),
        (∀ t : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N),
          ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩
              : modularFunctionFieldC (ResidueField A) N) ∉ t.toValuationSubring ∨
            ∃ s ∈ S, 0 < t.ord
              ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩
                  : modularFunctionFieldC (ResidueField A) N)
                - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) s)) →
          t ∈ T) →
        ∀ V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
          ¬ goodJS N q A S V₀ →
          frobOnPlacesGeomLevel (ResidueField A) N data hKr
              (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V₀))
            = P.reduceFst V₀ →
          IsAffineGeomPlace (ResidueField A) N (P.reduceFst V₀) →
          ∃ p : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
            Divisor.IsPrincipal p ∧ p V₀ = -1 ∧ Divisor.degree p = 0 ∧
              ∀ V ∈ p.support, V ≠ V₀ → goodJS N q A S V := by
  intro data hKr hα hβ P R W hM hRL hW hOLF S hS T hT V₀ hbad hfix haff
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  classical
  have hord : P.reduceFst V₀ ∉ ssPlaces q N (ResidueField A) := by
    intro hss
    have hssp := (isSupersingularPlace_iff q N (ResidueField A) (P.reduceFst V₀)).mp
      ((mem_ssPlaces_iff q N (ResidueField A)).mp hss)
    apply hbad
    refine goodJ_of_reduceFst_affine_goodVal N q hq hqN A hA data hKr hα hβ P S V₀ ?_ ?_
    · exact not_lt.mpr (ord_nonneg_of_mem haff.1)
    · intro s hs hpos
      change 0 < (P.reduceFst V₀).ord (jGeomGen (ResidueField A) N
        - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) s) at hpos
      have hnc : jGeomGen (ResidueField A) N
          - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
              ((P.reduceFst V₀).evalAt (jGeomGen (ResidueField A) N)) ≠ 0 := by
        intro hzero
        have hconst : jGeomGen (ResidueField A) N
            = algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
                ((P.reduceFst V₀).evalAt (jGeomGen (ResidueField A) N)) := sub_eq_zero.mp hzero
        have hpos' := hpos
        rw [hconst, ← map_sub] at hpos'
        have hne := ne_zero_of_ord_pos _ hpos'
        have hcs : (P.reduceFst V₀).evalAt (jGeomGen (ResidueField A) N) - s ≠ 0 :=
          fun h => hne (by rw [h, map_zero])
        rw [ord_algebraMap_eq_zero hcs] at hpos'
        exact lt_irrefl _ hpos'
      have hval := ord_sub_evalAt_pos_of_isRational hssp.1 haff.1 hnc
      have hseq := sep_ord_pos_gen (P.reduceFst V₀) (jGeomGen (ResidueField A) N) hpos hval
      exact hS s hs (hseq ▸ hssp.2.2)
  obtain ⟨g, h₁, h₂, hgr₁, hgr₂, hgord, hfused, hbox⟩ :=
    Avoidance.commonUnit_fixed N q hq hqN A hA data hKr hα hβ P R hM hOLF W hRL hW V₀ hfix haff hord S
      (badPoints N q A data hKr P T V₀)
  obtain ⟨c, h₁', h₂', hd₁, hd₂, hner₁, hner₂, hne, hordV₀, hpole_of, hgood, hbase₁, -,
      hmates_fst, hmates_snd, hbridge₁, hbridge₂, p, hp, hpdeg⟩ :=
    Avoidance.sectionKit N q hq hqN A hA data hKr hα hβ P R S T V₀ g h₁ h₂ hgord hfused
  have hmemBase : ∀ t'', t'' ∈ T ∪ {P.reduceFst V₀, P.reduceSnd V₀} →
      t'' ∈ badPoints N q A data hKr P T V₀ := by
    intro t'' h
    unfold badPoints
    exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
  have hmemImg : ∀ t'', t'' ∈ T ∪ {P.reduceFst V₀, P.reduceSnd V₀} →
      frobOnPlacesGeomLevel (ResidueField A) N data hKr t''
        ∈ badPoints N q A data hKr P T V₀ := by
    intro t'' h
    unfold badPoints
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ h))
  have hmemPre : ∀ s'', frobOnPlacesGeomLevel (ResidueField A) N data hKr s''
        ∈ T ∪ {P.reduceFst V₀, P.reduceSnd V₀} →
      s'' ∈ badPoints N q A data hKr P T V₀ := by
    intro s'' h
    unfold badPoints
    exact Finset.mem_union_right _ (Finset.mem_preimage.mpr h)
  have hφmem : frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V₀)
      ∈ badPoints N q A data hKr P T V₀ :=
    hmemImg _ (Finset.mem_union_right _ (Finset.mem_insert_self _ _))
  have hr1ne : R.residue₁ ⟨g, h₁⟩ ≠ 0 := by
    rw [ProlongationTuple.residue₁_apply]
    exact (map_ne_zero R.ι).mpr hgr₁
  have hr2ne : R.residue₂ ⟨g, h₂⟩ ≠ 0 := by
    rw [ProlongationTuple.residue₂_apply]
    exact (map_ne_zero R.ι).mpr hgr₂
  have hsh₁ : R.residue₁ ⟨g, h₁⟩
      - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
          (IsLocalRing.residue A c) ≠ 0 := by
    rw [← hd₁, ProlongationTuple.residue₁_apply]
    exact (map_ne_zero R.ι).mpr hner₁
  have hsh₂ : R.residue₂ ⟨g, h₂⟩
      - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
          (IsLocalRing.residue A c) ≠ 0 := by
    rw [← hd₂, ProlongationTuple.residue₂_apply]
    exact (map_ne_zero R.ι).mpr hner₂
  have hlawF := hOLF _ h₁' h₂' hner₁ hner₂ p hp (P.reduceFst V₀) hfix haff
  have hboxh : Finsupp.mapDomain P.reduceFst p (P.reduceFst V₀) = -1 := by
    rw [hlawF, hd₁, hd₂]
    rcases hbox with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
    ·
      have hA1 : (P.reduceFst V₀).ord (R.residue₁ ⟨g, h₁⟩
          - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
              (IsLocalRing.residue A c)) = -1 := by
        rcases eq_or_ne (IsLocalRing.residue A c) 0 with hc0 | hc0
        · rw [hc0, map_zero, sub_zero]
          exact hs1
        · have hcne : algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
              (IsLocalRing.residue A c) ≠ 0 := (map_ne_zero _).mpr hc0
          have hordc : (P.reduceFst V₀).ord (algebraMap (ResidueField A)
              (modularFunctionFieldC (ResidueField A) N) (IsLocalRing.residue A c)) = 0 :=
            ConstantReduction.ord_algebraMap (P.reduceFst V₀) hc0
          rw [ord_sub_eq_of_ord_lt (P.reduceFst V₀) hr1ne hcne (by rw [hs1, hordc]; omega)]
          exact hs1
      have hA2 : (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V₀)).ord
          (R.residue₂ ⟨g, h₂⟩
            - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
                (IsLocalRing.residue A c)) = 0 := by
        have hnpos : ¬ 0 < (frobOnPlacesGeomLevel (ResidueField A) N data hKr
            (P.reduceFst V₀)).ord (R.residue₂ ⟨g, h₂⟩
              - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
                  (IsLocalRing.residue A c)) :=
          fun hpos => hbridge₂ _ hφmem hpos
        rcases eq_or_ne (IsLocalRing.residue A c) 0 with hc0 | hc0
        · rw [hc0, map_zero, sub_zero]
          exact hs2
        · have hcne : algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
              (IsLocalRing.residue A c) ≠ 0 := (map_ne_zero _).mpr hc0
          have hordc : (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V₀)).ord
              (algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
                (IsLocalRing.residue A c)) = 0 :=
            ConstantReduction.ord_algebraMap _ hc0
          have hxy : R.residue₂ ⟨g, h₂⟩
              ≠ algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
                  (IsLocalRing.residue A c) := by
            intro he
            exact hsh₂ (by rw [he, sub_self])
          have hge := ord_sub_nonneg (frobOnPlacesGeomLevel (ResidueField A) N data hKr
            (P.reduceFst V₀)) hr2ne hcne hxy (le_of_eq hs2.symm) (le_of_eq hordc.symm)
          omega
      omega
    ·
      have hB1 : (P.reduceFst V₀).ord (R.residue₁ ⟨g, h₁⟩
          - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
              (IsLocalRing.residue A c)) = 0 := by
        have hnpos : ¬ 0 < (P.reduceFst V₀).ord (R.residue₁ ⟨g, h₁⟩
            - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
                (IsLocalRing.residue A c)) :=
          fun hpos => hbridge₁ _ hbase₁ hpos
        rcases eq_or_ne (IsLocalRing.residue A c) 0 with hc0 | hc0
        · rw [hc0, map_zero, sub_zero]
          exact hs1
        · have hcne : algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
              (IsLocalRing.residue A c) ≠ 0 := (map_ne_zero _).mpr hc0
          have hordc : (P.reduceFst V₀).ord (algebraMap (ResidueField A)
              (modularFunctionFieldC (ResidueField A) N) (IsLocalRing.residue A c)) = 0 :=
            ConstantReduction.ord_algebraMap (P.reduceFst V₀) hc0
          have hxy : R.residue₁ ⟨g, h₁⟩
              ≠ algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
                  (IsLocalRing.residue A c) := by
            intro he
            exact hsh₁ (by rw [he, sub_self])
          have hge := ord_sub_nonneg (P.reduceFst V₀) hr1ne hcne hxy (le_of_eq hs1.symm)
            (le_of_eq hordc.symm)
          omega
      have hB2 : (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V₀)).ord
          (R.residue₂ ⟨g, h₂⟩
            - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
                (IsLocalRing.residue A c)) = -1 := by
        rcases eq_or_ne (IsLocalRing.residue A c) 0 with hc0 | hc0
        · rw [hc0, map_zero, sub_zero]
          exact hs2
        · have hcne : algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
              (IsLocalRing.residue A c) ≠ 0 := (map_ne_zero _).mpr hc0
          have hordc : (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V₀)).ord
              (algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
                (IsLocalRing.residue A c)) = 0 :=
            ConstantReduction.ord_algebraMap _ hc0
          rw [ord_sub_eq_of_ord_lt _ hr2ne hcne (by rw [hs2, hordc]; omega)]
          exact hs2
      omega

  have hkillFibre : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      V' ≠ V₀ → P.reduceFst V' = P.reduceFst V₀ →
      ¬ 0 < V'.ord (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
          (c : AlgebraicClosure ℚ)) := by
    intro V' hne' hr hpos'
    exact mapDomain_pin P.reduceFst p (P.reduceFst V₀) V₀ V' hr hne'
      (by rw [hp V₀, hordV₀])
      (fun V'' hne'' hr'' => by
        rw [hp V'']
        exact hmates_fst _ hbase₁ V'' hne'' hr'')
      (by rw [hp V']; exact hpos') hboxh

  have hnotZ₀ : ¬ ProlongationTuple.IsZeroSide P V₀ := fun hz₀ =>
    (Avoidance.nonaffine_of_cusp N q hq hqN A hA data hKr hα hβ P V₀ (Or.inr hz₀.1)).1 haff
  have hnotSS₀ : ¬ P.IsStrictSnd V₀ := by
    intro hss₀
    refine hss₀.2 ?_
    have h := hfix
    rw [hss₀.1] at h
    exact (frobOnPlacesGeomLevel_injective (ResidueField A) N data hKr) h
  have hnz : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V' ≠ V₀ →
      P.reduceFst V' ∈ T ∪ {P.reduceFst V₀, P.reduceSnd V₀} →
      ¬ 0 < V'.ord (g - algebraMap (AlgebraicClosure ℚ)
          (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ)) := by
    intro V' hne' hmem hpos'
    by_cases hfib : P.reduceFst V' = P.reduceFst V₀
    · exact hkillFibre V' hne' hfib hpos'
    have hmemB : P.reduceFst V' ∈ badPoints N q A data hKr P T V₀ := hmemBase _ hmem
    have hpV' : 0 < p V' := by
      rw [hp V']
      exact hpos'

    have hfib_fst : ∀ V'' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        P.reduceFst V'' = P.reduceFst V' → 0 ≤ p V'' := by
      intro V'' hr
      by_cases hV₀'' : V'' = V₀
      · subst hV₀''
        exact absurd hr.symm hfib
      · rw [hp V'']
        exact hmates_fst _ hmemB V'' hV₀'' hr
    have killCusp : ProlongationTuple.IsCuspidal P V' → False := by
      intro hcusp
      rcases ProlongationTuple.isInftySide_or_isZeroSide_of_isCuspidal P hqN V' hcusp
        with hinf | hzero
      · have hlawI := hM.2.2.1 _ h₁' h₂' hner₁ hner₂ p hp V' hinf
        have hposD : 0 < Finsupp.mapDomain P.reduceFst
            (Finsupp.filter (ProlongationTuple.IsInftySide P) p) (P.reduceFst V') := by
          refine mapDomain_pos_of_mem_fiber _ _ _ V' rfl ?_ ?_
          · rw [Finsupp.filter_apply, if_pos hinf]
            exact hpV'
          · intro V'' hr
            classical
            rw [Finsupp.filter_apply]
            split
            · exact hfib_fst V'' hr
            · omega
        rw [hlawI, hd₁] at hposD
        exact hbridge₁ _ hmemB hposD
      · have hk₂ := Avoidance.componentLawSnd N q hq hqN A hA data hKr hα hβ P V' hzero
        have hmemB₂ : P.reduceSnd V' ∈ badPoints N q A data hKr P T V₀ :=
          hmemPre _ (by rw [← hk₂]; exact hmem)
        have hlawZ := hM.2.2.2 _ h₁' h₂' hner₁ hner₂ p hp V' hzero
        have hposD : 0 < Finsupp.mapDomain P.reduceSnd
            (Finsupp.filter (ProlongationTuple.IsZeroSide P) p) (P.reduceSnd V') := by
          refine mapDomain_pos_of_mem_fiber _ _ _ V' rfl ?_ ?_
          · rw [Finsupp.filter_apply, if_pos hzero]
            exact hpV'
          · intro V'' hr
            classical
            rw [Finsupp.filter_apply]
            split
            · rename_i hsfV''
              by_cases hV₀'' : V'' = V₀
              · subst hV₀''
                exact absurd hsfV'' hnotZ₀
              · rw [hp V'']
                exact hmates_snd _ hmemB₂ V'' hV₀'' hr
            · omega
        rw [hlawZ, hd₂] at hposD
        exact hbridge₂ _ hmemB₂ hposD
    rcases place_trichotomy N q hq hqN A hA data hKr hα hβ P V' with hcusp | hfixV' | hsf' | hss'
    · exact killCusp hcusp
    · by_cases hcusp' : ProlongationTuple.IsCuspidal P V'
      · exact killCusp hcusp'
      · have haff' :=
          (Avoidance.affine_of_noncusp N q hq hqN A hA data hKr hα hβ P V' hcusp').1
        have hlawF' := hOLF _ h₁' h₂' hner₁ hner₂ p hp (P.reduceFst V') hfixV' haff'
        have hposD : 0 < Finsupp.mapDomain P.reduceFst p (P.reduceFst V') := by
          refine mapDomain_pos_of_mem_fiber _ _ _ V' rfl hpV' ?_
          intro V'' hr
          exact hfib_fst V'' hr
        rw [hlawF'] at hposD
        have hone : 0 < (P.reduceFst V').ord (R.residue₁ ⟨g - algebraMap (AlgebraicClosure ℚ)
              (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ), h₁'⟩) ∨
            0 < (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V')).ord
              (R.residue₂ ⟨g - algebraMap (AlgebraicClosure ℚ)
                (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ), h₂'⟩) := by
          omega
        rcases hone with h1 | h2
        · rw [hd₁] at h1
          exact hbridge₁ _ hmemB h1
        · rw [hd₂] at h2
          exact hbridge₂ _ (hmemImg _ hmem) h2
    · have hlawS := hM.1 _ h₁' h₂' hner₁ hner₂ p hp (P.reduceFst V') hsf'.2
      have hposD : 0 < Finsupp.mapDomain P.reduceFst
          (Finsupp.filter P.IsStrictFst p) (P.reduceFst V') := by
        refine mapDomain_pos_of_mem_fiber _ _ _ V' rfl ?_ ?_
        · rw [Finsupp.filter_apply, if_pos hsf']
          exact hpV'
        · intro V'' hr
          classical
          rw [Finsupp.filter_apply]
          split
          · exact hfib_fst V'' hr
          · omega
      rw [hlawS, hd₁] at hposD
      exact hbridge₁ _ hmemB hposD
    · have hmemB₂ : P.reduceSnd V' ∈ badPoints N q A data hKr P T V₀ :=
        hmemPre _ (by rw [← hss'.1]; exact hmem)
      have hlawS2 := hM.2.1 _ h₁' h₂' hner₁ hner₂ p hp (P.reduceSnd V') hss'.2
      have hposD : 0 < Finsupp.mapDomain P.reduceSnd
          (Finsupp.filter P.IsStrictSnd p) (P.reduceSnd V') := by
        refine mapDomain_pos_of_mem_fiber _ _ _ V' rfl ?_ ?_
        · rw [Finsupp.filter_apply, if_pos hss']
          exact hpV'
        · intro V'' hr
          classical
          rw [Finsupp.filter_apply]
          split
          · rename_i hsfV''
            by_cases hV₀'' : V'' = V₀
            · subst hV₀''
              exact absurd hsfV'' hnotSS₀
            · rw [hp V'']
              exact hmates_snd _ hmemB₂ V'' hV₀'' hr
          · omega
      rw [hlawS2, hd₂] at hposD
      exact hbridge₂ _ hmemB₂ hposD
  refine ⟨p, ⟨_, hne, hp⟩, by rw [hp V₀]; exact hordV₀, hpdeg, ?_⟩
  intro V hVsupp hVne
  have hordne : V.ord (g - algebraMap (AlgebraicClosure ℚ)
      (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ)) ≠ 0 := by
    rw [← hp V]
    exact Finsupp.mem_support_iff.mp hVsupp
  rcases lt_or_gt_of_ne hordne with hneg | hposV
  ·
    have hgp := hpole_of V hneg
    rcases hgood V hgp with rfl | hgoodV
    · exact absurd rfl hVne
    · exact hgoodV
  ·
    have hnzU : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        V' ≠ V₀ → P.reduceFst V' ∈ T ∪ {P.reduceFst V₀, P.reduceSnd V₀} →
        ¬ 0 < V'.ord ((1 : ↥(modularFunctionFieldBar (N * q))) * g
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
              (c : AlgebraicClosure ℚ)) := by
      simpa [one_mul] using hnz
    exact zeros_good N q hq hqN A hA data hKr hα hβ P R W hM hRL hOLF S T hT V₀ g 1 c
      hnzU V (by simpa [one_mul] using hposV) hVne

private theorem Avoidance.step_sndBranch
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : ProlongationTuple P)
      (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N))),
      R.IsModel → R.RegularityLaw W → (∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A)) → R.OrderLawFixed →
      ∀ (S : Finset (ResidueField A))
        (T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))),
        (∀ t : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N),
          ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩
              : modularFunctionFieldC (ResidueField A) N) ∉ t.toValuationSubring ∨
            ∃ s ∈ S, 0 < t.ord
              ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩
                  : modularFunctionFieldC (ResidueField A) N)
                - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) s)) →
          t ∈ T) →
        ∀ V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
          ¬ goodJS N q A S V₀ →
          ProlongationTuple.IsZeroSide P V₀ ∨ P.IsStrictSnd V₀ →
          ∃ p : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
            Divisor.IsPrincipal p ∧ p V₀ = -1 ∧ Divisor.degree p = 0 ∧
              ∀ V ∈ p.support, V ≠ V₀ → goodJS N q A S V := by
  intro data hKr hα hβ P R W hM hRL hW hOLF S T hT V₀ _hbad htyS
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  classical
  obtain ⟨g, h₁, h₂, hgr₁, hgr₂, hgord, hfused, hsurv⟩ :=
    Avoidance.commonUnit_snd N q hq hqN A hA data hKr hα hβ P R hM hOLF W hRL hW V₀ htyS S
      (badPoints N q A data hKr P T V₀)
  obtain ⟨c, h₁', h₂', hd₁, hd₂, hner₁, hner₂, hne, hordV₀, hpole_of, hgood, -, hbase₂,
      hmates_fst, hmates_snd, hbridge₁, hbridge₂, p, hp, hpdeg⟩ :=
    Avoidance.sectionKit N q hq hqN A hA data hKr hα hβ P R S T V₀ g h₁ h₂ hgord hfused

  have hsurvh₂ : (P.reduceSnd V₀).ord (R.residue₂ ⟨g - algebraMap (AlgebraicClosure ℚ)
      (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ), h₂'⟩) = -1 := by
    rw [hd₂]
    rcases eq_or_ne (IsLocalRing.residue A c) 0 with hc0 | hc0
    · rw [hc0, map_zero, sub_zero]
      exact hsurv
    · have hr2ne : R.residue₂ ⟨g, h₂⟩ ≠ 0 := by
        intro h0
        rw [h0, Place.ord_zero] at hsurv
        omega
      have hcne : algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
          (IsLocalRing.residue A c) ≠ 0 := (map_ne_zero _).mpr hc0
      have hordc : (P.reduceSnd V₀).ord (algebraMap (ResidueField A)
          (modularFunctionFieldC (ResidueField A) N) (IsLocalRing.residue A c)) = 0 :=
        ConstantReduction.ord_algebraMap (P.reduceSnd V₀) hc0
      rw [ord_sub_eq_of_ord_lt (P.reduceSnd V₀) hr2ne hcne (by rw [hsurv, hordc]; omega)]
      exact hsurv
  have hmemBase : ∀ t'', t'' ∈ T ∪ {P.reduceFst V₀, P.reduceSnd V₀} →
      t'' ∈ badPoints N q A data hKr P T V₀ := by
    intro t'' h
    unfold badPoints
    exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
  have hmemImg : ∀ t'', t'' ∈ T ∪ {P.reduceFst V₀, P.reduceSnd V₀} →
      frobOnPlacesGeomLevel (ResidueField A) N data hKr t''
        ∈ badPoints N q A data hKr P T V₀ := by
    intro t'' h
    unfold badPoints
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ h))
  have hmemPre : ∀ s'', frobOnPlacesGeomLevel (ResidueField A) N data hKr s''
        ∈ T ∪ {P.reduceFst V₀, P.reduceSnd V₀} →
      s'' ∈ badPoints N q A data hKr P T V₀ := by
    intro s'' h
    unfold badPoints
    exact Finset.mem_union_right _ (Finset.mem_preimage.mpr h)

  have hnotI₀ : ¬ ProlongationTuple.IsInftySide P V₀ := by
    intro hi₀
    rcases htyS with hz₀ | hssV₀
    · exact ModularCurve.PlaceSpecialization.ProlongationTuple.not_isInftySide_of_isZeroSide
        P V₀ hz₀ hi₀
    · have hk := Avoidance.componentLawFst N q hq hqN A hA data hKr hα hβ P V₀ hi₀
      rw [hssV₀.1] at hk
      exact hssV₀.2 hk

  have hnotSF₀ : ¬ P.IsStrictFst V₀ := by
    intro hsf₀
    rcases htyS with hz₀ | hssV₀
    · have hk := Avoidance.componentLawSnd N q hq hqN A hA data hKr hα hβ P V₀ hz₀
      rw [← hsf₀.1] at hk
      exact hsf₀.2 hk.symm
    · have : frobOnPlacesGeomLevel (ResidueField A) N data hKr
          (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V₀))
          = P.reduceFst V₀ := by
        rw [hsf₀.1, ← hssV₀.1]
      exact hsf₀.2 this
  have hnz : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V' ≠ V₀ →
      P.reduceFst V' ∈ T ∪ {P.reduceFst V₀, P.reduceSnd V₀} →
      ¬ 0 < V'.ord (g - algebraMap (AlgebraicClosure ℚ)
          (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ)) := by
    intro V' hne' hmem hpos'
    have hmemB : P.reduceFst V' ∈ badPoints N q A data hKr P T V₀ := hmemBase _ hmem
    have hpV' : 0 < p V' := by
      rw [hp V']
      exact hpos'
    have killCusp : ProlongationTuple.IsCuspidal P V' → False := by
      intro hcusp
      rcases ProlongationTuple.isInftySide_or_isZeroSide_of_isCuspidal P hqN V' hcusp
        with hinf | hzero
      ·
        have hlawI := hM.2.2.1 _ h₁' h₂' hner₁ hner₂ p hp V' hinf
        have hposD : 0 < Finsupp.mapDomain P.reduceFst
            (Finsupp.filter (ProlongationTuple.IsInftySide P) p) (P.reduceFst V') := by
          refine mapDomain_pos_of_mem_fiber _ _ _ V' rfl ?_ ?_
          · rw [Finsupp.filter_apply, if_pos hinf]
            exact hpV'
          · intro V'' hr
            classical
            rw [Finsupp.filter_apply]
            split
            · rename_i hsfV''
              by_cases hV₀'' : V'' = V₀
              · subst hV₀''
                exact absurd hsfV'' hnotI₀
              · rw [hp V'']
                exact hmates_fst _ hmemB V'' hV₀'' hr
            · omega
        rw [hlawI, hd₁] at hposD
        exact hbridge₁ _ hmemB hposD
      ·
        have hk₂ := Avoidance.componentLawSnd N q hq hqN A hA data hKr hα hβ P V' hzero
        have hmemB₂ : P.reduceSnd V' ∈ badPoints N q A data hKr P T V₀ :=
          hmemPre _ (by rw [← hk₂]; exact hmem)
        have hlawZ := hM.2.2.2 _ h₁' h₂' hner₁ hner₂ p hp V' hzero
        by_cases hpin : P.reduceSnd V₀ = P.reduceSnd V' ∧ ProlongationTuple.IsZeroSide P V₀
        · rw [← hpin.1, hsurvh₂] at hlawZ
          exact mapDomain_filtered_pin P.reduceSnd p (ProlongationTuple.IsZeroSide P)
            (P.reduceSnd V₀) V₀ V' hpin.1.symm hne'
            (by rw [hp V₀, hordV₀])
            (fun V'' hne'' hr => by
              rw [hp V'']
              exact hmates_snd _ hbase₂ V'' hne'' hr)
            hpV' hzero hlawZ
        · have hposD : 0 < Finsupp.mapDomain P.reduceSnd
              (Finsupp.filter (ProlongationTuple.IsZeroSide P) p) (P.reduceSnd V') := by
            refine mapDomain_pos_of_mem_fiber _ _ _ V' rfl ?_ ?_
            · rw [Finsupp.filter_apply, if_pos hzero]
              exact hpV'
            · intro V'' hr
              classical
              rw [Finsupp.filter_apply]
              split
              · rename_i hsfV''
                by_cases hV₀'' : V'' = V₀
                · subst hV₀''
                  exact absurd ⟨hr, hsfV''⟩ hpin
                · rw [hp V'']
                  exact hmates_snd _ hmemB₂ V'' hV₀'' hr
              · omega
          rw [hlawZ, hd₂] at hposD
          exact hbridge₂ _ hmemB₂ hposD
    rcases place_trichotomy N q hq hqN A hA data hKr hα hβ P V' with hcusp | hfixV' | hsf' | hss'
    · exact killCusp hcusp
    ·

      by_cases hcusp' : ProlongationTuple.IsCuspidal P V'
      · exact killCusp hcusp'
      · have haff' :=
          (Avoidance.affine_of_noncusp N q hq hqN A hA data hKr hα hβ P V' hcusp').1
        have hV₀out : P.reduceFst V₀ ≠ P.reduceFst V' := by
          intro he
          rcases htyS with hz₀ | hss₀
          · exact (Avoidance.nonaffine_of_cusp N q hq hqN A hA data hKr hα hβ P V₀
              (Or.inr hz₀.1)).1 (he ▸ haff')
          · refine hss₀.2 ?_
            have h := hfixV'
            rw [← he, hss₀.1] at h
            exact (frobOnPlacesGeomLevel_injective (ResidueField A) N data hKr) h
        have hlawF' := hOLF _ h₁' h₂' hner₁ hner₂ p hp (P.reduceFst V') hfixV' haff'
        have hposD : 0 < Finsupp.mapDomain P.reduceFst p (P.reduceFst V') := by
          refine mapDomain_pos_of_mem_fiber _ _ _ V' rfl hpV' ?_
          intro V'' hr
          by_cases hV₀'' : V'' = V₀
          · subst hV₀''
            exact absurd hr hV₀out
          · rw [hp V'']
            exact hmates_fst _ hmemB V'' hV₀'' hr
        rw [hlawF'] at hposD
        have hone : 0 < (P.reduceFst V').ord (R.residue₁ ⟨g - algebraMap (AlgebraicClosure ℚ)
              (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ), h₁'⟩) ∨
            0 < (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V')).ord
              (R.residue₂ ⟨g - algebraMap (AlgebraicClosure ℚ)
                (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ), h₂'⟩) := by
          omega
        rcases hone with h1 | h2
        · rw [hd₁] at h1
          exact hbridge₁ _ hmemB h1
        · rw [hd₂] at h2
          exact hbridge₂ _ (hmemImg _ hmem) h2
    ·
      have hlawS := hM.1 _ h₁' h₂' hner₁ hner₂ p hp (P.reduceFst V') hsf'.2
      have hposD : 0 < Finsupp.mapDomain P.reduceFst
          (Finsupp.filter P.IsStrictFst p) (P.reduceFst V') := by
        refine mapDomain_pos_of_mem_fiber _ _ _ V' rfl ?_ ?_
        · rw [Finsupp.filter_apply, if_pos hsf']
          exact hpV'
        · intro V'' hr
          classical
          rw [Finsupp.filter_apply]
          split
          · rename_i hsfV''
            by_cases hV₀'' : V'' = V₀
            · subst hV₀''
              exact absurd hsfV'' hnotSF₀
            · rw [hp V'']
              exact hmates_fst _ hmemB V'' hV₀'' hr
          · omega
      rw [hlawS, hd₁] at hposD
      exact hbridge₁ _ hmemB hposD
    ·
      have hmemB₂ : P.reduceSnd V' ∈ badPoints N q A data hKr P T V₀ :=
        hmemPre _ (by rw [← hss'.1]; exact hmem)
      have hlawS2 := hM.2.1 _ h₁' h₂' hner₁ hner₂ p hp (P.reduceSnd V') hss'.2
      by_cases hpin : P.reduceSnd V₀ = P.reduceSnd V' ∧ P.IsStrictSnd V₀
      · rw [← hpin.1, hsurvh₂] at hlawS2
        exact mapDomain_filtered_pin P.reduceSnd p P.IsStrictSnd
          (P.reduceSnd V₀) V₀ V' hpin.1.symm hne'
          (by rw [hp V₀, hordV₀])
          (fun V'' hne'' hr => by
            rw [hp V'']
            exact hmates_snd _ hbase₂ V'' hne'' hr)
          hpV' hss' hlawS2
      · have hposD : 0 < Finsupp.mapDomain P.reduceSnd
            (Finsupp.filter P.IsStrictSnd p) (P.reduceSnd V') := by
          refine mapDomain_pos_of_mem_fiber _ _ _ V' rfl ?_ ?_
          · rw [Finsupp.filter_apply, if_pos hss']
            exact hpV'
          · intro V'' hr
            classical
            rw [Finsupp.filter_apply]
            split
            · rename_i hsfV''
              by_cases hV₀'' : V'' = V₀
              · subst hV₀''
                exact absurd ⟨hr, hsfV''⟩ hpin
              · rw [hp V'']
                exact hmates_snd _ hmemB₂ V'' hV₀'' hr
            · omega
        rw [hlawS2, hd₂] at hposD
        exact hbridge₂ _ hmemB₂ hposD

  refine ⟨p, ⟨_, hne, hp⟩, by rw [hp V₀]; exact hordV₀, hpdeg, ?_⟩
  intro V hVsupp hVne
  have hordne : V.ord (g - algebraMap (AlgebraicClosure ℚ)
      (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ)) ≠ 0 := by
    rw [← hp V]
    exact Finsupp.mem_support_iff.mp hVsupp
  rcases lt_or_gt_of_ne hordne with hneg | hposV
  · have hgp := hpole_of V hneg
    rcases hgood V hgp with rfl | hgoodV
    · exact absurd rfl hVne
    · exact hgoodV
  · have hnzU : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        V' ≠ V₀ → P.reduceFst V' ∈ T ∪ {P.reduceFst V₀, P.reduceSnd V₀} →
        ¬ 0 < V'.ord ((1 : ↥(modularFunctionFieldBar (N * q))) * g
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
              (c : AlgebraicClosure ℚ)) := by
      simpa [one_mul] using hnz
    exact zeros_good N q hq hqN A hA data hKr hα hβ P R W hM hRL hOLF S T hT V₀ g 1 c
      hnzU V (by simpa [one_mul] using hposV) hVne

private theorem step_removeBad
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : ProlongationTuple P)
      (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N))),
      R.IsModel → R.RegularityLaw W → (∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A)) → R.OrderLawFixed →
      ∀ (S : Finset (ResidueField A))
        (T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))),
        (∀ t : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N),
          ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩
              : modularFunctionFieldC (ResidueField A) N) ∉ t.toValuationSubring ∨
            ∃ s ∈ S, 0 < t.ord
              ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩
                  : modularFunctionFieldC (ResidueField A) N)
                - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) s)) →
          t ∈ T) →
        ∀ V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
          ¬ goodJS N q A S V₀ →
          (ProlongationTuple.IsInftySide P V₀ ∨ P.IsStrictFst V₀) ∨
            (ProlongationTuple.IsZeroSide P V₀ ∨ P.IsStrictSnd V₀) →
          ∃ p : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
            Divisor.IsPrincipal p ∧ p V₀ = -1 ∧ Divisor.degree p = 0 ∧
              ∀ V ∈ p.support, V ≠ V₀ → goodJS N q A S V := by
  intro data hKr hα hβ P R W hM hRL hW hOLF S T hT V₀ _hbad hty
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  classical
  rcases hty with htyF | htyS
  ·
    obtain ⟨g, h₁, h₂, hgr₁, hgr₂, hgord, hfused, hsurv⟩ :=
      Avoidance.commonUnit_fst N q hq hqN A hA data hKr hα hβ P R hM hOLF W hRL hW V₀ htyF S
        (badPoints N q A data hKr P T V₀)
    obtain ⟨c, h₁', h₂', hd₁, hd₂, hner₁, hner₂, hne, hordV₀, hpole_of, hgood, hbase₁, -,
        hmates_fst, hmates_snd, hbridge₁, hbridge₂, p, hp, hpdeg⟩ :=
      Avoidance.sectionKit N q hq hqN A hA data hKr hα hβ P R S T V₀ g h₁ h₂ hgord hfused

    have hsurvh : (P.reduceFst V₀).ord (R.residue₁ ⟨g - algebraMap (AlgebraicClosure ℚ)
        (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ), h₁'⟩) = -1 := by
      rw [hd₁]
      rcases eq_or_ne (IsLocalRing.residue A c) 0 with hc0 | hc0
      · rw [hc0, map_zero, sub_zero]
        exact hsurv
      · have hr1ne : R.residue₁ ⟨g, h₁⟩ ≠ 0 := by
          intro h0
          rw [h0, Place.ord_zero] at hsurv
          omega
        have hcne : algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
            (IsLocalRing.residue A c) ≠ 0 := (map_ne_zero _).mpr hc0
        have hordc : (P.reduceFst V₀).ord (algebraMap (ResidueField A)
            (modularFunctionFieldC (ResidueField A) N) (IsLocalRing.residue A c)) = 0 :=
          ConstantReduction.ord_algebraMap (P.reduceFst V₀) hc0
        rw [ord_sub_eq_of_ord_lt (P.reduceFst V₀) hr1ne hcne (by rw [hsurv, hordc]; omega)]
        exact hsurv
    have hmemBase : ∀ t'', t'' ∈ T ∪ {P.reduceFst V₀, P.reduceSnd V₀} →
        t'' ∈ badPoints N q A data hKr P T V₀ := by
      intro t'' h
      unfold badPoints
      exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
    have hmemImg : ∀ t'', t'' ∈ T ∪ {P.reduceFst V₀, P.reduceSnd V₀} →
        frobOnPlacesGeomLevel (ResidueField A) N data hKr t''
          ∈ badPoints N q A data hKr P T V₀ := by
      intro t'' h
      unfold badPoints
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ h))
    have hmemPre : ∀ s'', frobOnPlacesGeomLevel (ResidueField A) N data hKr s''
          ∈ T ∪ {P.reduceFst V₀, P.reduceSnd V₀} →
        s'' ∈ badPoints N q A data hKr P T V₀ := by
      intro s'' h
      unfold badPoints
      exact Finset.mem_union_right _ (Finset.mem_preimage.mpr h)
    have hnotZ₀ : ¬ ProlongationTuple.IsZeroSide P V₀ := by
      intro hz₀
      rcases htyF with hinfV₀ | hstrV₀
      · exact ModularCurve.PlaceSpecialization.ProlongationTuple.not_isInftySide_of_isZeroSide
          P V₀ hz₀ hinfV₀
      · have hk := Avoidance.componentLawSnd N q hq hqN A hA data hKr hα hβ P V₀ hz₀
        rw [← hstrV₀.1] at hk
        exact hstrV₀.2 hk.symm

    have hnotSS₀ : ¬ P.IsStrictSnd V₀ := by
      intro hss₀
      rcases htyF with hinfV₀ | hstrV₀
      · have hk := Avoidance.componentLawFst N q hq hqN A hA data hKr hα hβ P V₀ hinfV₀
        refine hss₀.2 ?_
        calc frobOnPlacesGeomLevel (ResidueField A) N data hKr
              (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceSnd V₀))
            = frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V₀) := by
              rw [← hss₀.1]
          _ = P.reduceSnd V₀ := hk
      · have : frobOnPlacesGeomLevel (ResidueField A) N data hKr
            (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V₀))
            = P.reduceFst V₀ := by
          rw [hstrV₀.1, ← hss₀.1]
        exact hstrV₀.2 this
    have hnz : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V' ≠ V₀ →
        P.reduceFst V' ∈ T ∪ {P.reduceFst V₀, P.reduceSnd V₀} →
        ¬ 0 < V'.ord (g - algebraMap (AlgebraicClosure ℚ)
            (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ)) := by
      intro V' hne' hmem hpos'
      have hmemB : P.reduceFst V' ∈ badPoints N q A data hKr P T V₀ := hmemBase _ hmem
      have hpV' : 0 < p V' := by
        rw [hp V']
        exact hpos'

      have killCusp : ProlongationTuple.IsCuspidal P V' → False := by
        intro hcusp
        rcases ProlongationTuple.isInftySide_or_isZeroSide_of_isCuspidal P hqN V' hcusp
          with hinf | hzero
        ·
          have hlawI := hM.2.2.1 _ h₁' h₂' hner₁ hner₂ p hp V' hinf
          by_cases hpin : P.reduceFst V₀ = P.reduceFst V' ∧ ProlongationTuple.IsInftySide P V₀
          · rw [← hpin.1, hsurvh] at hlawI
            exact mapDomain_filtered_pin P.reduceFst p (ProlongationTuple.IsInftySide P)
              (P.reduceFst V₀) V₀ V' hpin.1.symm hne'
              (by rw [hp V₀, hordV₀])
              (fun V'' hne'' hr => by
                rw [hp V'']
                exact hmates_fst _ hbase₁ V'' hne'' hr)
              hpV' hinf hlawI
          · have hposD : 0 < Finsupp.mapDomain P.reduceFst
                (Finsupp.filter (ProlongationTuple.IsInftySide P) p) (P.reduceFst V') := by
              refine mapDomain_pos_of_mem_fiber _ _ _ V' rfl ?_ ?_
              · rw [Finsupp.filter_apply, if_pos hinf]
                exact hpV'
              · intro V'' hr
                classical
                rw [Finsupp.filter_apply]
                split
                · rename_i hsfV''
                  by_cases hV₀'' : V'' = V₀
                  · subst hV₀''
                    exact absurd ⟨hr, hsfV''⟩ hpin
                  · rw [hp V'']
                    exact hmates_fst _ hmemB V'' hV₀'' hr
                · omega
            rw [hlawI, hd₁] at hposD
            exact hbridge₁ _ hmemB hposD
        ·
          have hk₂ := Avoidance.componentLawSnd N q hq hqN A hA data hKr hα hβ P V' hzero
          have hmemB₂ : P.reduceSnd V' ∈ badPoints N q A data hKr P T V₀ :=
            hmemPre _ (by rw [← hk₂]; exact hmem)
          have hlawZ := hM.2.2.2 _ h₁' h₂' hner₁ hner₂ p hp V' hzero
          have hposD : 0 < Finsupp.mapDomain P.reduceSnd
              (Finsupp.filter (ProlongationTuple.IsZeroSide P) p) (P.reduceSnd V') := by
            refine mapDomain_pos_of_mem_fiber _ _ _ V' rfl ?_ ?_
            · rw [Finsupp.filter_apply, if_pos hzero]
              exact hpV'
            · intro V'' hr
              classical
              rw [Finsupp.filter_apply]
              split
              · rename_i hsfV''
                by_cases hV₀'' : V'' = V₀
                · subst hV₀''
                  exact absurd hsfV'' hnotZ₀
                · rw [hp V'']
                  exact hmates_snd _ hmemB₂ V'' hV₀'' hr
              · omega
          rw [hlawZ, hd₂] at hposD
          exact hbridge₂ _ hmemB₂ hposD
      rcases place_trichotomy N q hq hqN A hA data hKr hα hβ P V' with hcusp | hfixV' | hsf' | hss'
      · exact killCusp hcusp
      ·

        by_cases hcusp' : ProlongationTuple.IsCuspidal P V'
        · exact killCusp hcusp'
        · have haff := (Avoidance.affine_of_noncusp N q hq hqN A hA data hKr hα hβ P V' hcusp').1

          have hV₀out : P.reduceFst V₀ ≠ P.reduceFst V' := by
            intro he
            rcases htyF with hinfV₀ | hstrV₀
            · exact (Avoidance.nonaffine_of_cusp N q hq hqN A hA data hKr hα hβ P V₀ (Or.inl hinfV₀.1)).1
                (he ▸ haff)
            · exact hstrV₀.2 (by rw [he]; exact hfixV')
          have hlawF := hOLF _ h₁' h₂' hner₁ hner₂ p hp (P.reduceFst V') hfixV' haff
          have hposD : 0 < Finsupp.mapDomain P.reduceFst p (P.reduceFst V') := by
            refine mapDomain_pos_of_mem_fiber _ _ _ V' rfl hpV' ?_
            intro V'' hr
            by_cases hV₀'' : V'' = V₀
            · subst hV₀''
              exact absurd hr hV₀out
            · rw [hp V'']
              exact hmates_fst _ hmemB V'' hV₀'' hr
          rw [hlawF] at hposD
          have hone : 0 < (P.reduceFst V').ord (R.residue₁ ⟨g - algebraMap (AlgebraicClosure ℚ)
                (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ), h₁'⟩) ∨
              0 < (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V')).ord
                (R.residue₂ ⟨g - algebraMap (AlgebraicClosure ℚ)
                  (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ), h₂'⟩) := by
            omega
          rcases hone with h1 | h2
          · rw [hd₁] at h1
            exact hbridge₁ _ hmemB h1
          · rw [hd₂] at h2
            exact hbridge₂ _ (hmemImg _ hmem) h2
      ·
        have hlawS := hM.1 _ h₁' h₂' hner₁ hner₂ p hp (P.reduceFst V') hsf'.2
        by_cases hpin : P.reduceFst V₀ = P.reduceFst V' ∧ P.IsStrictFst V₀
        · rw [← hpin.1, hsurvh] at hlawS
          exact mapDomain_filtered_pin P.reduceFst p P.IsStrictFst
            (P.reduceFst V₀) V₀ V' hpin.1.symm hne'
            (by rw [hp V₀, hordV₀])
            (fun V'' hne'' hr => by
              rw [hp V'']
              exact hmates_fst _ hbase₁ V'' hne'' hr)
            hpV' hsf' hlawS
        · have hposD : 0 < Finsupp.mapDomain P.reduceFst
              (Finsupp.filter P.IsStrictFst p) (P.reduceFst V') := by
            refine mapDomain_pos_of_mem_fiber _ _ _ V' rfl ?_ ?_
            · rw [Finsupp.filter_apply, if_pos hsf']
              exact hpV'
            · intro V'' hr
              classical
              rw [Finsupp.filter_apply]
              split
              · rename_i hsfV''
                by_cases hV₀'' : V'' = V₀
                · subst hV₀''
                  exact absurd ⟨hr, hsfV''⟩ hpin
                · rw [hp V'']
                  exact hmates_fst _ hmemB V'' hV₀'' hr
              · omega
          rw [hlawS, hd₁] at hposD
          exact hbridge₁ _ hmemB hposD
      ·
        have hmemB₂ : P.reduceSnd V' ∈ badPoints N q A data hKr P T V₀ :=
          hmemPre _ (by rw [← hss'.1]; exact hmem)
        have hlawS2 := hM.2.1 _ h₁' h₂' hner₁ hner₂ p hp (P.reduceSnd V') hss'.2
        have hposD : 0 < Finsupp.mapDomain P.reduceSnd
            (Finsupp.filter P.IsStrictSnd p) (P.reduceSnd V') := by
          refine mapDomain_pos_of_mem_fiber _ _ _ V' rfl ?_ ?_
          · rw [Finsupp.filter_apply, if_pos hss']
            exact hpV'
          · intro V'' hr
            classical
            rw [Finsupp.filter_apply]
            split
            · rename_i hsfV''
              by_cases hV₀'' : V'' = V₀
              · subst hV₀''
                exact absurd hsfV'' hnotSS₀
              · rw [hp V'']
                exact hmates_snd _ hmemB₂ V'' hV₀'' hr
            · omega
        rw [hlawS2, hd₂] at hposD
        exact hbridge₂ _ hmemB₂ hposD
    refine ⟨p, ⟨_, hne, hp⟩, by rw [hp V₀]; exact hordV₀, hpdeg, ?_⟩
    intro V hVsupp hVne
    have hordne : V.ord (g - algebraMap (AlgebraicClosure ℚ)
        (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ)) ≠ 0 := by
      rw [← hp V]
      exact Finsupp.mem_support_iff.mp hVsupp
    rcases lt_or_gt_of_ne hordne with hneg | hposV
    ·
      have hgp := hpole_of V hneg
      rcases hgood V hgp with rfl | hgoodV
      · exact absurd rfl hVne
      · exact hgoodV
    ·
      have hnzU : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
          V' ≠ V₀ → P.reduceFst V' ∈ T ∪ {P.reduceFst V₀, P.reduceSnd V₀} →
          ¬ 0 < V'.ord ((1 : ↥(modularFunctionFieldBar (N * q))) * g
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
                (c : AlgebraicClosure ℚ)) := by
        simpa [one_mul] using hnz
      exact zeros_good N q hq hqN A hA data hKr hα hβ P R W hM hRL hOLF S T hT V₀ g 1 c
        hnzU V (by simpa [one_mul] using hposV) hVne
  ·
    exact Avoidance.step_sndBranch N q hq hqN A hA data hKr hα hβ P R W hM hRL hW hOLF
      S T hT V₀ _hbad htyS

theorem solution
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (_ : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : ProlongationTuple P),
      R.IsModel → R.RegularityLaw W → R.OrderLawFixed →
      ∀ (S : Finset (ResidueField A)) (_ : ∀ s ∈ S, s ∉ ssJSet q (ResidueField A))
        (x : JZero (N * q)),
        ∃ E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
          Pic0.mk E = x ∧
            ∀ V ∈ (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
              ∃ a : A,
                0 < V.ord
                    (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                          (modularFunctionField_le_full (N * q) (jq_mem (N * q)))⟩
                      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
                          (a : AlgebraicClosure ℚ)) ∧
                  IsLocalRing.residue A a ∉ S := by
  intro W hW data hKr hα hβ P R hM hRL hOLF S hS x
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  classical
  obtain ⟨T, hT⟩ := exists_badSet N q hq hqN A hA S
  obtain ⟨D₀, hmk⟩ := Pic0.mk_surjective x
  obtain ⟨e, hep, hedeg, hegood⟩ :=
    Avoidance.avoid_exists_isPrincipal_degree_forall_support
      (goodJS N q A S)
      (fun V₀ hbad => by
        classical
        by_cases hnode : frobOnPlacesGeomLevel (ResidueField A) N data hKr
              (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V₀))
            = P.reduceFst V₀ ∧
          IsAffineGeomPlace (ResidueField A) N (P.reduceFst V₀)
        ·
          exact Avoidance.fixed_residual N q hq hqN A hA data hKr hα hβ P R W hM hRL hW hOLF
            S hS T hT V₀ hbad hnode.1 hnode.2
        · exact step_removeBad N q hq hqN A hA data hKr hα hβ P R W hM hRL hW hOLF S T hT V₀ hbad
            (Avoidance.badTypology_nonnode N q hq hqN A hA data hKr hα hβ P S T V₀
              (Or.inr (Or.inr hbad)) hnode))
      (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
  have hEdeg : ((D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) + e)
      ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))) := by
    rw [Divisor.mem_degZero, map_add, hedeg, add_zero]
    exact Divisor.mem_degZero.mp D₀.2
  refine ⟨⟨_, hEdeg⟩, ?_, ?_⟩
  · rw [← hmk]
    symm
    show QuotientAddGroup.mk D₀ = QuotientAddGroup.mk
      (⟨_, hEdeg⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
        (F := ↥(modularFunctionFieldBar (N * q)))))
    refine QuotientAddGroup.eq.mpr ?_
    rw [AddSubgroup.mem_addSubgroupOf]
    have hco : ((-D₀ + ⟨_, hEdeg⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
        (F := ↥(modularFunctionFieldBar (N * q))))) : Divisor (AlgebraicClosure ℚ)
        (modularFunctionFieldBar (N * q))) = e := by
      push_cast
      abel
    rw [hco]
    exact Divisor.mem_principal.mpr hep
  · intro V hV
    exact hegood V hV

end S_ModularCurve_PlaceSpecialization_exists_rep_forall_exists_ord_sub_pos_residue_notMem_of_isModel_of_regularityLaw_of_orderLawFixed_of_ssPlaces
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_rep_forall_exists_ord_sub_pos_residue_notMem_of_isModel_of_regularityLaw_of_orderLawFixed_of_ssPlaces (solution)
