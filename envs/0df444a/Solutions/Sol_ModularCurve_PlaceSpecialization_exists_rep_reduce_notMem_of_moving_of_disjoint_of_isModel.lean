-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_rep_reduce_notMem_of_moving_of_disjoint_of_isModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/bc2f5553-df25-5b69-9ab2-35ad5d32f202

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Definitions.Def_AlgebraicCurve_GluedPic0
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_rep_forall_exists_ord_sub_pos_residue_notMem_of_isModel_of_regularityLaw_of_orderLawFixed_of_ssPlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_rep_reduce_notMem_of_moving_of_disjoint_of_isModel
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.numberField_of_finiteDimensional"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one HahnSeries.ramScale_apply ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply"
p2m_attr_erase "simp" "WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄"
p2m_attr_erase "simp" "TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.symPoly_zero ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

private theorem ne_zero_of_ord_pos {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (h : 0 < v.ord f) : f ≠ 0 := by
  rintro rfl
  rw [Place.ord_zero] at h
  exact lt_irrefl 0 h

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

private theorem redFst_ord_pos_of_ord_pos
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
      (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (a : A),
      0 < V.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full (N * q) (jq_mem (N * q)))⟩ : modularFunctionFieldBar (N * q))
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) →
      0 < (P.reduceFst V).ord ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N)
          - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) (IsLocalRing.residue A a)) := by
  intro data hKr hα hβ P V a ha
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
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
  exact P.d0_j _ a hre

noncomputable section

private def Phi2Fin.jbar (K : Type*) [Field K] (N : ℕ) [NeZero N] : modularFunctionFieldC K N :=
  ⟨jqModC K, jqModC_mem K N⟩

private theorem Phi2Fin.transcendental_jbar (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    Transcendental K (Phi2Fin.jbar K N) := by
  have h := transcendental_jqModC K
  rw [show jqModC K = ((modularFunctionFieldC K N).val (Phi2Fin.jbar K N)) from rfl,
    Transcendental, isAlgebraic_algHom_iff (modularFunctionFieldC K N).val
      (modularFunctionFieldC K N).val.injective] at h
  exact h

private theorem Phi2Fin.jbar_sub_algebraMap_ne_zero (K : Type*) [Field K] (N : ℕ) [NeZero N] (a : K) :
    Phi2Fin.jbar K N - algebraMap K (modularFunctionFieldC K N) a ≠ 0 := fun h0 =>
  Phi2Fin.transcendental_jbar K N ((sub_eq_zero.mp h0) ▸ isAlgebraic_algebraMap a)

end

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

private theorem ord_nonneg_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F]
    {w : Place K F} {f : F} (hf : f ∈ w.toValuationSubring) : 0 ≤ w.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp [Place.ord_zero]
  · by_contra hneg
    push_neg at hneg
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

private theorem mem_of_ord_sub_pos {K F : Type*} [Field K] [Field F] [Algebra K F]
    {w : Place K F} {g : F} {c : K}
    (h : 0 < w.ord (g - algebraMap K F c)) : g ∈ w.toValuationSubring := by
  rcases eq_or_ne (g - algebraMap K F c) 0 with hz | hnz
  · rw [sub_eq_zero.mp hz]
    exact w.algebraMap_mem' c
  · have hmem : g - algebraMap K F c ∈ w.toValuationSubring := by
      rcases w.toValuationSubring.mem_or_inv_mem (g - algebraMap K F c) with hin | hinv
      · exact hin
      · exfalso
        have h1 : 0 ≤ w.ord (g - algebraMap K F c)⁻¹ := ord_nonneg_of_mem hinv
        rw [Place.ord_inv] at h1
        omega
    have := add_mem hmem (w.algebraMap_mem' c)
    simpa using this

private theorem isRational_downstairs (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N]
    (t : Place K (modularFunctionFieldC K N)) : t.IsRational := by
  haveI : IsCurveOver K (modularFunctionFieldC K N) :=
    isCurveOver_modularFunctionFieldC_of_perfectField K N
  haveI : Module.Finite K t.ResidueField :=
    Module.finite_of_finrank_eq_succ (n := 0) (IsCurveOver.deg_eq_one_of_isAlgClosed t)
  haveI : Algebra.IsIntegral K t.ResidueField := Algebra.IsIntegral.of_finite K t.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K)).2

private theorem mem_W_of_ord_sub_pos_of_mem_ssJSet
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (t : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)) (c : ResidueField A),
      0 < t.ord ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c) → c ∈ ssJSet q (ResidueField A) → t ∈ W := by
  intro W hW data hKr t c hc hss
  have _ := data
  have _ := hKr
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  have hrat : t.IsRational := isRational_downstairs (ResidueField A) N t
  have hjmem : jGeomGen (ResidueField A) N ∈ t.toValuationSubring := mem_of_ord_sub_pos hc
  obtain ⟨dataN⟩ := ModularCurve.nonempty_modularPolynomialData N
  have haff : IsAffineGeomPlace (ResidueField A) N t := by
    unfold IsAffineGeomPlace
    exact ⟨hjmem, jNGeomGen_mem_of_jGeomGen_mem dataN t hjmem⟩
  have hev : 0 < t.ord ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) (t.evalAt (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N))) :=
    ord_sub_evalAt_pos_of_isRational hrat hjmem (Phi2Fin.jbar_sub_algebraMap_ne_zero (ResidueField A) N _)
  have heq : t.evalAt (jGeomGen (ResidueField A) N) = c := sep_ord_pos_gen t _ hev hc
  refine (hW t).mpr ?_
  show IsSupersingularPlace q N (ResidueField A) t
  unfold IsSupersingularPlace
  refine ⟨hrat, haff, ?_⟩
  rw [heq]
  exact hss

private theorem frob_mem_W_iff
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (w : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)),
      frobOnPlacesGeomLevel (ResidueField A) N data hKr w ∈ W ↔ w ∈ W := by
  intro W hW data hKr w
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  classical
  have hfwd : ∀ u ∈ W, frobOnPlacesGeomLevel (ResidueField A) N data hKr u ∈ W := by
    intro u hu
    have h := arithFrobC_smul_mem_ssPlaces q N (ResidueField A) u ((hW u).mp hu)
    rw [arithFrobC_smul_eq_frobOnPlacesGeomLevel q (ResidueField A) N data hKr u] at h
    exact (hW _).mpr h
  have hinj := frobOnPlacesGeomLevel_injective (ResidueField A) N data hKr
  have himg : W.image (frobOnPlacesGeomLevel (ResidueField A) N data hKr) = W := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro y hy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
      exact hfwd u hu
    · rw [Finset.card_image_of_injective _ hinj]
  constructor
  · intro h
    rw [← himg] at h
    obtain ⟨u, hu, hEq⟩ := Finset.mem_image.mp h
    exact hinj hEq ▸ hu
  · intro h
    exact hfwd w h

open Classical in

private theorem SupportAvoidance.redPair_mem_W_or_notMem_of_ord_pos_of_valOf_notMem
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (X : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (a : A),
      0 < V.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full (N * q) (jq_mem (N * q)))⟩ : modularFunctionFieldBar (N * q))
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) →
      IsLocalRing.residue A a ∉
        ((((X ∪ (X).image (frobOnPlacesGeomLevel (ResidueField A) N data hKr))
            ∪ (X).preimage (frobOnPlacesGeomLevel (ResidueField A) N data hKr) (Set.injOn_of_injective (frobOnPlacesGeomLevel_injective (ResidueField A) N data hKr))).filter
          (fun t => t ∉ W ∧ ∃ c : ResidueField A, 0 < t.ord ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c))).image
        (valOf (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N))) →
      (P.reduceFst V ∈ W ∧ P.reduceSnd V ∈ W) ∨ (P.reduceFst V ∉ X ∧ P.reduceSnd V ∉ X) := by
  intro W hW data hKr hα hβ P X V a ha hnot
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  classical
  have hfst : 0 < (P.reduceFst V).ord ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N)
      - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) (IsLocalRing.residue A a)) :=
    redFst_ord_pos_of_ord_pos N q hq hqN A hA data hKr hα hβ P V a ha
  have hvfst : valOf (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) (P.reduceFst V) = IsLocalRing.residue A a :=
    valOf_eq hfst
  by_cases hw : P.reduceFst V ∈ W
  · left
    refine ⟨hw, ?_⟩
    rcases P.d1 V with hrel | hrel
    · have hrel1 : P.reduceFst V = frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceSnd V) := hrel
      rw [hrel1] at hw
      exact (frob_mem_W_iff N q hq hqN A hA W hW data hKr (P.reduceSnd V)).mp hw
    · have hrel2 : frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V) = P.reduceSnd V := hrel
      rw [← hrel2]
      exact (frob_mem_W_iff N q hq hqN A hA W hW data hKr (P.reduceFst V)).mpr hw
  · right
    have hnotin : P.reduceFst V ∉
        (X ∪ X.image (frobOnPlacesGeomLevel (ResidueField A) N data hKr)) ∪ X.preimage (frobOnPlacesGeomLevel (ResidueField A) N data hKr) (Set.injOn_of_injective (frobOnPlacesGeomLevel_injective (ResidueField A) N data hKr)) := by
      intro hin
      refine hnot (hvfst ▸ Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hin, hw, ⟨_, hfst⟩⟩))
    constructor
    · intro hin
      exact hnotin (Finset.mem_union_left _ (Finset.mem_union_left _ hin))
    · intro hin
      rcases P.d1 V with hrel | hrel
      · have hrel1 : P.reduceFst V = frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceSnd V) := hrel
        exact hnotin (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hin, hrel1.symm⟩)))
      · have hrel2 : frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V) = P.reduceSnd V := hrel
        exact hnotin (Finset.mem_union_right _ (Finset.mem_preimage.mpr (hrel2 ▸ hin)))

open Classical in

private theorem SupportAvoidance.forall_mem_filtered_notMem_ssJSet
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (X : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N))),
      ∀ s ∈ ((((X ∪ (X).image (frobOnPlacesGeomLevel (ResidueField A) N data hKr))
            ∪ (X).preimage (frobOnPlacesGeomLevel (ResidueField A) N data hKr) (Set.injOn_of_injective (frobOnPlacesGeomLevel_injective (ResidueField A) N data hKr))).filter
          (fun t => t ∉ W ∧ ∃ c : ResidueField A, 0 < t.ord ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c))).image
        (valOf (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N))), s ∉ ssJSet q (ResidueField A) := by
  intro W hW data hKr X s hs hss
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  classical
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨-, htW, c, hc⟩ := Finset.mem_filter.mp ht
  rw [valOf_eq hc] at hss
  exact htW (mem_W_of_ord_sub_pos_of_mem_ssJSet N q hq hqN A hA W hW data hKr t c hc hss)

private theorem SupportAvoidance.forall_T_of_tuple

    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : ProlongationTuple P),
      R.IsModel → R.RegularityLaw W → R.OrderLawFixed →
      ∀ (T : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N))) (hTW : ∀ w ∈ T, w ∉ W) (x : JZero (N * q)),
        ∃ E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
          Pic0.mk E = x ∧
            ∀ V ∈ (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
              P.reduceFst V ∉ T ∧ P.reduceSnd V ∉ T := by
  intro W hW data hKr hα hβ P R hM hRL hOLF T hTW x
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  classical
  obtain ⟨E, hmk, hE⟩ :=
    ModularCurve.PlaceSpecialization.exists_rep_forall_exists_ord_sub_pos_residue_notMem_of_isModel_of_regularityLaw_of_orderLawFixed_of_ssPlaces N q hq hqN A hA W hW data hKr hα hβ P R hM hRL hOLF
      ((((T ∪ (T).image (frobOnPlacesGeomLevel (ResidueField A) N data hKr))
          ∪ (T).preimage (frobOnPlacesGeomLevel (ResidueField A) N data hKr) (Set.injOn_of_injective (frobOnPlacesGeomLevel_injective (ResidueField A) N data hKr))).filter
        (fun t => t ∉ W ∧ ∃ c : ResidueField A, 0 < t.ord ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c))).image
      (valOf (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N)))
      (SupportAvoidance.forall_mem_filtered_notMem_ssJSet N q hq hqN A hA W hW data hKr T) x
  refine ⟨E, hmk, fun V hV => ?_⟩
  obtain ⟨a, haord, hanot⟩ := hE V hV
  rcases SupportAvoidance.redPair_mem_W_or_notMem_of_ord_pos_of_valOf_notMem N q hq hqN A hA W hW data hKr hα hβ P T V a haord hanot with ⟨hwF, hwS⟩ | ⟨hnF, hnS⟩
  · exact ⟨fun h => hTW _ h hwF, fun h => hTW _ h hwS⟩
  · exact ⟨hnF, hnS⟩

theorem solution
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hO : R.OrderLawFixed),
        (∀ T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)),
          ∃ E₀ C₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
            (∀ V, 0 ≤ E₀ V) ∧ P.IsGoodDiv E₀ ∧
              (∀ V ∈ E₀.support, P.reduceFst V ∉ T ∧ P.reduceSnd V ∉ T) ∧
                0 < Divisor.degree E₀ ∧ (∀ V, 0 ≤ C₀ V) ∧
                  (∀ σ ∈ A.inertiaSubgroupIn ℚ,
                    arithmeticGalois (modularFunctionFieldFull (N * q)) σ • C₀ = C₀) ∧
                    0 < Divisor.degree C₀ ∧ Divisor.IsPrincipal (E₀ - C₀)) →
          ∀ (T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))),
          (∀ w ∈ T, w ∉ W) →
          ∀ x : JZero (N * q),
            ∃ (E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                  (F := ↥(modularFunctionFieldBar (N * q))))),
              Pic0.mk E = x ∧
                ∀ V ∈ (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
                  P.reduceFst V ∉ T ∧ P.reduceSnd V ∉ T := by
  intro W hW data hKr hα hβ P R hR hRL hO heng T hTW x
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  have _ := heng
  exact SupportAvoidance.forall_T_of_tuple N q hq hqN A hA W hW data hKr hα hβ P R hR hRL hO T hTW x

#print axioms solution

end S_ModularCurve_PlaceSpecialization_exists_rep_reduce_notMem_of_moving_of_disjoint_of_isModel
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_rep_reduce_notMem_of_moving_of_disjoint_of_isModel (solution)
