-- Prove2me | solution 1 for ModularCurve.FullLevel.tube_of_isRational_of_forall_rational_cuspRegular_evalAt_sub_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/acb38274-15bb-54c8-b47c-1aaac07d02f2

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_ModularCurve_FinitePlaceLift
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord
import Theorems.Thm_ModularCurve_CompEq_finrank_adjoin_jBar_eq_dedekindPsi
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_AlgebraicCurve_ConstantReduction_isPointwise_of_hasPrincipalDivisors
import Theorems.Thm_ModularCurve_FullLevel_exists_rational_integral_cuspRegular_evalAt_ne_of_isRational_of_ne
import Theorems.Thm_ModularCurve_isAffineGeomPlace_or_ord_jGeomGen_lt_zero
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_tube_of_isRational_of_forall_rational_cuspRegular_evalAt_sub_mem_maximalIdeal
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X"
p2m_attr_erase "simp" "AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ProjectiveLine.map_mk ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open AlgebraicCurve ModularCurve IsLocalRing

namespace P2mTubeTest

local notation "Qb" => AlgebraicClosure ℚ

section Divisors

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem degree_eq_sum_of_deg_eq_one (hdeg : ∀ v : Place K F, v.deg = 1) (D : Divisor K F) :
    Divisor.degree D = D.sum fun _ n => n := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun v _ => ?_
  simp [hdeg v]

theorem eq_of_le_of_degree_eq (hdeg : ∀ v : Place K F, v.deg = 1) {D D' : Divisor K F} (hle : D ≤ D')
    (hdegD : Divisor.degree D = Divisor.degree D') : D = D' := by
  classical
  have hE : 0 ≤ D' - D := fun v => by
    have := hle v
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_sub, Pi.sub_apply]
    omega
  have hdeg0 : Divisor.degree (D' - D) = 0 := by rw [map_sub, hdegD, sub_self]
  rw [degree_eq_sum_of_deg_eq_one hdeg] at hdeg0
  have hzero : D' - D = 0 := by
    ext v
    by_contra hv
    have hvpos : 0 < (D' - D) v := lt_of_le_of_ne (hE v) (Ne.symm hv)
    have hmem : v ∈ (D' - D).support := Finsupp.mem_support_iff.mpr hv
    have hsum : (D' - D) v ≤ (D' - D).sum fun _ n => n := by
      rw [Finsupp.sum]
      exact Finset.single_le_sum (f := fun w => (D' - D) w) (fun w _ => hE w) hmem
    omega
  have := sub_eq_zero.mp hzero
  exact this.symm

theorem le_mapDomain_apply {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F']
    (r : Place K F → Place K' F') {D : Divisor K F} (hD : 0 ≤ D) (P : Place K F) :
    D P ≤ Finsupp.mapDomain r D (r P) := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  simp only [Finsupp.single_apply]
  have hnn : ∀ a, 0 ≤ (if r a = r P then D a else 0) := fun a => by
    split_ifs
    · exact hD a
    · exact le_rfl
  by_cases hP : P ∈ D.support
  · have h1 : D P = (if r P = r P then D P else 0) := by simp
    rw [h1]
    exact Finset.single_le_sum (f := fun a => if r a = r P then D a else 0) (fun a _ => hnn a) hP
  · rw [Finsupp.notMem_support_iff.mp hP]
    exact Finset.sum_nonneg fun a _ => hnn a

end Divisors

section Bar

variable (N : ℕ) [NeZero N]

abbrev jF : ↥(modularFunctionFieldBar N) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩

theorem coeffEmb_jq_eq_jqModC (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L jq = jqModC L :=
  map_jqModC (algebraMap ℚ L)

theorem jF_ne_zero : jF N ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : ↥(modularFunctionFieldBar N) => (z : LaurentSeries Qb).coeff (-1)) h
  simp only [ZeroMemClass.coe_zero, HahnSeries.coeff_zero] at h1
  rw [coeffEmb_coeff, coeff_jq_neg_one, map_one] at h1
  exact one_ne_zero h1

theorem transcendental_jF : Transcendental Qb (jF N) := transcendental_coeffEmb_jq Qb N

scoped instance isCurveOver_bar : IsCurveOver Qb ↥(modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N

scoped instance hasPrincipalDivisors_bar : HasPrincipalDivisors Qb ↥(modularFunctionFieldBar N) :=
  IsCurveOver.hasPrincipalDivisors

scoped instance finiteDimensional_lSpace_zero_bar :
    FiniteDimensional Qb ↥(LSpace (0 : Divisor Qb ↥(modularFunctionFieldBar N))) := by
  have hC : ConstantsAreBase Qb ↥(modularFunctionFieldBar N) :=
    constantsAreBase_of_deg_eq_one (cuspInftyBar N) (deg_eq_one_modularFunctionFieldBar N _)
  rw [show LSpace (0 : Divisor Qb ↥(modularFunctionFieldBar N)) = _ from hC]
  infer_instance

scoped instance finiteDimensional_adjoin_jF :
    FiniteDimensional (IntermediateField.adjoin Qb ({jF N} : Set ↥(modularFunctionFieldBar N)))
      ↥(modularFunctionFieldBar N) :=
  finiteDimensional_adjoin_coeffEmb_jq_of_neZero N

theorem finrank_adjoin_jF :
    Module.finrank (IntermediateField.adjoin Qb ({jF N} : Set ↥(modularFunctionFieldBar N)))
      ↥(modularFunctionFieldBar N) = dedekindPsi N :=
  CompEq.finrank_adjoin_jBar_eq_dedekindPsi N

theorem degree_poleDivisor_jF (E₀ : Divisor Qb ↥(modularFunctionFieldBar N))
    (hE₀ : ∀ v, E₀ v = max 0 (-(v.ord (jF N)))) : Divisor.degree E₀ = dedekindPsi N := by
  rw [Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord (jF N) (transcendental_jF N) E₀ hE₀, finrank_adjoin_jF]

end Bar

section Red

theorem finrank_adjoin_transport {L : Type*} [Field L]
    {E E' : IntermediateField L (LaurentSeries L)} (h : E = E')
    {x : LaurentSeries L} (hx : x ∈ E) (hx' : x ∈ E') :
    Module.finrank (IntermediateField.adjoin L ({⟨x, hx⟩} : Set E)) E =
      Module.finrank (IntermediateField.adjoin L ({⟨x, hx'⟩} : Set E')) E' := by
  subst h; rfl

variable (κ : Type*) [Field κ] (N : ℕ) [NeZero N]

abbrev jC : ↥(modularFunctionFieldC κ N) := ⟨jqModC κ, jqModC_mem κ N⟩

theorem jC_eq_jGeomGen : jC κ N = jGeomGen κ N := rfl

theorem transcendental_jC : Transcendental κ (jC κ N) := fun h =>
  transcendental_jqModC κ
    ((isAlgebraic_algHom_iff (modularFunctionFieldC κ N).val Subtype.val_injective).mpr h)

theorem jC_ne_zero : jC κ N ≠ 0 := fun h => transcendental_jC κ N (h ▸ isAlgebraic_zero)

theorem finrank_adjoin_jC (q : ℕ) [Fact q.Prime] [CharP κ q] (hqN : ¬ q ∣ N) :
    Module.finrank (IntermediateField.adjoin κ ({jC κ N} : Set ↥(modularFunctionFieldC κ N)))
      ↥(modularFunctionFieldC κ N) = dedekindPsi N := by
  have hN : (N : κ) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff κ q] at h0
    exact hqN h0
  rw [finrank_adjoin_transport (modularFunctionFieldC_eq_modularFunctionFieldFullC κ q N hqN)
    (jqModC_mem κ N) (jqModC_mem_full κ N)]
  exact finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi κ N hN

end Red

section PlaceLemmas

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isRational_of_isCurveOver [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) : v.IsRational := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

theorem residue_mk_algebraMap (v : Place K F) (c : K) :
    IsLocalRing.residue v.toValuationSubring ⟨algebraMap K F c, v.algebraMap_mem' c⟩ =
      algebraMap K v.ResidueField c := by
  rw [IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField, IsLocalRing.ResidueField.algebraMap_eq]
  rfl

theorem evalAt_eq_of_algebraMap_eq (v : Place K F) (hv : v.IsRational) {x : F} (hx : x ∈ v.toValuationSubring)
    {c : K} (h : algebraMap K v.ResidueField c = IsLocalRing.residue v.toValuationSubring ⟨x, hx⟩) :
    v.evalAt x = c := by
  apply (algebraMap K v.ResidueField).injective
  rw [v.algebraMap_evalAt hv hx, h]

theorem evalAt_sub_algebraMap (v : Place K F) (hv : v.IsRational) {x : F} (hx : x ∈ v.toValuationSubring) (c : K) :
    v.evalAt (x - algebraMap K F c) = v.evalAt x - c := by
  have hmem : x - algebraMap K F c ∈ v.toValuationSubring := sub_mem hx (v.algebraMap_mem' c)
  refine evalAt_eq_of_algebraMap_eq v hv hmem ?_
  have hcoe : (⟨x - algebraMap K F c, hmem⟩ : v.toValuationSubring) =
      ⟨x, hx⟩ - ⟨algebraMap K F c, v.algebraMap_mem' c⟩ := Subtype.ext rfl
  rw [hcoe, map_sub, map_sub, v.algebraMap_evalAt hv hx, residue_mk_algebraMap]

theorem evalAt_add_algebraMap (v : Place K F) (hv : v.IsRational) {x : F} (hx : x ∈ v.toValuationSubring) (c : K) :
    v.evalAt (x + algebraMap K F c) = v.evalAt x + c := by
  have hmem : x + algebraMap K F c ∈ v.toValuationSubring := add_mem hx (v.algebraMap_mem' c)
  refine evalAt_eq_of_algebraMap_eq v hv hmem ?_
  have hcoe : (⟨x + algebraMap K F c, hmem⟩ : v.toValuationSubring) =
      ⟨x, hx⟩ + ⟨algebraMap K F c, v.algebraMap_mem' c⟩ := Subtype.ext rfl
  rw [hcoe, map_add, map_add, v.algebraMap_evalAt hv hx, residue_mk_algebraMap]

theorem evalAt_mul (v : Place K F) (hv : v.IsRational) {x y : F} (hx : x ∈ v.toValuationSubring)
    (hy : y ∈ v.toValuationSubring) : v.evalAt (x * y) = v.evalAt x * v.evalAt y := by
  have hmem : x * y ∈ v.toValuationSubring := mul_mem hx hy
  refine evalAt_eq_of_algebraMap_eq v hv hmem ?_
  have hcoe : (⟨x * y, hmem⟩ : v.toValuationSubring) = ⟨x, hx⟩ * ⟨y, hy⟩ := Subtype.ext rfl
  rw [hcoe, map_mul, map_mul, v.algebraMap_evalAt hv hx, v.algebraMap_evalAt hv hy]

theorem evalAt_eq_zero_iff_ord_pos (v : Place K F) (hv : v.IsRational) {x : F} (hx : x ∈ v.toValuationSubring)
    (hx0 : x ≠ 0) : v.evalAt x = 0 ↔ 0 < v.ord x := by
  rw [← v.mem_maximalIdeal_iff_ord_pos hx0 hx, ← IsLocalRing.residue_eq_zero_iff,
    ← v.algebraMap_evalAt hv hx, map_eq_zero_iff _ (algebraMap K v.ResidueField).injective]

theorem residue_mk_eq_zero_iff_ord_pos (v : Place K F) {x : F} (hx : x ∈ v.toValuationSubring) (hx0 : x ≠ 0) :
    IsLocalRing.residue v.toValuationSubring ⟨x, hx⟩ = 0 ↔ 0 < v.ord x := by
  rw [IsLocalRing.residue_eq_zero_iff, v.mem_maximalIdeal_iff_ord_pos hx0 hx]

theorem mem_of_ord_nonneg' (v : Place K F) {x : F} (h : 0 ≤ v.ord x) : x ∈ v.toValuationSubring := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact zero_mem _
  · exact (Place.mem_iff_ord_nonneg v hx0).mpr h

end PlaceLemmas

section Algebraic

open ModularCurve.FullLevel

theorem isAlgebraic_fieldBar (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M') :
    letI := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    Algebra.IsAlgebraic ↥(modularFunctionFieldBar M') ↥(fieldBar q M') := by
  letI alg : Algebra ↥(modularFunctionFieldBar M') ↥(fieldBar q M') :=
    (IntermediateField.inclusion hle).toRingHom.toAlgebra
  set ι : ↥(modularFunctionFieldBar M') →ₐ[Qb] ↥(fieldBar q M') := IntermediateField.inclusion hle with hιdef
  have hιalg : ∀ x, algebraMap ↥(modularFunctionFieldBar M') ↥(fieldBar q M') x = ι x := fun _ => rfl

  have hCF' := ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField Qb (q ^ 2 * M')
    (ModularCurve.FullLevel.levelH q M')
  haveI : IsCurveOver Qb ↥(fieldBar q M') := hCF'.1
  haveI : Algebra.EssFiniteType Qb ↥(fieldBar q M') := hCF'.2

  set j' : ↥(fieldBar q M') := ι (jF M') with hj'def
  have hj't : Transcendental Qb j' := fun h =>
    transcendental_jF M' ((isAlgebraic_algHom_iff ι (IntermediateField.inclusion_injective hle)).mp h)
  haveI hfin : FiniteDimensional (IntermediateField.adjoin Qb ({j'} : Set ↥(fieldBar q M'))) ↥(fieldBar q M') :=
    IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType hj't
  haveI halgJ : Algebra.IsAlgebraic (IntermediateField.adjoin Qb ({j'} : Set ↥(fieldBar q M'))) ↥(fieldBar q M') :=
    Algebra.IsAlgebraic.of_finite _ _

  have hJ : (IntermediateField.adjoin Qb ({j'} : Set ↥(fieldBar q M'))).toSubalgebra ≤ ι.range := by
    rw [← AlgHom.fieldRange_toSubalgebra]
    exact IntermediateField.toSubalgebra_le_toSubalgebra.mpr
      (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr ⟨jF M', rfl⟩))
  set e := AlgEquiv.ofInjective ι (IntermediateField.inclusion_injective hle) with hedef
  let φ : ↥(IntermediateField.adjoin Qb ({j'} : Set ↥(fieldBar q M'))) →ₐ[Qb] ↥(modularFunctionFieldBar M') :=
    e.symm.toAlgHom.comp (Subalgebra.inclusion hJ)
  have hφ : ∀ z, ι (φ z) = (z : ↥(fieldBar q M')) := by
    intro z
    have h1 : (e (e.symm (Subalgebra.inclusion hJ z)) : ↥(fieldBar q M')) = ι (e.symm (Subalgebra.inclusion hJ z)) :=
      AlgEquiv.ofInjective_apply ι _ _
    rw [AlgEquiv.apply_symm_apply] at h1
    rw [show φ z = e.symm (Subalgebra.inclusion hJ z) from rfl, ← h1]
    rfl
  refine ⟨fun x => ?_⟩
  obtain ⟨p, hp0, hpx⟩ := halgJ.isAlgebraic x
  refine ⟨p.map φ.toRingHom, ?_, ?_⟩
  · exact (Polynomial.map_ne_zero_iff φ.toRingHom.injective).mpr hp0
  · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hcomp : (algebraMap ↥(modularFunctionFieldBar M') ↥(fieldBar q M')).comp φ.toRingHom =
        algebraMap ↥(IntermediateField.adjoin Qb ({j'} : Set ↥(fieldBar q M'))) ↥(fieldBar q M') := by
      refine RingHom.ext fun z => ?_
      rw [RingHom.comp_apply, hιalg]
      exact hφ z
    rw [hcomp, ← Polynomial.aeval_def, hpx]

end Algebraic

section Transport

theorem pole_zero_transport
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring Qb) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hj : jF M' ∈ R₀.integers) (hjres : R₀.residue ⟨jF M', hj⟩ = jC (ResidueField A) M') :
    (∀ P : Place Qb ↥(modularFunctionFieldBar M'),
        0 ≤ (R₀.placeMap P).ord (jC (ResidueField A) M') → 0 ≤ P.ord (jF M')) ∧
    (∀ P : Place Qb ↥(modularFunctionFieldBar M'),
        0 < P.ord (jF M') → 0 < (R₀.placeMap P).ord (jC (ResidueField A) M')) := by
  classical

  haveI hκ : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : PerfectField (ResidueField A) := IsAlgClosed.perfectField _
  haveI : CharP (ResidueField A) q := by
    have hq0 : ((q : ℕ) : ResidueField A) = 0 := by
      have hqm : (⟨(q : AlgebraicClosure ℚ), natCast_mem A q⟩ : A) ∈ maximalIdeal A := by
        rw [ValuationSubring.valuation_lt_one_iff]
        exact (A.mem_nonunits_iff).mp hA
      have : IsLocalRing.residue A ⟨(q : AlgebraicClosure ℚ), natCast_mem A q⟩ = 0 :=
        (IsLocalRing.residue_eq_zero_iff _).mpr hqm
      rw [← map_natCast (IsLocalRing.residue A) q]
      convert this using 2
      rfl
    exact (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).mpr hq0
  haveI : IsCurveOver (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M') :=
    isCurveOver_modularFunctionFieldC_of_perfectField (ResidueField A) M'
  haveI : HasPrincipalDivisors (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M') :=
    IsCurveOver.hasPrincipalDivisors
  have hdeg1 : ∀ w : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M'), w.deg = 1 :=
    IsCurveOver.deg_eq_one_of_isAlgClosed
  haveI : FiniteDimensional (ResidueField A)
      ↥(LSpace (0 : Divisor (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M'))) := by
    have hC : ConstantsAreBase (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M') :=
      constantsAreBase_of_deg_eq_one (R₀.placeMap (cuspInftyBar M')) (hdeg1 _)
    rw [show LSpace (0 : Divisor (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')) = _ from hC]
    infer_instance
  haveI : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A)
        ({jC (ResidueField A) M'} : Set ↥(modularFunctionFieldC (ResidueField A) M')))
      ↥(modularFunctionFieldC (ResidueField A) M') :=
    Module.finite_of_finrank_pos (by
      rw [finrank_adjoin_jC (ResidueField A) M' q hqM']; exact dedekindPsi_pos M' (NeZero.ne M'))

  obtain ⟨Dj, hDj, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (jF M') (jF_ne_zero M')
  set E₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') :=
    Finsupp.mapRange (fun n : ℤ => max 0 (-n)) (by simp) Dj with hE₀def
  set Z₀ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') :=
    Finsupp.mapRange (fun n : ℤ => max 0 n) (by simp) Dj with hZ₀def
  have hE₀ : ∀ P, E₀ P = max 0 (-(P.ord (jF M'))) := fun P => by
    rw [hE₀def, Finsupp.mapRange_apply, hDj P]
  have hZ₀ : ∀ P, Z₀ P = max 0 (P.ord (jF M')) := fun P => by
    rw [hZ₀def, Finsupp.mapRange_apply, hDj P]
  have hDjZE : Dj = Z₀ - E₀ := by
    ext P
    rw [Finsupp.sub_apply, hZ₀, hE₀, hDj]
    omega
  have hE₀nn : 0 ≤ E₀ := fun P => by rw [hE₀]; exact le_max_left _ _
  have hZ₀nn : 0 ≤ Z₀ := fun P => by rw [hZ₀]; exact le_max_left _ _

  set r := R₀.placeMap with hr
  have hjbar0 : R₀.residue ⟨jF M', hj⟩ ≠ 0 := by
    rw [hjres]; exact jC_ne_zero (ResidueField A) M'
  have hjbar : ∀ Q, Finsupp.mapDomain r Dj Q = Q.ord (jC (ResidueField A) M') := by
    intro Q; rw [← hjres]; exact R₀.mapDomain_placeMap ⟨jF M', hj⟩ hjbar0 Dj hDj Q

  obtain ⟨Djb, hDjb, -⟩ := HasPrincipalDivisors.exists_divisor (K := ResidueField A)
    (jC (ResidueField A) M') (jC_ne_zero (ResidueField A) M')
  set Eb : Divisor (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M') :=
    Finsupp.mapRange (fun n : ℤ => max 0 (-n)) (by simp) Djb with hEbdef
  set Zb : Divisor (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M') :=
    Finsupp.mapRange (fun n : ℤ => max 0 n) (by simp) Djb with hZbdef
  have hEb : ∀ Q, Eb Q = max 0 (-(Q.ord (jC (ResidueField A) M'))) := fun Q => by
    rw [hEbdef, Finsupp.mapRange_apply, hDjb Q]
  have hZb : ∀ Q, Zb Q = max 0 (Q.ord (jC (ResidueField A) M')) := fun Q => by
    rw [hZbdef, Finsupp.mapRange_apply, hDjb Q]
  have hDjbZE : Djb = Zb - Eb := by
    ext Q
    rw [Finsupp.sub_apply, hZb, hEb, hDjb]
    omega

  have hkey : Finsupp.mapDomain r E₀ = Eb := by
    symm
    refine eq_of_le_of_degree_eq hdeg1 ?_ ?_
    · intro Q
      have h1 : Finsupp.mapDomain r Z₀ Q - Finsupp.mapDomain r E₀ Q = Q.ord (jC (ResidueField A) M') := by
        rw [← Finsupp.sub_apply, ← Finsupp.mapDomain_sub, ← hDjZE]
        exact hjbar Q
      have h2 : 0 ≤ Finsupp.mapDomain r Z₀ Q := (Finsupp.mapDomain_nonneg hZ₀nn) Q
      have h3 : 0 ≤ Finsupp.mapDomain r E₀ Q := (Finsupp.mapDomain_nonneg hE₀nn) Q
      rw [hEb]
      exact max_le h3 (by omega)
    · rw [R₀.degree_mapDomain, degree_poleDivisor_jF M' E₀ hE₀,
        Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord (jC (ResidueField A) M')
          (transcendental_jC (ResidueField A) M') Eb hEb,
        finrank_adjoin_jC (ResidueField A) M' q hqM']

  have hkeyZ : Finsupp.mapDomain r Z₀ = Zb := by
    have h1 : Finsupp.mapDomain r Dj = Djb := Finsupp.ext fun Q => by rw [hjbar Q, hDjb Q]
    rw [hDjZE, Finsupp.mapDomain_sub, hkey, hDjbZE] at h1
    exact sub_left_injective h1
  constructor
  · intro P hP
    by_contra hneg
    push Not at hneg
    have hE₀P : 0 < E₀ P := by
      rw [hE₀]
      exact lt_max_of_lt_right (by omega)
    have h1 := le_mapDomain_apply r hE₀nn P
    rw [hkey, hEb, max_eq_left (by omega)] at h1
    omega
  · intro P hP
    have hZ₀P : 0 < Z₀ P := by
      rw [hZ₀]
      exact lt_max_of_lt_right hP
    have h1 := le_mapDomain_apply r hZ₀nn P
    rw [hkeyZ, hZb] at h1
    rcases le_or_gt ((R₀.placeMap P).ord (jC (ResidueField A) M')) 0 with h | h
    · rw [max_eq_left h] at h1
      omega
    · exact h

end Transport

end P2mTubeTest
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tube_of_isRational_of_forall_rational_cuspRegular_evalAt_sub_mem_maximalIdeal.P2mTubeTest"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tube_of_isRational_of_forall_rational_cuspRegular_evalAt_sub_mem_maximalIdeal.P2mTubeTest"

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups
open P2mTubeTest

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)
    (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')) (hP : P.IsRational)

    (htest : ∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
          ∃ h : P.evalAt (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
            (⟨_, h⟩ : A) ∈ maximalIdeal A) :

    ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
            (⟨_, h⟩ : A) ∈ maximalIdeal A := by
  classical

  haveI hκ : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : PerfectField (ResidueField A) := IsAlgClosed.perfectField _
  haveI : IsCurveOver (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M') :=
    isCurveOver_modularFunctionFieldC_of_perfectField (ResidueField A) M'
  have hratF : ∀ v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'), v.IsRational :=
    fun v => isRational_of_isCurveOver v
  have hratC : ∀ w : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M'), w.IsRational :=
    fun w => isRational_of_isCurveOver w

  have hjq : coeffMap A.subtype (jqModC A) = coeffEmb (AlgebraicClosure ℚ) jq :=
    (map_jqModC _).trans (coeffEmb_jq_eq_jqModC (AlgebraicClosure ℚ)).symm
  have hyj : coeffMap A.subtype (jqModC A) ∈ modularFunctionFieldBar M' := by
    rw [hjq]; exact (jF M').2
  obtain ⟨hj0, hjres0⟩ := hR₀ (jqModC A) hyj
  have hjFeq : (⟨coeffMap A.subtype (jqModC A), hyj⟩ : ↥(modularFunctionFieldBar M')) = jF M' :=
    Subtype.ext hjq
  have hj : jF M' ∈ R₀.integers := hjFeq ▸ hj0
  have hjres : R₀.residue ⟨jF M', hj⟩ = jC (ResidueField A) M' := by
    have heq : (⟨⟨coeffMap A.subtype (jqModC A), hyj⟩, hj0⟩ : R₀.integers) = ⟨jF M', hj⟩ :=
      Subtype.ext hjFeq
    rw [← heq]
    apply Subtype.ext
    rw [hjres0]
    exact map_jqModC _

  set sP : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M') :=
    ((s : ↥W) : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M')) with hsPdef
  have hs : IsSupersingularPlace q M' (ResidueField A) sP := (hW _).mp s.2
  obtain ⟨hsrat, hsaff, hsj⟩ := hs
  have hjs : jC (ResidueField A) M' ∈ sP.toValuationSubring := hsaff.1
  obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective (R := A) (sP.evalAt (jC (ResidueField A) M'))
  intro f hf hfreg hfs a ha

  letI alg : Algebra ↥(modularFunctionFieldBar M') ↥(fieldBar q M') :=
    (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') ↥(fieldBar q M') :=
    IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion hle).commutes x).symm
  haveI : Algebra.IsAlgebraic ↥(modularFunctionFieldBar M') ↥(fieldBar q M') := isAlgebraic_fieldBar q M' hle
  haveI : Algebra.IsIntegral ↥(modularFunctionFieldBar M') ↥(fieldBar q M') :=
    Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  have hincl : ∀ x : ↥(modularFunctionFieldBar M'),
      (IntermediateField.inclusion hle x : ↥(fieldBar q M')) = algebraMap _ ↥(fieldBar q M') x := fun _ => rfl
  set P' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') := P.restrict ↥(modularFunctionFieldBar M')
    with hP'def
  have hP'rat : P'.IsRational := hratF P'
  have hmemP' : ∀ x : ↥(modularFunctionFieldBar M'),
      x ∈ P'.toValuationSubring ↔ (IntermediateField.inclusion hle x : ↥(fieldBar q M')) ∈ P.toValuationSubring := by
    intro x
    rw [hincl x]
    exact Place.mem_restrict_iff P
  have hevalP' : ∀ x : ↥(modularFunctionFieldBar M'), x ∈ P'.toValuationSubring →
      P.evalAt (IntermediateField.inclusion hle x : ↥(fieldBar q M')) = P'.evalAt x :=
    fun x hx => Place.evalAt_algebraMap_eq_evalAt_restrict P hP'rat hx

  have htest' : ∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
      (∀ Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'), 0 ≤ Q.ord (jF M') →
        0 ≤ Q.ord (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M'))) →
      R₀.residue ⟨_, hgi⟩ ∈ sP.toValuationSubring →
      ∃ (hP' : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ P'.toValuationSubring)
        (hA : P'.evalAt ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ ∈ A),
        IsLocalRing.residue A ⟨_, hA⟩ = sP.evalAt (R₀.residue ⟨_, hgi⟩) := by
    intro g hg hgi hgreg hgs
    obtain ⟨hmem, hval⟩ := htest g hg hgi hgreg hgs
    have hmem' := (hmemP' _).mpr hmem
    obtain ⟨b, hb⟩ := IsLocalRing.residue_surjective (R := A) (sP.evalAt (R₀.residue ⟨_, hgi⟩))
    obtain ⟨hdA, hdm⟩ := hval b hb
    have key := hevalP' _ hmem'
    have hdA' : P'.evalAt ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ - (b : AlgebraicClosure ℚ) ∈ A := by
      rw [← key]; exact hdA
    have hA : P'.evalAt ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ ∈ A := by
      have := add_mem hdA' b.2
      simpa using this
    refine ⟨hmem', hA, ?_⟩
    rw [← hb]
    apply Ideal.Quotient.eq.mpr
    have hsplit : (⟨_, hA⟩ : ↥A) - b = ⟨_, hdA⟩ := by
      apply Subtype.ext
      show P'.evalAt _ - (b : AlgebraicClosure ℚ) = P.evalAt _ - (b : AlgebraicClosure ℚ)
      rw [key]
    rw [hsplit]; exact hdm

  obtain ⟨hjP', hjA, hjval⟩ := htest' jq (modularFunctionField_le_full M' (jq_mem M')) hj (fun Q h => h) (hjres ▸ hjs)

  have hPW : R₀.IsPointwise := ConstantReduction.isPointwise_of_hasPrincipalDivisors R₀
  obtain ⟨hFIB, hZER⟩ := pole_zero_transport q M' hqM' A hA R₀ hj hjres
  set r := R₀.placeMap with hrdef

  have hs''j : 0 ≤ (r P').ord (jC (ResidueField A) M') := by
    by_contra hneg
    push Not at hneg
    have hjunit : IsUnit (⟨jF M', hj⟩ : R₀.integers) :=
      R₀.toRegularProlongation.isUnit_of_residue_ne_zero (f := ⟨jF M', hj⟩)
        (by rw [ConstantReduction.toRegularProlongation_residue, hjres]; exact jC_ne_zero _ M')
    have hv1 : R₀.integers.valuation (jF M' : ↥(modularFunctionFieldBar M')) = 1 := by
      have := R₀.integers.valuation_unit hjunit.unit
      rwa [IsUnit.unit_spec] at this
    have hjinv : (jF M')⁻¹ ∈ R₀.integers := by
      rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, hv1, inv_one]
    have hjinvres : R₀.residue ⟨(jF M')⁻¹, hjinv⟩ = (jC (ResidueField A) M')⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← hjres, ← map_mul]
      have : (⟨(jF M')⁻¹, hjinv⟩ * ⟨jF M', hj⟩ : R₀.integers) = 1 :=
        Subtype.ext (inv_mul_cancel₀ (jF_ne_zero M'))
      rw [this, map_one]
    have hfib : ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'), r w = r P' →
        (jF M')⁻¹ ∈ w.toValuationSubring := by
      intro w hw
      apply mem_of_ord_nonneg'
      rw [Place.ord_inv]
      by_contra h'
      push Not at h'
      have := hZER w (by omega)
      rw [hw] at this
      omega
    obtain ⟨hm, hval, heq⟩ := hPW P' hP'rat (jF M')⁻¹ hjinv hfib
    have hres0 : IsLocalRing.residue (r P').toValuationSubring ⟨R₀.residue ⟨(jF M')⁻¹, hjinv⟩, hm⟩ = 0 := by
      have hm' : (jC (ResidueField A) M')⁻¹ ∈ (r P').toValuationSubring := hjinvres ▸ hm
      have : (⟨R₀.residue ⟨(jF M')⁻¹, hjinv⟩, hm⟩ : (r P').toValuationSubring) = ⟨(jC (ResidueField A) M')⁻¹, hm'⟩ :=
        Subtype.ext hjinvres
      rw [this, residue_mk_eq_zero_iff_ord_pos _ hm' (inv_ne_zero (jC_ne_zero (ResidueField A) M')), Place.ord_inv]
      omega
    rw [hres0, map_eq_zero_iff _ (algebraMap (ResidueField A) _).injective, IsLocalRing.residue_eq_zero_iff] at heq
    have hjinvP' : (jF M')⁻¹ ∈ P'.toValuationSubring := hfib P' rfl
    have hprod : P'.evalAt (jF M') * P'.evalAt (jF M')⁻¹ = 1 := by
      rw [← evalAt_mul P' hP'rat hjP' hjinvP', mul_inv_cancel₀ (jF_ne_zero M'), Place.evalAt_one]
    have h1 : (1 : A) ∈ maximalIdeal A := by
      have : (⟨P'.evalAt (jF M'), hjA⟩ : A) * ⟨P'.evalAt (jF M')⁻¹, hval⟩ = 1 := Subtype.ext hprod
      rw [← this]
      exact Ideal.mul_mem_left _ _ heq
    exact (maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

  have hfibreg : ∀ x : ↥(modularFunctionFieldBar M'),
      (∀ Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'), 0 ≤ Q.ord (jF M') → 0 ≤ Q.ord x) →
      ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'), r w = r P' → x ∈ w.toValuationSubring := by
    intro x hx w hw
    apply mem_of_ord_nonneg'
    apply hx
    apply hFIB
    rw [hw]
    exact hs''j

  have hpw : ∀ (x : ↥(modularFunctionFieldBar M')) (hxint : x ∈ R₀.integers),
      (∀ Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'), 0 ≤ Q.ord (jF M') → 0 ≤ Q.ord x) →
      ∃ (hm : R₀.residue ⟨x, hxint⟩ ∈ (r P').toValuationSubring) (h : P'.evalAt x ∈ A),
        x ∈ P'.toValuationSubring ∧
        (r P').evalAt (R₀.residue ⟨x, hxint⟩) = (IsLocalRing.residue A ⟨_, h⟩ : ResidueField A) := by
    intro x hxint hx
    obtain ⟨hm, h, heq⟩ := hPW P' hP'rat x hxint (hfibreg x hx)
    exact ⟨hm, h, hfibreg x hx P' rfl, evalAt_eq_of_algebraMap_eq (r P') (hratC _) hm heq⟩

  obtain ⟨hmj, hjA2, -, hjeq⟩ := hpw (jF M') hj (fun Q h => h)
  have hevj : (r P').evalAt (jC (ResidueField A) M') = sP.evalAt (jC (ResidueField A) M') := by
    rw [← hjres, hjeq, ← hjval]
  have hjrP' : jC (ResidueField A) M' ∈ (r P').toValuationSubring := mem_of_ord_nonneg' _ hs''j
  have haff : IsAffineGeomPlace (ResidueField A) M' (r P') :=
    (isAffineGeomPlace_or_ord_jGeomGen_lt_zero (ResidueField A) M' (r P')).resolve_right (not_lt.mpr hs''j)
  have hss : r P' ∈ ssPlaces q M' (ResidueField A) := by
    refine ⟨hratC _, haff, ?_⟩
    rw [show jGeomGen (ResidueField A) M' = jC (ResidueField A) M' from rfl, hevj]
    exact hsj
  have hmemW : r P' ∈ W := (hW _).mpr hss

  have hrs : r P' = sP := by
    by_contra hne
    obtain ⟨g, hg, hgi, hgreg, hgs, hgs', hgne⟩ :=
      ModularCurve.FullLevel.exists_rational_integral_cuspRegular_evalAt_ne_of_isRational_of_ne q M' hqM' A hA R₀ hR₀
        sP (r P') hsrat (hratC _) hjs hjrP' (Ne.symm hne)
    obtain ⟨hgP', hgA, hgval⟩ := htest' g hg hgi hgreg hgs
    obtain ⟨hmg, hg', -, hgeq⟩ := hpw _ hgi hgreg
    apply hgne
    rw [← hgval, hgeq]

  obtain ⟨hmf, hfA, hfP', hfeq⟩ := hpw f hf hfreg
  rw [hrs] at hfeq
  have hresEq : IsLocalRing.residue A ⟨P'.evalAt f, hfA⟩ = IsLocalRing.residue A a := by
    rw [← hfeq, ← ha]
  have hsub : (⟨P'.evalAt f, hfA⟩ : A) - a ∈ maximalIdeal A := by
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact hresEq
  have hPf : P.evalAt (IntermediateField.inclusion hle f : ↥(fieldBar q M')) = P'.evalAt f := hevalP' f hfP'
  have hmemA : P.evalAt (IntermediateField.inclusion hle f : ↥(fieldBar q M')) - (a : AlgebraicClosure ℚ) ∈ A := by
    rw [hPf]; exact sub_mem hfA a.2
  refine ⟨hmemA, ?_⟩
  have : (⟨_, hmemA⟩ : A) = ⟨P'.evalAt f, hfA⟩ - a := Subtype.ext (by simp [hPf])
  rw [this]
  exact hsub

end S_ModularCurve_FullLevel_tube_of_isRational_of_forall_rational_cuspRegular_evalAt_sub_mem_maximalIdeal
end P2MW
export P2MW.S_ModularCurve_FullLevel_tube_of_isRational_of_forall_rational_cuspRegular_evalAt_sub_mem_maximalIdeal (solution)
