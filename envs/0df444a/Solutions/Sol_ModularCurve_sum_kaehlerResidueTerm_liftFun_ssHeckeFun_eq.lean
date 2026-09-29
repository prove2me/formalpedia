-- Prove2me | solution 1 for ModularCurve.sum_kaehlerResidueTerm_liftFun_ssHeckeFun_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/3182584a-c6ec-51cd-a94a-593b5e324981

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_SSCarrier
import Definitions.Def_ModularCurve_SSHeckeV2
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_WeightDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_FibreResidueIdentityAlong
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_Place_neg_le_ord_trace_of_forall_le_ord_sub_pred
import Theorems.Thm_ModularCurve_sum_kaehlerResidueTerm_eq_sum_kaehlerResidueTerm_traceAlong_of_ord_sub_traceFunAlong
import Theorems.Thm_ModularCurve_SSHeckeV2_liftFun_spec
import Theorems.Thm_ModularCurve_SSHeckeV2_ord_heckeMultiplier_eq_and_width_eq_and_mem_ssPlaces_of_mem_fiber
import Theorems.Thm_AlgebraicCurve_Place_neg_le_ord_trace_of_forall_le_ord_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_Place_evalAt_eq_zero_iff_one_le_ord
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_mem_ssPlaces
import Theorems.Thm_AlgebraicCurve_fibreResidueIdentityAlong_of_separableAlong_of_dCoordGenerates
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaC
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaC
import Theorems.Thm_ModularCurve_separableAlong_heckeAlphaC_heckeBetaC
import Theorems.Thm_ModularCurve_isQExpansionDiffAlong_qExpansionDiffAlong
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_theta_coeff
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_AlgebraicCurve_Place_canonicalLocalResidueDataK_eq
import Theorems.Thm_ModularCurve_weightFloor_eq_of_isAffineGeomPlace
import Theorems.Thm_ModularCurve_exists_divisor_forall_eq_weightFloor_fieldC
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_ModularCurve_ord_unif
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_sum_kaehlerResidueTerm_liftFun_ssHeckeFun_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.Affine.Point.instFinite GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "instance" "ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.serrePairing_apply_mk AlgebraicCurve.residueSumOffChartLinear_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂"
p2m_attr_erase "simp" "PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one HahnSeries.ramScale_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU LaurentSeries.coeff_heckeV LaurentSeries.coeff_heckeU FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve ModularCurve

namespace STUB2Red

theorem core_ineq (ux uz ea eb m : ℤ) (hux1 : 1 ≤ ux) (hux3 : ux ≤ 3) (huz1 : 1 ≤ uz) (huz3 : uz ≤ 3)
    (hea : 1 ≤ ea) (heb : 1 ≤ eb) (h3 : ea * uz = eb * ux) :
    ux ≤ ea * ((-m) % uz - (-m) % ux + ux) := by
  have hB1 : 1 ≤ (-m) % uz - (-m) % ux + ux := by
    have := Int.emod_nonneg (-m) (show uz ≠ 0 by omega)
    have := Int.emod_lt_of_pos (-m) (show 0 < ux by omega)
    omega
  have hB5 : (-m) % uz - (-m) % ux + ux ≤ 5 := by
    have := Int.emod_nonneg (-m) (show ux ≠ 0 by omega)
    have := Int.emod_lt_of_pos (-m) (show 0 < uz by omega)
    omega

  obtain ⟨B, hB⟩ : ∃ B, B = (-m) % uz - (-m) % ux + ux := ⟨_, rfl⟩
  rw [← hB] at hB1 hB5 ⊢
  interval_cases ux <;> interval_cases uz <;> interval_cases B <;> omega

theorem subpred_ineq (ux uz ea eb r s m Dx Dz O : ℤ) (hux1 : 1 ≤ ux) (hux3 : ux ≤ 3) (huz1 : 1 ≤ uz) (huz3 : uz ≤ 3)
    (hea : 1 ≤ ea) (heb : 1 ≤ eb) (h3 : ea * uz = eb * ux)
    (hDx : ux * Dx = m * (ux * r - 1) - (-m) % ux) (hDz : uz * Dz = m * (uz * s - 1) - (-m) % uz)
    (hO : -Dz ≤ O) :
    -(ea * Dx) - (ea - 1) ≤ eb * O + m * (eb * s - ea * r) := by
  have hcore := core_ineq ux uz ea eb m hux1 hux3 huz1 huz3 hea heb h3
  have hO' : -(eb * Dz) ≤ eb * O := by nlinarith

  have E : ux * uz * (-(eb * Dz) + m * (eb * s - ea * r) + ea * Dx + ea - 1)
      = uz * (ea * ((-m) % uz - (-m) % ux + ux) - ux) := by
    linear_combination (-(ux * eb)) * hDz + (uz * ea) * hDx - (m + (-m) % uz) * h3
  have hpos : 0 < ux * uz := mul_pos (by omega) (by omega)
  have hnn : 0 ≤ ux * uz * (-(eb * Dz) + m * (eb * s - ea * r) + ea * Dx + ea - 1) := by
    rw [E]; exact mul_nonneg (by omega) (by linarith)
  have := (mul_nonneg_iff_of_pos_left hpos).mp hnn
  linarith

variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]

theorem width_mul_weightDivisor_eq_sub_emod (hp5 : 5 ≤ p) (hN : (N : K) ≠ 0) (m : ℕ) (z : Place K ↥(modularFunctionFieldC K N)) (hz : z ∈ ssPlaces p N K) :
    (placeWidth N z : ℤ) * ModularCurve.weightDivisor K N m z
      = (m : ℤ) * ((placeWidth N z : ℤ) * (placeRamificationJ N z : ℤ) - 1) - (-(m : ℤ)) % (placeWidth N z : ℤ) := by
  have hpN : ¬ p ∣ N := fun hh => hN ((CharP.cast_eq_zero_iff K p N).mpr hh)
  have hW : ((jWidth (z.evalAt (jGeomGen K N)) : ℤ)) = (placeWidth N z : ℤ) * (placeRamificationJ N z : ℤ) := by
    exact_mod_cast (Nat.div_mul_cancel (ModularCurve.placeRamificationJ_dvd_jWidth_of_mem_ssPlaces hp5 hpN hz)).symm
  rw [ModularCurve.weightDivisor_apply K N m (ModularCurve.exists_divisor_forall_eq_weightFloor_fieldC K N m) z,
    ModularCurve.weightFloor_eq_of_isAffineGeomPlace p hp5 N hpN K m z hz.2.1, hW]
  set u : ℤ := (placeWidth N z : ℤ)
  set M : ℤ := (m : ℤ) * (u * (placeRamificationJ N z : ℤ) - 1)
  have hM : M = (-(m : ℤ)) + u * ((m : ℤ) * (placeRamificationJ N z : ℤ)) := by ring
  have h1 : u * (M / u) = M - M % u := by have := Int.emod_add_mul_ediv M u; linarith
  rw [h1, hM, Int.add_mul_emod_self_left]

theorem neg_mul_sub_pred_le_ord_heckeBetaC_mul_pow
    (hp5 : 5 ≤ p) (hN : (N : K) ≠ 0)
    (hα : (heckeAlphaC K N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC K N ℓ).toRingHom.IsIntegral)
    (m : ℕ) (hm : 1 ≤ m) (h : ↥(charLDegeneracyRoof K N ℓ)) (hh0 : h ≠ 0)
    (gv : ↥(modularFunctionFieldC K N)) (hgv0 : gv ≠ 0)
    (hF : ∀ z : Place K ↥(modularFunctionFieldC K N), z ∈ ssPlaces p N K → -(ModularCurve.weightDivisor K N m z) ≤ z.ord gv)
    (x : Place K ↥(modularFunctionFieldC K N)) (hx : x ∈ ssPlaces p N K)
    (S : Finset (Place K ↥(charLDegeneracyRoof K N ℓ)))
    (hSx : ∀ y : Place K ↥(charLDegeneracyRoof K N ℓ), y ∈ S ↔ y.restrictAlong (heckeAlphaC K N ℓ) hα = x)
    (hH : ∀ y ∈ S,
      y.ord h = (Place.ramificationIndexAlong (heckeBetaC K N ℓ) y : ℤ)
                  * (placeRamificationJ N (y.restrictAlong (heckeBetaC K N ℓ) hβ) : ℤ)
              - (Place.ramificationIndexAlong (heckeAlphaC K N ℓ) y : ℤ) * (placeRamificationJ N x : ℤ))
    (hW : ∀ y ∈ S,
      (Place.ramificationIndexAlong (heckeAlphaC K N ℓ) y : ℤ) * (placeWidth N (y.restrictAlong (heckeBetaC K N ℓ) hβ) : ℤ)
        = (Place.ramificationIndexAlong (heckeBetaC K N ℓ) y : ℤ) * (placeWidth N x : ℤ))
    (hS : ∀ y ∈ S, y.restrictAlong (heckeBetaC K N ℓ) hβ ∈ ssPlaces p N K) :
    ∀ y ∈ S, -((Place.ramificationIndexAlong (heckeAlphaC K N ℓ) y : ℤ) * ModularCurve.weightDivisor K N m x)
        - ((Place.ramificationIndexAlong (heckeAlphaC K N ℓ) y : ℤ) - 1) ≤ y.ord (heckeBetaC K N ℓ gv * h ^ m) := by
  classical
  intro y hy
  have hpN : ¬ p ∣ N := fun hh => hN ((CharP.cast_eq_zero_iff K p N).mpr hh)
  set z := y.restrictAlong (heckeBetaC K N ℓ) hβ with hz_def
  have hz : z ∈ ssPlaces p N K := hS y hy

  have hWx : placeWidth N x * placeRamificationJ N x = jWidth (x.evalAt (jGeomGen K N)) :=
    Nat.div_mul_cancel (ModularCurve.placeRamificationJ_dvd_jWidth_of_mem_ssPlaces hp5 hpN hx)
  have hWz : placeWidth N z * placeRamificationJ N z = jWidth (z.evalAt (jGeomGen K N)) :=
    Nat.div_mul_cancel (ModularCurve.placeRamificationJ_dvd_jWidth_of_mem_ssPlaces hp5 hpN hz)
  have j3x : jWidth (x.evalAt (jGeomGen K N)) ≤ 3 := by unfold jWidth; split_ifs <;> omega
  have j1x : 1 ≤ jWidth (x.evalAt (jGeomGen K N)) := by unfold jWidth; split_ifs <;> omega
  have j3z : jWidth (z.evalAt (jGeomGen K N)) ≤ 3 := by unfold jWidth; split_ifs <;> omega
  have j1z : 1 ≤ jWidth (z.evalAt (jGeomGen K N)) := by unfold jWidth; split_ifs <;> omega
  have hux1 : 1 ≤ placeWidth N x := by
    rcases Nat.eq_zero_or_pos (placeWidth N x) with h0 | hpos
    · rw [h0, zero_mul] at hWx; omega
    · exact hpos
  have huz1 : 1 ≤ placeWidth N z := by
    rcases Nat.eq_zero_or_pos (placeWidth N z) with h0 | hpos
    · rw [h0, zero_mul] at hWz; omega
    · exact hpos
  have hux3 : placeWidth N x ≤ 3 := (Nat.div_le_self _ _).trans j3x
  have huz3 : placeWidth N z ≤ 3 := (Nat.div_le_self _ _).trans j3z

  have hβ0 : heckeBetaC K N ℓ gv ≠ 0 := (map_ne_zero_iff _ (heckeBetaC K N ℓ).injective).mpr hgv0
  rw [y.ord_mul hβ0 (pow_ne_zero m hh0), ← zpow_natCast, y.ord_zpow, Place.ord_restrictAlong (heckeBetaC K N ℓ) hβ y gv, hH y hy]

  have heb : 1 ≤ (Place.ramificationIndexAlong (heckeBetaC K N ℓ) y : ℤ) := by
    have h0 : 0 < Place.ramificationIndexAlong (heckeBetaC K N ℓ) y := by
      unfold Place.ramificationIndexAlong
      letI := AlgebraicCurve.algebraAlong (heckeBetaC K N ℓ)
      haveI := AlgebraicCurve.isIntegral_along (heckeBetaC K N ℓ) hβ
      exact Place.ramificationIndex_pos (F := ↥(modularFunctionFieldC K N)) (w := y)
    exact_mod_cast h0
  have hea : 1 ≤ (Place.ramificationIndexAlong (heckeAlphaC K N ℓ) y : ℤ) := by
    have h0 : 0 < Place.ramificationIndexAlong (heckeAlphaC K N ℓ) y := by
      unfold Place.ramificationIndexAlong
      letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
      haveI := AlgebraicCurve.isIntegral_along (heckeAlphaC K N ℓ) hα
      exact Place.ramificationIndex_pos (F := ↥(modularFunctionFieldC K N)) (w := y)
    exact_mod_cast h0
  have hDx := width_mul_weightDivisor_eq_sub_emod p K N hp5 hN m x hx
  have hDz := width_mul_weightDivisor_eq_sub_emod p K N hp5 hN m z hz
  exact subpred_ineq _ _ _ _ _ _ _ _ _ _ (by exact_mod_cast hux1) (by exact_mod_cast hux3) (by exact_mod_cast huz1) (by exact_mod_cast huz3)
    hea heb (hW y hy) hDx hDz (hF z hz)

end STUB2Red

namespace STUB2Red

variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]

theorem weightDivisor_nonneg_of_mem_ssPlaces (hp5 : 5 ≤ p) (hN : (N : K) ≠ 0) (m : ℕ) (z : Place K ↥(modularFunctionFieldC K N)) (hz : z ∈ ssPlaces p N K) :
    0 ≤ ModularCurve.weightDivisor K N m z := by
  have hpN : ¬ p ∣ N := fun hh => hN ((CharP.cast_eq_zero_iff K p N).mpr hh)
  rw [ModularCurve.weightDivisor_apply K N m (ModularCurve.exists_divisor_forall_eq_weightFloor_fieldC K N m) z,
    ModularCurve.weightFloor_eq_of_isAffineGeomPlace p hp5 N hpN K m z hz.2.1]
  apply Int.ediv_nonneg _ (by positivity)
  apply mul_nonneg (by positivity)
  have : 1 ≤ jWidth (z.evalAt (jGeomGen K N)) := by unfold jWidth; split_ifs <;> omega
  omega

theorem ord_algebraMap_eq_zero (z : Place K ↥(modularFunctionFieldC K N)) (c : K) (hc : c ≠ 0) :
    z.ord (algebraMap K ↥(modularFunctionFieldC K N) c) = 0 := by
  have h0 : algebraMap K ↥(modularFunctionFieldC K N) c ≠ 0 := (map_ne_zero_iff _ (algebraMap K _).injective).mpr hc
  have h0' : algebraMap K ↥(modularFunctionFieldC K N) c⁻¹ ≠ 0 := (map_ne_zero_iff _ (algebraMap K _).injective).mpr (inv_ne_zero hc)
  have h1 := z.ord_mul h0 h0'
  rw [← map_mul, mul_inv_cancel₀ hc, map_one, Place.ord_one] at h1
  have h2 : 0 ≤ z.ord (algebraMap K ↥(modularFunctionFieldC K N) c) := (Place.mem_iff_ord_nonneg z h0).mp (z.algebraMap_mem' c)
  have h3 : 0 ≤ z.ord (algebraMap K ↥(modularFunctionFieldC K N) c⁻¹) := (Place.mem_iff_ord_nonneg z h0').mp (z.algebraMap_mem' c⁻¹)
  omega

theorem neg_weightDivisor_le_ord_traceFunAlong
    (hp5 : 5 ≤ p) (hN : (N : K) ≠ 0) (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p) (m : ℕ) (hm : 1 ≤ m)
    [IsCurveOver K ↥(modularFunctionFieldC K N)] [IsCurveOver K ↥(charLDegeneracyRoof K N ℓ)]
    (hαI : HeckeAlphaCIntegral K N ℓ) (hβI : HeckeBetaCIntegral K N ℓ)
    (gv : ↥(modularFunctionFieldC K N))
    (hgv : ∀ z : Place K ↥(modularFunctionFieldC K N), z ∈ ssPlaces p N K → -(ModularCurve.weightDivisor K N m z) ≤ z.ord gv)
    (x : Place K ↥(modularFunctionFieldC K N)) (hx : x ∈ ssPlaces p N K) :
    -(ModularCurve.weightDivisor K N m x) ≤ x.ord (traceFunAlong (heckeAlphaC K N ℓ)
        (heckeBetaC K N ℓ gv * (algebraMap K ↥(charLDegeneracyRoof K N ℓ) ((ℓ : K) ^ (m - 1)) * ModularCurve.heckeMultiplier N K ℓ ^ m))) := by
  classical
  have hD0 := weightDivisor_nonneg_of_mem_ssPlaces p K N hp5 hN m x hx
  letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
  haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC K N ℓ)
  set hM := ModularCurve.heckeMultiplier N K ℓ with hMdef
  set c : K := (ℓ : K) ^ (m - 1) with hcdef
  have hc0 : c ≠ 0 := by
    apply pow_ne_zero
    intro h0
    have : p ∣ ℓ := (CharP.cast_eq_zero_iff K p ℓ).mp h0
    exact hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp this).symm

  have e1 : heckeBetaC K N ℓ gv * (algebraMap K ↥(charLDegeneracyRoof K N ℓ) c * hM ^ m)
      = (algebraMap K ↥(modularFunctionFieldC K N) c) • (heckeBetaC K N ℓ gv * hM ^ m) := by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply K ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) c]; ring
  rw [traceFunAlong_apply, e1, LinearMap.map_smul_of_tower, smul_eq_mul]

  by_cases hT0 : Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ gv * hM ^ m) = 0
  · rw [hT0, mul_zero, Place.ord_zero]; omega
  rw [x.ord_mul ((map_ne_zero_iff _ (algebraMap K _).injective).mpr hc0) hT0, ord_algebraMap_eq_zero K N x c hc0, zero_add]
  have hgv0 : gv ≠ 0 := by
    intro h0; apply hT0; rw [h0, map_zero, zero_mul, map_zero]
  have hM0 : hM ≠ 0 := by
    intro h0; apply hT0
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
    rw [h0, pow_succ, mul_zero, mul_zero, map_zero]

  set S := AlgebraicCurve.Place.fiberAlong (heckeAlphaC K N ℓ) hαI x
  have hSx : ∀ y : Place K ↥(charLDegeneracyRoof K N ℓ), y ∈ S ↔ y.restrictAlong (heckeAlphaC K N ℓ) hαI = x :=
    fun y => AlgebraicCurve.Place.mem_fiberAlong
  obtain ⟨hH, hW, hS⟩ := ModularCurve.SSHeckeV2.ord_heckeMultiplier_eq_and_width_eq_and_mem_ssPlaces_of_mem_fiber
    p hp5 K N ℓ hN hℓN hℓp hαI hβI x hx S hSx
  have hpNℓ : ¬ p ∣ N * ℓ := by
    intro hh
    rcases (Nat.Prime.dvd_mul Fact.out).mp hh with h1 | h2
    · exact (fun hh => hN ((CharP.cast_eq_zero_iff K p N).mpr hh)) h1
    · exact hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp h2).symm
  exact AlgebraicCurve.Place.neg_le_ord_trace_of_forall_le_ord_sub_pred (heckeAlphaC K N ℓ) hαI
    (ModularCurve.finiteAlong_heckeAlphaC K N ℓ) (ModularCurve.separableAlong_heckeAlphaC_heckeBetaC K N ℓ hpNℓ).1
    x S hSx _ hD0 _ (neg_mul_sub_pred_le_ord_heckeBetaC_mul_pow p K N ℓ hp5 hN hαI hβI m hm hM hM0 gv hgv0 hgv x hx S hSx hH hW hS)

end STUB2Red

open AlgebraicCurve ModularCurve

namespace STUB2Red
namespace Aux

variable {K : Type} [Field K]

theorem evalAt_add' {F : Type*} [Field F] [Algebra K F] (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  have hfg : f + g ∈ v.toValuationSubring := add_mem hf hg
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv hfg, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg]
  rw [show (⟨f + g, hfg⟩ : v.toValuationSubring) = ⟨f, hf⟩ + ⟨g, hg⟩ from rfl, map_add]

variable (N : ℕ) [NeZero N]

theorem zpow_mul_mem (x : Place K ↥(modularFunctionFieldC K N)) (a : ℤ) (t : ↥(modularFunctionFieldC K N)) (ht : t = 0 ∨ -a ≤ x.ord t) :
    ModularCurve.unif N K x ^ a * t ∈ x.toValuationSubring := by
  rcases eq_or_ne t 0 with rfl | ht0
  · rw [mul_zero]; exact zero_mem _
  rcases ht with h | h
  · exact absurd h ht0
  have hπ := ModularCurve.ord_unif K N x
  have hπ0 : ModularCurve.unif N K x ≠ 0 := by intro h0; rw [h0, Place.ord_zero] at hπ; exact zero_ne_one hπ
  apply Place.mem_of_ord_nonneg x (mul_ne_zero (zpow_ne_zero a hπ0) ht0)
  rw [x.ord_mul (zpow_ne_zero a hπ0) ht0, x.ord_zpow, hπ, mul_one]; omega

theorem lead_add (x : Place K ↥(modularFunctionFieldC K N)) (hx : x.IsRational) (a : ℤ) (s t : ↥(modularFunctionFieldC K N))
    (hs : ModularCurve.unif N K x ^ a * s ∈ x.toValuationSubring) (ht : ModularCurve.unif N K x ^ a * t ∈ x.toValuationSubring) :
    ModularCurve.lead N K x a (s + t) = ModularCurve.lead N K x a s + ModularCurve.lead N K x a t := by
  unfold ModularCurve.lead
  rw [mul_add, evalAt_add' x hx hs ht]

theorem lead_algebraMap_mul (x : Place K ↥(modularFunctionFieldC K N)) (hx : x.IsRational) (a : ℤ) (c : K) (t : ↥(modularFunctionFieldC K N))
    (ht : ModularCurve.unif N K x ^ a * t ∈ x.toValuationSubring) :
    ModularCurve.lead N K x a (algebraMap K _ c * t) = c * ModularCurve.lead N K x a t := by
  unfold ModularCurve.lead
  rw [mul_left_comm, Place.evalAt_mul x hx (x.algebraMap_mem' c) ht, Place.evalAt_algebraMap]

end STUB2Red.Aux

namespace STUB2Red

open STUB2Red.Aux

variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]

theorem ord_sub_ge_of_index (hp5 : 5 ≤ p) (hN : (N : K) ≠ 0) (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p) (m : ℕ) (hm : 1 ≤ m)
    (v : ModularCurve.SSCarrier p N K hp5 (2 * (m : ℤ))) (x : ModularCurve.SSIndex p N K hp5 (2 * (m : ℤ)))
    (hg : -(ModularCurve.weightDivisor K N m x.1) ≤ x.1.ord (traceFunAlong (heckeAlphaC K N ℓ)
        (heckeBetaC K N ℓ (ModularCurve.liftFun p N K hp5 (2 * (m : ℤ)) v) *
          (algebraMap K ↥(charLDegeneracyRoof K N ℓ) ((ℓ : K) ^ (m - 1)) * ModularCurve.heckeMultiplier N K ℓ ^ m)))) :
    let f₁ := ModularCurve.liftFun p N K hp5 (2 * (m : ℤ)) (ModularCurve.ssHeckeFun p N K hp5 (2 * (m : ℤ)) ℓ v)
    let g := traceFunAlong (heckeAlphaC K N ℓ) (heckeBetaC K N ℓ (ModularCurve.liftFun p N K hp5 (2 * (m : ℤ)) v) *
              (algebraMap K ↥(charLDegeneracyRoof K N ℓ) ((ℓ : K) ^ (m - 1)) * ModularCurve.heckeMultiplier N K ℓ ^ m))
    f₁ - g = 0 ∨ -(ModularCurve.weightDivisor K N m x.1) + 1 ≤ x.1.ord (f₁ - g) := by
  classical
  intro f₁ g
  have hpN : ¬ p ∣ N := fun hh => hN ((CharP.cast_eq_zero_iff K p N).mpr hh)
  have hkn : ((2 * (m : ℤ)) / 2).toNat = m := by simp
  have hxrat : x.1.IsRational := x.2.1.1

  have hcoef : ModularCurve.weightDivisor K N m x.1 = ModularCurve.poleOrder p N K hp5 (2 * (m : ℤ)) x := by
    rw [ModularCurve.weightDivisor_apply K N m (ModularCurve.exists_divisor_forall_eq_weightFloor_fieldC K N m) x.1,
      ModularCurve.weightFloor_eq_of_isAffineGeomPlace p hp5 N hpN K m x.1 x.2.1.2.1]
    unfold ModularCurve.poleOrder
    congr 1
    congr 1
    omega
  set a := ModularCurve.poleOrder p N K hp5 (2 * (m : ℤ)) x with hadef
  rw [hcoef] at hg ⊢

  have hLspec := ModularCurve.SSHeckeV2.liftFun_spec p hp5 K N hN (2 * (m : ℤ)) (ModularCurve.ssHeckeFun p N K hp5 (2 * (m : ℤ)) ℓ v)
  have hLv := ModularCurve.SSHeckeV2.liftFun_spec p hp5 K N hN (2 * (m : ℤ)) v
  simp only [hkn] at hLspec hLv
  have lead_f : ModularCurve.lead N K x.1 a f₁ = ModularCurve.ssHeckeFun p N K hp5 (2 * (m : ℤ)) ℓ v x := hLspec.2 x
  have mem_f : ModularCurve.unif N K x.1 ^ a * f₁ ∈ x.1.toValuationSubring := by
    apply zpow_mul_mem N x.1 a; right
    have := hLspec.1 x.1 x.2.1
    rw [hcoef] at this; exact this
  have mem_g : ModularCurve.unif N K x.1 ^ a * g ∈ x.1.toValuationSubring := zpow_mul_mem N x.1 a g (Or.inr hg)

  letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
  haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC K N ℓ)
  set hM := ModularCurve.heckeMultiplier N K ℓ with hMdef
  set Lv := ModularCurve.liftFun p N K hp5 (2 * (m : ℤ)) v with hLvdef
  set c : K := (ℓ : K) ^ (m - 1) with hcdef
  set T := Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ Lv * hM ^ m) with hTdef
  have hg_eq : g = algebraMap K ↥(modularFunctionFieldC K N) c * T := by
    show traceFunAlong (heckeAlphaC K N ℓ) _ = _
    have e1 : heckeBetaC K N ℓ Lv * (algebraMap K ↥(charLDegeneracyRoof K N ℓ) c * hM ^ m)
        = (algebraMap K ↥(modularFunctionFieldC K N) c) • (heckeBetaC K N ℓ Lv * hM ^ m) := by
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply K ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) c]; ring
    rw [traceFunAlong_apply, e1, LinearMap.map_smul_of_tower, smul_eq_mul]

  have hc0 : c ≠ 0 := by
    apply pow_ne_zero; intro h0
    have : p ∣ ℓ := (CharP.cast_eq_zero_iff K p ℓ).mp h0
    exact hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp this).symm
  have mem_T : ModularCurve.unif N K x.1 ^ a * T ∈ x.1.toValuationSubring := by
    have hc0' : algebraMap K ↥(modularFunctionFieldC K N) c ≠ 0 := (map_ne_zero_iff _ (algebraMap K _).injective).mpr hc0
    have e2 : ModularCurve.unif N K x.1 ^ a * T
        = algebraMap K _ c⁻¹ * (ModularCurve.unif N K x.1 ^ a * g) := by
      rw [hg_eq, map_inv₀, ← mul_assoc, ← mul_assoc, mul_comm ((algebraMap K ↥(modularFunctionFieldC K N)) c)⁻¹,
        mul_assoc _ _ ((algebraMap K ↥(modularFunctionFieldC K N)) c), inv_mul_cancel₀ hc0', mul_one]
    rw [e2]; exact mul_mem (x.1.algebraMap_mem' _) mem_g
  have lead_g : ModularCurve.lead N K x.1 a g = ModularCurve.ssHeckeFun p N K hp5 (2 * (m : ℤ)) ℓ v x := by
    rw [hg_eq, lead_algebraMap_mul N x.1 hxrat a c T mem_T]
    show _ = algebraMap K K ((ℓ : K) ^ ((2 * (m : ℤ)) / 2 - 1)) * ModularCurve.lead N K x.1 a
      (Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
        (heckeBetaC K N ℓ Lv * hM ^ ((2 * (m : ℤ)) / 2).toNat))
    have hid : ∀ t : K, algebraMap K K t = t := fun t => rfl
    rw [hkn, hid]
    congr 1
    rw [hcdef, ← zpow_natCast]
    congr 1
    omega

  have lead_d : ModularCurve.lead N K x.1 a (f₁ - g) = 0 := by
    have hsum : f₁ = g + (f₁ - g) := by ring
    have mem_d : ModularCurve.unif N K x.1 ^ a * (f₁ - g) ∈ x.1.toValuationSubring := by
      rw [mul_sub]; exact sub_mem mem_f mem_g
    have := lead_add N x.1 hxrat a g (f₁ - g) mem_g mem_d
    rw [← hsum, lead_f, lead_g] at this
    linear_combination -this

  by_cases hd0 : f₁ - g = 0
  · left; exact hd0
  right
  have hπ := ModularCurve.ord_unif K N x.1
  have hπ0 : ModularCurve.unif N K x.1 ≠ 0 := by intro h0; rw [h0, Place.ord_zero] at hπ; exact zero_ne_one hπ
  have hf0 : ModularCurve.unif N K x.1 ^ a * (f₁ - g) ≠ 0 := mul_ne_zero (zpow_ne_zero a hπ0) hd0
  have mem_d : ModularCurve.unif N K x.1 ^ a * (f₁ - g) ∈ x.1.toValuationSubring := by
    rw [mul_sub]; exact sub_mem mem_f mem_g
  have h1 := (Place.evalAt_eq_zero_iff_one_le_ord x.1 hxrat hf0 mem_d).mp lead_d
  rw [x.1.ord_mul (zpow_ne_zero a hπ0) hd0, x.1.ord_zpow, hπ, mul_one] at h1
  omega

end STUB2Red

open AlgebraicCurve ModularCurve KaehlerDifferential

namespace STUB2Red

variable (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] [NeZero ℓ]

theorem subsingleton_hasCanonicalLocalResidueKStar (F : Type*) [Field F] [Algebra K F] [IsCurveOver K F] :
    Subsingleton (HasCanonicalLocalResidueKStar K F) := by
  refine ⟨fun a b => ?_⟩
  have hr : ∀ v : Place K F, v.IsRational := fun v => by
    haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
    haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
    exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2
  obtain ⟨da⟩ := a
  obtain ⟨db⟩ := b
  congr 1
  funext v
  exact AlgebraicCurve.Place.canonicalLocalResidueDataK_eq v (hr v) _ _

theorem D_heckeBetaC_jGeomGen_ne_zero (hℓK : (ℓ : K) ≠ 0) :
    KaehlerDifferential.D K ↥(charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ (jGeomGen K N)) ≠ 0 := by
  intro h0
  have h1 := (ModularCurve.isQExpansionDiffAlong_qExpansionDiffAlong (charLDegeneracyRoof K N ℓ).val).1
    (heckeBetaC K N ℓ (jGeomGen K N))

  have h2 : thetaL K (qExpand K ℓ (jqModC K)) = 0 := by
    change thetaL K ((charLDegeneracyRoof K N ℓ).val (heckeBetaC K N ℓ (jGeomGen K N))) = 0
    rw [← h1]
    convert map_zero (qExpansionDiffAlong (charLDegeneracyRoof K N ℓ).val) using 2
  replace h2 := congrArg (fun s : LaurentSeries K => s.coeff (-(ℓ : ℤ))) h2
  simp only [HahnSeries.coeff_zero] at h2
  rw [thetaL_apply, theta_coeff, show (-(ℓ : ℤ)) = (ℓ : ℤ) * (-1) by ring, qExpand_coeff_mul,
    ModularCurve.coeff_jqModC_neg_one, zsmul_eq_mul, mul_one] at h2
  push_cast at h2
  have h3 : (ℓ : K) * -1 = 0 := h2
  exact hℓK (by simpa using h3)

end STUB2Red

open AlgebraicCurve ModularCurve KaehlerDifferential STUB2Red in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] [NeZero ℓ]
    [IsCurveOver K ↥(modularFunctionFieldC K N)] [IsCurveOver K ↥(charLDegeneracyRoof K N ℓ)]
    [HasCanonicalLocalResidueKStar K ↥(modularFunctionFieldC K N)] [HasCanonicalLocalResidueKStar K ↥(charLDegeneracyRoof K N ℓ)]
    [HasPrincipalDivisors K ↥(charLDegeneracyRoof K N ℓ)]
    [∀ v : Place K ↥(modularFunctionFieldC K N), v.DCoordGenerates] [∀ w : Place K ↥(charLDegeneracyRoof K N ℓ), w.DCoordGenerates]
    [Nontrivial Ω[↥(modularFunctionFieldC K N)⁄K]] [Nontrivial Ω[↥(charLDegeneracyRoof K N ℓ)⁄K]]
    (hN : (N : K) ≠ 0) (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (m : ℕ) (hm : 1 ≤ m)
    (hαI : HeckeAlphaCIntegral K N ℓ) (hβI : HeckeBetaCIntegral K N ℓ)
    (SS : Finset (Place K ↥(modularFunctionFieldC K N))) (hSS : ∀ x, x ∈ SS ↔ x ∈ ssPlaces p N K)
    (hstab : ∀ w : Place K ↥(charLDegeneracyRoof K N ℓ),
      Place.restrictAlong (heckeAlphaC K N ℓ) hαI w ∈ SS ↔ Place.restrictAlong (heckeBetaC K N ℓ) hβI w ∈ SS)
    (v : ModularCurve.SSIndex p N K hp5 (2 * (m : ℤ)) → K) (ω : Ω[↥(modularFunctionFieldC K N)⁄K])
    (hωi : ∀ x : ModularCurve.SSIndex p N K hp5 (2 * (m : ℤ)), ModularCurve.weightDivisor K N m x.1 - 1 ≤ x.1.ordDifferential ω)
    (hωn : ∀ x ∈ SS, ¬ ((placeWidth N x : ℤ) ∣ (m : ℤ)) → ModularCurve.weightDivisor K N m x ≤ x.ordDifferential ω) :
    ∑ x ∈ SS, kaehlerResidueTerm ω
        (diagonalHom K ↥(modularFunctionFieldC K N) (ModularCurve.liftFun p N K hp5 (2 * (m : ℤ)) (ModularCurve.ssHeckeFun p N K hp5 (2 * (m : ℤ)) ℓ v))) x
      = ∑ z ∈ SS, kaehlerResidueTerm
          (Differential.traceAlong (heckeBetaC K N ℓ)
            ((algebraMap K ↥(charLDegeneracyRoof K N ℓ) ((ℓ : K) ^ (m - 1)) * ModularCurve.heckeMultiplier N K ℓ ^ m) •
              Differential.pullbackAlong (heckeAlphaC K N ℓ) ω))
          (diagonalHom K ↥(modularFunctionFieldC K N) (ModularCurve.liftFun p N K hp5 (2 * (m : ℤ)) v)) z := by
  classical
  set u : ↥(charLDegeneracyRoof K N ℓ) := algebraMap K ↥(charLDegeneracyRoof K N ℓ) ((ℓ : K) ^ (m - 1)) * ModularCurve.heckeMultiplier N K ℓ ^ m with hu
  set gv : ↥(modularFunctionFieldC K N) := ModularCurve.liftFun p N K hp5 (2 * (m : ℤ)) v with hgv
  set f₁ : ↥(modularFunctionFieldC K N) := ModularCurve.liftFun p N K hp5 (2 * (m : ℤ)) (ModularCurve.ssHeckeFun p N K hp5 (2 * (m : ℤ)) ℓ v) with hf₁

  have hfloor : ∀ (w : SSCarrier p N K hp5 (2 * (m : ℤ))) (z : Place K ↥(modularFunctionFieldC K N)), z ∈ ssPlaces p N K →
      -(ModularCurve.weightDivisor K N m z) ≤ z.ord (ModularCurve.liftFun p N K hp5 (2 * (m : ℤ)) w) := by
    intro w z hz
    have h1 := (ModularCurve.SSHeckeV2.liftFun_spec p hp5 K N hN (2 * (m : ℤ)) w).1 z hz
    have e : (2 * (m : ℤ) / 2).toNat = m := by
      rw [Int.mul_ediv_cancel_left _ two_ne_zero]; exact Int.toNat_natCast m
    rwa [e] at h1

  have hpN : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).mpr h)
  have hpℓ : ¬ p ∣ ℓ := fun h => hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out) (Fact.out)).mp h).symm
  have hpNℓ : ¬ p ∣ N * ℓ := fun h => ((Nat.Prime.dvd_mul (Fact.out)).mp h).elim hpN hpℓ
  have hsepαβ := ModularCurve.separableAlong_heckeAlphaC_heckeBetaC K N ℓ hpNℓ
  have hsep : SeparableAlong K (heckeBetaC K N ℓ) := hsepαβ.2

  haveI := subsingleton_hasCanonicalLocalResidueKStar K ↥(modularFunctionFieldC K N)
  haveI := subsingleton_hasCanonicalLocalResidueKStar K ↥(charLDegeneracyRoof K N ℓ)
  have hFα : FibreResidueIdentityAlong (heckeAlphaC K N ℓ) hαI := by
    convert AlgebraicCurve.fibreResidueIdentityAlong_of_separableAlong_of_dCoordGenerates
      (heckeAlphaC K N ℓ) hαI (ModularCurve.finiteAlong_heckeAlphaC K N ℓ) hsepαβ.1 using 2
  have hFβ : FibreResidueIdentityAlong (heckeBetaC K N ℓ) hβI := by
    convert AlgebraicCurve.fibreResidueIdentityAlong_of_separableAlong_of_dCoordGenerates
      (heckeBetaC K N ℓ) hβI (ModularCurve.finiteAlong_heckeBetaC K N ℓ) hsep using 2

  have hℓK : (ℓ : K) ≠ 0 := fun h => hpℓ ((CharP.cast_eq_zero_iff K p ℓ).mp h)
  have hΩ : ∀ η : Ω[↥(charLDegeneracyRoof K N ℓ)⁄K], ∃ (ω₁ : Ω[↥(modularFunctionFieldC K N)⁄K]) (c : ↥(charLDegeneracyRoof K N ℓ)), η = c • Differential.pullbackAlong (heckeBetaC K N ℓ) ω₁ := by
    intro η
    have hrk := (IsCurveOver.kaehler_free_rank_one (K := K) (F := ↥(charLDegeneracyRoof K N ℓ))).2
    have hne := D_heckeBetaC_jGeomGen_ne_zero K N ℓ hℓK
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hrk η
    exact ⟨KaehlerDifferential.D K _ (jGeomGen K N), c, by rw [Differential.pullbackAlong_D, hc]⟩
  refine ModularCurve.sum_kaehlerResidueTerm_eq_sum_kaehlerResidueTerm_traceAlong_of_ord_sub_traceFunAlong
    p hp5 K N ℓ hαI hβI hFα hFβ hsep hΩ SS hSS hstab m hm u gv f₁ ω ?_ ?_ hωi hωn
  ·
    intro x
    exact ord_sub_ge_of_index p K N ℓ hp5 hN hℓN hℓp m hm v x
      (neg_weightDivisor_le_ord_traceFunAlong p K N ℓ hp5 hN hℓN hℓp m hm hαI hβI gv (hfloor v) x.1 x.2.1)
  ·
    intro x hx hdx
    have h1 : -(ModularCurve.weightDivisor K N m x) ≤ x.ord f₁ := hfloor _ x ((hSS x).mp hx)
    have h2 : -(ModularCurve.weightDivisor K N m x) ≤ x.ord (traceFunAlong (heckeAlphaC K N ℓ) (heckeBetaC K N ℓ gv * u)) :=
      neg_weightDivisor_le_ord_traceFunAlong p K N ℓ hp5 hN hℓN hℓp m hm hαI hβI gv (hfloor v) x ((hSS x).mp hx)

    have H1 := (x.adicValuation_le_exp_iff).mpr (Or.inr h1)
    have H2 := (x.adicValuation_le_exp_iff).mpr (Or.inr h2)
    exact (x.adicValuation_le_exp_iff).mp (le_trans (Valuation.map_sub _ _ _) (max_le H1 H2))

end S_ModularCurve_sum_kaehlerResidueTerm_liftFun_ssHeckeFun_eq
end P2MW
export P2MW.S_ModularCurve_sum_kaehlerResidueTerm_liftFun_ssHeckeFun_eq (solution)
