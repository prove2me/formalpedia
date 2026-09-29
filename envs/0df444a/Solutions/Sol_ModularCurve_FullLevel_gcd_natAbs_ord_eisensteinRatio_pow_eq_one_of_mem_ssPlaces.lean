-- Prove2me | solution 1 for ModularCurve.FullLevel.gcd_natAbs_ord_eisensteinRatio_pow_eq_one_of_mem_ssPlaces
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/764b6a0b-5889-5cba-8eef-6159ddaab0b9

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularCurve_TateFormal
import Theorems.Thm_ModularCurve_exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq
import Theorems.Thm_ModularCurve_thetaL_jqModC_mul_intSeriesC_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_c4_tatePowerSeries
import Theorems.Thm_ModularCurve_c6_tatePowerSeries
import Theorems.Thm_ModularCurve_Delta_tatePowerSeries
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_gcd_natAbs_ord_eisensteinRatio_pow_eq_one_of_mem_ssPlaces
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one"
p2m_attr_erase "simp" "TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing
open scoped ArithmeticFunction.sigma

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

noncomputable section

namespace IgusaO1

section Orders

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]

theorem ord_pow' (x : Place K F) (f : F) (n : ℕ) : x.ord (f ^ n) = n * x.ord f := by
  rw [← zpow_natCast, x.ord_zpow]

end Orders

section Places

variable (K : Type) [Field K] (N : ℕ) [NeZero N]

theorem jGeomGen_ne_zero : (jGeomGen K N : ↥(modularFunctionFieldC K N)) ≠ 0 := by
  simpa using jGeomGen_sub_algebraMap_ne_zero K N 0

theorem jGeomGen_sub_ofNat_ne_zero :
    (jGeomGen K N : ↥(modularFunctionFieldC K N)) - 1728 ≠ 0 := by
  have := jGeomGen_sub_algebraMap_ne_zero K N 1728
  rwa [map_ofNat] at this

end Places

section Series

variable (K : Type*) [Field K]

theorem intSeriesC_eq_laurentOfInt (p : PowerSeries ℤ) : intSeriesC K p = laurentOfInt K p := rfl

theorem eisenstein4_eq_mk :
    eisenstein4 = PowerSeries.mk fun n => if n = 0 then 1 else 240 * (σ 3 n : ℤ) := by
  ext n; simp [eisenstein4, PowerSeries.coeff_mk, ArithmeticFunction.sigma_apply]

theorem eisenstein6_eq_mk :
    eisenstein6 = PowerSeries.mk fun n => if n = 0 then 1 else -504 * (σ 5 n : ℤ) := by
  ext n; simp [eisenstein6, PowerSeries.coeff_mk, ArithmeticFunction.sigma_apply]

theorem E4_cube_sub_E6_sq :
    laurentOfInt K eisenstein4 ^ 3 - laurentOfInt K eisenstein6 ^ 2 =
      1728 * laurentOfInt K (PowerSeries.X * dedekindEtaUnit) := by
  have h := tatePowerSeries.c_relation
  rw [c4_tatePowerSeries, c6_tatePowerSeries, Delta_tatePowerSeries, neg_sq] at h
  have h' := congrArg (laurentOfInt K) h
  rw [map_mul, map_sub, map_pow, map_pow, map_ofNat] at h'
  exact h'.symm

theorem jqModC_mul_delta :
    jqModC K * laurentOfInt K (PowerSeries.X * dedekindEtaUnit) = laurentOfInt K eisenstein4 ^ 3 := by
  have hX : laurentOfInt K PowerSeries.X = HahnSeries.single (1 : ℤ) (1 : K) := by
    rw [laurentOfInt_apply, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]
  have hj : jqModC K = HahnSeries.single (-1 : ℤ) (1 : K) * laurentOfInt K jNum := rfl
  have hprod : jNum * dedekindEtaUnit = eisenstein4 ^ 3 := by
    rw [jNum, mul_assoc, mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, mul_one]
  calc jqModC K * laurentOfInt K (PowerSeries.X * dedekindEtaUnit)
      = (HahnSeries.single (-1 : ℤ) (1 : K) * HahnSeries.single (1 : ℤ) (1 : K)) *
          laurentOfInt K (jNum * dedekindEtaUnit) := by rw [hj, map_mul, map_mul, hX]; ring
    _ = laurentOfInt K eisenstein4 ^ 3 := by
          rw [HahnSeries.single_mul_single, hprod, map_pow]
          norm_num

theorem delta_ne_zero : laurentOfInt K (PowerSeries.X * dedekindEtaUnit) ≠ 0 := by
  intro h
  have h1 := congrArg (fun x : LaurentSeries K => x.coeff ((1 : ℕ) : ℤ)) h
  simp only [laurentOfInt_apply, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
    HahnSeries.coeff_zero] at h1
  rw [show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_dedekindEtaUnit, map_one] at h1
  exact one_ne_zero h1

theorem E4_ne_zero : laurentOfInt K eisenstein4 ≠ 0 := by
  intro h
  have h1 := congrArg (fun x : LaurentSeries K => x.coeff ((0 : ℕ) : ℤ)) h
  simp only [laurentOfInt_apply, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
    HahnSeries.coeff_zero] at h1
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_eisenstein4, map_one] at h1
  exact one_ne_zero h1

theorem E6_ne_zero : laurentOfInt K eisenstein6 ≠ 0 := by
  intro h
  have h1 := congrArg (fun x : LaurentSeries K => x.coeff ((0 : ℕ) : ℤ)) h
  simp only [laurentOfInt_apply, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
    HahnSeries.coeff_zero] at h1
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_eisenstein6, map_one] at h1
  exact one_ne_zero h1

theorem thetaL_mul_delta :
    thetaL K (jqModC K) * laurentOfInt K (PowerSeries.X * dedekindEtaUnit) =
      -(laurentOfInt K eisenstein4 ^ 2 * laurentOfInt K eisenstein6) := by
  have h := thetaL_jqModC_mul_intSeriesC_X_mul_dedekindEtaUnit K
  rw [intSeriesC_eq_laurentOfInt, intSeriesC_eq_laurentOfInt, map_mul (laurentOfInt K) (eisenstein4 ^ 2),
    map_pow] at h
  exact h

theorem thetaL_jqModC_ne_zero : thetaL K (jqModC K) ≠ 0 := by
  intro h
  have := thetaL_mul_delta K
  rw [h, zero_mul, eq_comm, neg_eq_zero] at this
  exact mul_ne_zero (pow_ne_zero 2 (E4_ne_zero K)) (E6_ne_zero K) this

theorem E4_mul_E6_mul_thetaL :
    laurentOfInt K eisenstein4 * laurentOfInt K eisenstein6 * thetaL K (jqModC K) =
      -(jqModC K * (jqModC K - 1728)) * laurentOfInt K (PowerSeries.X * dedekindEtaUnit) := by
  have F1 := thetaL_mul_delta K
  have F2 := jqModC_mul_delta K
  have F3 : (jqModC K - 1728) * laurentOfInt K (PowerSeries.X * dedekindEtaUnit) =
      laurentOfInt K eisenstein6 ^ 2 := by
    have := E4_cube_sub_E6_sq K
    linear_combination F2 + this
  apply mul_right_cancel₀ (delta_ne_zero K)
  linear_combination (laurentOfInt K eisenstein4 * laurentOfInt K eisenstein6) * F1 +
    ((jqModC K - 1728) * laurentOfInt K (PowerSeries.X * dedekindEtaUnit)) * F2 +
    laurentOfInt K eisenstein4 ^ 3 * F3

theorem radicand_eq (n : ℕ) (b : LaurentSeries K)
    (hb : b = (laurentOfInt K eisenstein4 * laurentOfInt K eisenstein6 /
      laurentOfInt K (PowerSeries.X * dedekindEtaUnit)) ^ n) :
    b = (-1) ^ n * (thetaL K (jqModC K) ^ n)⁻¹ * jqModC K ^ n * (jqModC K - 1728) ^ n := by
  have hT := thetaL_jqModC_ne_zero K
  have hD := delta_ne_zero K
  have hbT : b * thetaL K (jqModC K) ^ n = (-(jqModC K * (jqModC K - 1728))) ^ n := by
    rw [hb, ← mul_pow]
    congr 1
    rw [div_mul_eq_mul_div, div_eq_iff hD, E4_mul_E6_mul_thetaL]
  have hb' : b = (-(jqModC K * (jqModC K - 1728))) ^ n * (thetaL K (jqModC K) ^ n)⁻¹ := by
    rw [← hbT, mul_inv_cancel_right₀ (pow_ne_zero n hT)]
  have hneg : (-(jqModC K * (jqModC K - 1728))) ^ n =
      (-1) ^ n * jqModC K ^ n * (jqModC K - 1728) ^ n := by
    rw [neg_eq_neg_one_mul, mul_pow, mul_pow, mul_assoc]
  rw [hb', hneg]
  ring

end Series

end IgusaO1

end

open IgusaO1 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (b : ↥(modularFunctionFieldC (ResidueField A) M'))
    (hb : (b : LaurentSeries (ResidueField A)) =
        (ModularCurve.intSeriesC (ResidueField A) (PowerSeries.mk fun n => if n = 0 then 1 else 240 * (σ 3 n : ℤ)) *
            ModularCurve.intSeriesC (ResidueField A) (PowerSeries.mk fun n => if n = 0 then 1 else -504 * (σ 5 n : ℤ)) /
          ModularCurve.intSeriesC (ResidueField A) (PowerSeries.X * ModularCurve.dedekindEtaUnit)) ^ ((q - 1) / 2))
    (v : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M'))
    (hv : v ∈ ssPlaces q M' (ResidueField A)) :
    Nat.gcd ((q - 1) / 2) (v.ord b).natAbs = 1 := by

  haveI : CharP (ResidueField A) q := ValuationSubring.residueField_charP_of_liesOverPrime A (Fact.out) hA
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le

  obtain ⟨h, hcoe, haffine, hcusp⟩ :=
    ModularCurve.exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq q hq M' hqM' (ResidueField A)

  set n : ℕ := (q - 1) / 2 with hndef
  have hn2 : (((q : ℤ) - 1) / 2) = (n : ℤ) := by rw [hndef]; omega
  set J : ↥(modularFunctionFieldC (ResidueField A) M') := jGeomGen (ResidueField A) M' with hJdef

  have hT := thetaL_jqModC_ne_zero (ResidueField A)
  have hbL : (b : LaurentSeries (ResidueField A)) =
      (-1) ^ n * (h : LaurentSeries (ResidueField A)) * jqModC (ResidueField A) ^ n *
        (jqModC (ResidueField A) - 1728) ^ n := by
    have hz : (-(((q : ℤ) - 1) / 2)) = -(n : ℤ) := by rw [hn2]
    rw [hcoe, hz, zpow_neg, zpow_natCast]
    refine radicand_eq (ResidueField A) n _ ?_
    rw [hb, eisenstein4_eq_mk, eisenstein6_eq_mk]
    rfl
  have hcoeU : (((-1 : ↥(modularFunctionFieldC (ResidueField A) M')) ^ n * h * J ^ n * (J - 1728) ^ n :
      ↥(modularFunctionFieldC (ResidueField A) M')) : LaurentSeries (ResidueField A)) =
      (-1) ^ n * (h : LaurentSeries (ResidueField A)) * jqModC (ResidueField A) ^ n *
        (jqModC (ResidueField A) - 1728) ^ n := by
    rw [hJdef, IntermediateField.coe_mul, IntermediateField.coe_mul, IntermediateField.coe_mul,
      IntermediateField.coe_pow, IntermediateField.coe_pow, IntermediateField.coe_pow,
      AddSubgroupClass.coe_sub, coe_jGeomGen]
    norm_cast
  have hbE : b = (-1) ^ n * h * J ^ n * (J - 1728) ^ n :=
    Subtype.ext (by rw [hcoeU]; exact hbL)

  have hh0 : h ≠ 0 := by
    intro h0
    have : (h : LaurentSeries (ResidueField A)) = 0 := by rw [h0]; rfl
    rw [hcoe] at this
    exact zpow_ne_zero _ hT this
  have hJ0 : J ≠ 0 := jGeomGen_ne_zero (ResidueField A) M'
  have hJ1 : J - 1728 ≠ 0 := jGeomGen_sub_ofNat_ne_zero (ResidueField A) M'
  have hm1 : ((-1 : ↥(modularFunctionFieldC (ResidueField A) M')) ^ n) ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  have hordb : v.ord b = v.ord h + (n : ℤ) * v.ord J + (n : ℤ) * v.ord (J - 1728) := by
    rw [hbE, v.ord_mul (mul_ne_zero (mul_ne_zero hm1 hh0) (pow_ne_zero _ hJ0)) (pow_ne_zero _ hJ1),
      v.ord_mul (mul_ne_zero hm1 hh0) (pow_ne_zero _ hJ0), v.ord_mul hm1 hh0,
      ord_pow', ord_pow', ord_pow', v.ord_neg, v.ord_one]
    ring

  have haff : IsAffineGeomPlace (ResidueField A) M' v := hv.2.1
  have hst := (haffine v haff).1 hv
  unfold stackOrd at hst
  rw [hn2] at hst

  have hcop : IsCoprime (n : ℤ) (v.ord b) := by
    refine ⟨(((jWidth (v.evalAt J) : ℕ) : ℤ) - 1) - (placeWidth (K := ResidueField A) M' v : ℤ) *
      (v.ord J + v.ord (J - 1728)), (placeWidth (K := ResidueField A) M' v : ℤ), ?_⟩
    linear_combination (placeWidth (K := ResidueField A) M' v : ℤ) * hordb + hst
  have hg : Int.gcd (n : ℤ) (v.ord b) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop
  simpa [Int.gcd, Int.natAbs_natCast] using hg

end S_ModularCurve_FullLevel_gcd_natAbs_ord_eisensteinRatio_pow_eq_one_of_mem_ssPlaces
end P2MW
export P2MW.S_ModularCurve_FullLevel_gcd_natAbs_ord_eisensteinRatio_pow_eq_one_of_mem_ssPlaces (solution)
