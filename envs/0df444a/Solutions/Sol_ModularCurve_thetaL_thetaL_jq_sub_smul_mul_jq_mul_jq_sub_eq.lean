-- Prove2me | solution 1 for ModularCurve.thetaL_thetaL_jq_sub_smul_mul_jq_mul_jq_sub_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/8df8c357-ef30-5511-ad7b-90b6f5d9fd85

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_TateFormal
import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_EisensteinSeries_ramanujan_system_qExpansion_int
import Theorems.Thm_ModularCurve_eisenstein4_cube_sub_mk_sq
import Theorems.Thm_ModularCurve_thetaL_jq_mul_deltaSeries
import Theorems.Thm_ModularCurve_theta_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_thetaL_thetaL_jq_sub_smul_mul_jq_mul_jq_sub_eq
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_thetaL_thetaL_jq_sub_smul_mul_jq_mul_jq_sub_eq.ModularCurve"

set_option maxHeartbeats 6400000

namespace ModularCurve
p2m_export "ModularCurve" "eisenstein4 dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum jNumQ jq thetaL thetaL_apply eisenstein6 dedekindEtaUnitQ deltaSeries deltaSeries_ne_zero eisenstein4_cube_sub_mk_sq thetaL_jq_mul_deltaSeries theta_mul"
namespace RB1
p2m_open "ModularCurve"

theorem coeff_thetaL (f : LaurentSeries ℚ) (n : ℤ) : (thetaL ℚ f).coeff n = (n : ℚ) * f.coeff n := by
  rw [thetaL_apply, LaurentSeries.derivative_apply, HahnSeries.coeff_single_mul, one_mul,
    LaurentSeries.hasseDeriv_coeff, Nat.cast_one, sub_add_cancel, Ring.choose_one_right, zsmul_eq_mul]

theorem thetaL_mul (f g : LaurentSeries ℚ) : thetaL ℚ (f * g) = f * thetaL ℚ g + g * thetaL ℚ f := by
  simp only [thetaL_apply]
  exact theta_mul f g

noncomputable abbrev φ (f : PowerSeries ℤ) : LaurentSeries ℚ :=
  HahnSeries.ofPowerSeries ℤ ℚ (f.map (Int.castRingHom ℚ))

theorem φ_mul (f g : PowerSeries ℤ) : φ (f * g) = φ f * φ g := by simp [φ, map_mul]
theorem φ_sub (f g : PowerSeries ℤ) : φ (f - g) = φ f - φ g := by simp [φ, map_sub]
theorem φ_pow (f : PowerSeries ℤ) (n : ℕ) : φ (f ^ n) = φ f ^ n := by simp [φ, map_pow]
theorem φ_ofNat_mul (n : ℕ) [n.AtLeastTwo] (f : PowerSeries ℤ) :
    φ ((OfNat.ofNat n : PowerSeries ℤ) * f) = (OfNat.ofNat n : LaurentSeries ℚ) * φ f := by
  simp [φ, map_mul, map_ofNat]

theorem thetaL_φ (f : PowerSeries ℤ) : thetaL ℚ (φ f) = φ (PowerSeries.X * PowerSeries.derivative ℤ f) := by
  ext n
  rw [coeff_thetaL, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hn
  · simp
  · push_neg at hn
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [Int.natAbs_natCast, PowerSeries.coeff_map, PowerSeries.coeff_map]
    cases m with
    | zero => simp [PowerSeries.coeff_zero_X_mul]
    | succ k =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, map_mul, map_add, map_one, map_natCast]
      push_cast
      ring

theorem main (P : PowerSeries ℤ)
    (hP : P = PowerSeries.mk fun n => if n = 0 then 1 else -24 * ∑ d ∈ n.divisors, (d : ℤ)) :
    ((12 : ℚ) • thetaL ℚ (thetaL ℚ jq) - (2 : ℚ) • (HahnSeries.ofPowerSeries ℤ ℚ (P.map (Int.castRingHom ℚ)) * thetaL ℚ jq))
        * jq * (jq - 1728)
      = thetaL ℚ jq ^ 2 * ((14 : ℚ) • jq - 13824) := by

  obtain ⟨-, hQZ, hRZ⟩ := EisensteinSeries.ramanujan_system_qExpansion_int P eisenstein4 eisenstein6 hP rfl rfl
  set Pq := φ P with hPq
  set Q := φ eisenstein4 with hQdef
  set R := φ eisenstein6 with hRdef
  have hQ : 3 * thetaL ℚ Q = Pq * Q - R := by
    have h := congrArg φ hQZ
    rw [φ_ofNat_mul, ← thetaL_φ, φ_sub, φ_mul] at h
    exact h
  have hR : 2 * thetaL ℚ R = Pq * R - Q ^ 2 := by
    have h := congrArg φ hRZ
    rw [φ_ofNat_mul, ← thetaL_φ, φ_sub, φ_mul, φ_pow] at h
    exact h

  set Δ : LaurentSeries ℚ := deltaSeries with hΔdef
  have hΔφ : Δ = φ (PowerSeries.X * dedekindEtaUnit) := by
    rw [hΔdef, deltaSeries, dedekindEtaUnitQ, φ, map_mul, map_mul, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]
  have hD : Q ^ 3 - R ^ 2 = 1728 * Δ := by
    have h := congrArg φ eisenstein4_cube_sub_mk_sq
    rw [φ_sub, φ_pow, φ_pow, φ_ofNat_mul, ← hΔφ] at h
    exact h
  have hj : jq * Δ = Q ^ 3 := by
    rw [hΔdef, jq, deltaSeries, dedekindEtaUnitQ, jNumQ, jNum, mul_mul_mul_comm, HahnSeries.single_mul_single,
      ← map_mul, ← map_mul, mul_assoc, mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, mul_one, mul_one,
      show (-1 : ℤ) + 1 = 0 by norm_num, HahnSeries.single_zero_one, one_mul, hQdef, φ, map_pow, map_pow]
  have hT : thetaL ℚ jq * Δ = -(Q ^ 2 * R) := by
    rw [hΔdef, thetaL_jq_mul_deltaSeries, map_mul, map_pow, map_mul, map_pow]
  have hΔ0 : Δ ≠ 0 := by rw [hΔdef]; exact deltaSeries_ne_zero
  have h1728 : (1728 : LaurentSeries ℚ) ≠ 0 := by
    rw [← map_ofNat (algebraMap ℚ (LaurentSeries ℚ)) 1728]
    exact (map_ne_zero_iff _ (algebraMap ℚ (LaurentSeries ℚ)).injective).mpr (by norm_num)
  set N : LaurentSeries ℚ := Q ^ 3 - R ^ 2 with hNdef
  have hN0 : N ≠ 0 := by rw [hD]; exact mul_ne_zero h1728 hΔ0
  set T := thetaL ℚ jq with hTdef

  have hTN : T * N = (-1728 : ℚ) • (Q ^ 2 * R) := by
    rw [← HahnSeries.C_mul_eq_smul, map_neg, map_ofNat]
    linear_combination (1728 : LaurentSeries ℚ) * hT + T * hD
  have hθ := congrArg (thetaL ℚ) hTN
  rw [map_smul, thetaL_mul, hNdef, map_sub,
    show Q ^ 3 = Q * (Q * Q) by ring, show R ^ 2 = R * R by ring, show Q ^ 2 * R = (Q * Q) * R by ring,
    thetaL_mul Q (Q * Q), thetaL_mul Q Q, thetaL_mul R R, thetaL_mul (Q * Q) R, thetaL_mul Q Q,
    ← HahnSeries.C_mul_eq_smul, map_neg, map_ofNat] at hθ

  have h3 : (3 : LaurentSeries ℚ) ≠ 0 := by
    rw [← map_ofNat (algebraMap ℚ (LaurentSeries ℚ)) 3]
    exact (map_ne_zero_iff _ (algebraMap ℚ (LaurentSeries ℚ)).injective).mpr (by norm_num)
  have h2 : (2 : LaurentSeries ℚ) ≠ 0 := by
    rw [← map_ofNat (algebraMap ℚ (LaurentSeries ℚ)) 2]
    exact (map_ne_zero_iff _ (algebraMap ℚ (LaurentSeries ℚ)).injective).mpr (by norm_num)
  have hθQ : thetaL ℚ Q = (Pq * Q - R) / 3 := by rw [eq_div_iff h3, mul_comm, hQ]
  have hθR : thetaL ℚ R = (Pq * R - Q ^ 2) / 2 := by rw [eq_div_iff h2, mul_comm, hR]
  rw [hθQ, hθR] at hθ
  have hN' : Q * (Q * Q) - R * R ≠ 0 := by
    have : Q * (Q * Q) - R * R = N := by rw [hNdef]; ring
    rwa [this]
  have hθT : thetaL ℚ T =
      ((-1728 : LaurentSeries ℚ) * ((Q * Q) * ((Pq * R - Q ^ 2) / 2) + R * (Q * ((Pq * Q - R) / 3) + Q * ((Pq * Q - R) / 3)))
        - T * (Q * (Q * ((Pq * Q - R) / 3) + Q * ((Pq * Q - R) / 3)) + (Q * Q) * ((Pq * Q - R) / 3)
              - (R * ((Pq * R - Q ^ 2) / 2) + R * ((Pq * R - Q ^ 2) / 2))))
        / (Q * (Q * Q) - R * R) := by
    rw [eq_div_iff hN']
    linear_combination hθ
  have hTdiv : T = -(Q ^ 2 * R) / Δ := by rw [eq_div_iff hΔ0, hT]
  have hjdiv : jq = Q ^ 3 / Δ := by rw [eq_div_iff hΔ0, hj]
  have hΔdiv : Δ = (Q ^ 3 - R ^ 2) / 1728 := by rw [eq_div_iff h1728, mul_comm, ← hNdef, hD]

  rw [← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, map_ofNat, map_ofNat,
    map_ofNat, show HahnSeries.ofPowerSeries ℤ ℚ (P.map (Int.castRingHom ℚ)) = Pq from rfl, hθT, hTdiv, hjdiv, hΔdiv]
  have hN'' : Q ^ 3 - R ^ 2 ≠ 0 := by rwa [hNdef] at hN0
  field_simp
  ring

end ModularCurve.RB1

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_thetaL_thetaL_jq_sub_smul_mul_jq_mul_jq_sub_eq.ModularCurve in
theorem solution (P : PowerSeries ℤ)
    (hP : P = PowerSeries.mk fun n => if n = 0 then 1 else -24 * ∑ d ∈ n.divisors, (d : ℤ)) :
    ((12 : ℚ) • thetaL ℚ (thetaL ℚ jq) - (2 : ℚ) • (HahnSeries.ofPowerSeries ℤ ℚ (P.map (Int.castRingHom ℚ)) * thetaL ℚ jq))
        * jq * (jq - 1728)
      = thetaL ℚ jq ^ 2 * ((14 : ℚ) • jq - 13824) :=
  ModularCurve.RB1.main P hP

end S_ModularCurve_thetaL_thetaL_jq_sub_smul_mul_jq_mul_jq_sub_eq
end P2MW
export P2MW.S_ModularCurve_thetaL_thetaL_jq_sub_smul_mul_jq_mul_jq_sub_eq (solution)
