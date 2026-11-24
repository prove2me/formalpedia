-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localInf_weights_and_jets
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T18:35:19.222566+00:00
-- url     : https://prove2.me/submissions/aec6b141-bc36-439f-93ef-ff94d0f478c6

import Definitions.Def_HodgeComputerSSR_LocalInfCore
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localInf_weights_alg

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

namespace SymmetricSexticResidual.LocalResidueInfAlg
open Polynomial SymmetricSexticResidual.K5Field SymmetricSexticResidual.CoverAlgebra QuadraticCovers
private abbrev coeff_quadU := @SymmetricSexticResidual.LocalResidueInf.coeff_quadU
lemma quadU_mul2_coeff3 {R : Type*} [CommRing R] (a0 a1 a2 b0 b1 b2 : R) :
    (CoverParams.quadU a0 a1 a2 * CoverParams.quadU b0 b1 b2).coeff 3 = a1 * b2 + a2 * b1 := by
  have heq : CoverParams.quadU a0 a1 a2 * CoverParams.quadU b0 b1 b2 =
      C (a0 * b0) + C (a0 * b1 + a1 * b0) * X + C (a0 * b2 + a1 * b1 + a2 * b0) * X ^ 2 +
      C (a1 * b2 + a2 * b1) * X ^ 3 + C (a2 * b2) * X ^ 4 := by
    simp only [CoverParams.quadU, map_add, map_mul]; ring
  rw [heq]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C, Nat.reduceEqDiff, ↓reduceIte, mul_zero,
    zero_add, add_zero, mul_one]

lemma quadU_mul3_coeff5 {R : Type*} [CommRing R] (a0 a1 a2 b0 b1 b2 c0 c1 c2 : R) :
    (CoverParams.quadU a0 a1 a2 * CoverParams.quadU b0 b1 b2 * CoverParams.quadU c0 c1 c2).coeff 5 =
      a1 * b2 * c2 + a2 * b1 * c2 + a2 * b2 * c1 := by
  have heq : CoverParams.quadU a0 a1 a2 * CoverParams.quadU b0 b1 b2 * CoverParams.quadU c0 c1 c2 =
      C (a0 * b0 * c0) +
      C (a0 * b0 * c1 + a0 * b1 * c0 + a1 * b0 * c0) * X +
      C (a0 * b0 * c2 + a0 * b1 * c1 + a0 * b2 * c0 + a1 * b0 * c1 + a1 * b1 * c0 + a2 * b0 * c0) * X ^ 2 +
      C (a0 * b1 * c2 + a0 * b2 * c1 + a1 * b0 * c2 + a1 * b1 * c1 + a1 * b2 * c0 + a2 * b0 * c1 + a2 * b1 * c0) * X ^ 3 +
      C (a0 * b2 * c2 + a1 * b1 * c2 + a1 * b2 * c1 + a2 * b0 * c2 + a2 * b1 * c1 + a2 * b2 * c0) * X ^ 4 +
      C (a1 * b2 * c2 + a2 * b1 * c2 + a2 * b2 * c1) * X ^ 5 +
      C (a2 * b2 * c2) * X ^ 6 := by
    simp only [CoverParams.quadU, map_add, map_mul]; ring
  rw [heq]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C, Nat.reduceEqDiff, ↓reduceIte, mul_zero,
    zero_add, add_zero, mul_one]

lemma quadU_mul3_coeff4 {R : Type*} [CommRing R] (a0 a1 a2 b0 b1 b2 c0 c1 c2 : R) :
    (CoverParams.quadU a0 a1 a2 * CoverParams.quadU b0 b1 b2 * CoverParams.quadU c0 c1 c2).coeff 4 =
      a0 * b2 * c2 + a1 * b1 * c2 + a1 * b2 * c1 + a2 * b0 * c2 + a2 * b1 * c1 + a2 * b2 * c0 := by
  have heq : CoverParams.quadU a0 a1 a2 * CoverParams.quadU b0 b1 b2 * CoverParams.quadU c0 c1 c2 =
      C (a0 * b0 * c0) +
      C (a0 * b0 * c1 + a0 * b1 * c0 + a1 * b0 * c0) * X +
      C (a0 * b0 * c2 + a0 * b1 * c1 + a0 * b2 * c0 + a1 * b0 * c1 + a1 * b1 * c0 + a2 * b0 * c0) * X ^ 2 +
      C (a0 * b1 * c2 + a0 * b2 * c1 + a1 * b0 * c2 + a1 * b1 * c1 + a1 * b2 * c0 + a2 * b0 * c1 + a2 * b1 * c0) * X ^ 3 +
      C (a0 * b2 * c2 + a1 * b1 * c2 + a1 * b2 * c1 + a2 * b0 * c2 + a2 * b1 * c1 + a2 * b2 * c0) * X ^ 4 +
      C (a1 * b2 * c2 + a2 * b1 * c2 + a2 * b2 * c1) * X ^ 5 +
      C (a2 * b2 * c2) * X ^ 6 := by
    simp only [CoverParams.quadU, map_add, map_mul]; ring
  rw [heq]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C, Nat.reduceEqDiff, ↓reduceIte, mul_zero,
    zero_add, add_zero, mul_one]

lemma quadU_mul4_coeff7 {R : Type*} [CommRing R] (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : R) :
    (CoverParams.quadU a0 a1 a2 * CoverParams.quadU b0 b1 b2 *
     CoverParams.quadU c0 c1 c2 * CoverParams.quadU d0 d1 d2).coeff 7 =
      a1 * b2 * c2 * d2 + a2 * b1 * c2 * d2 + a2 * b2 * c1 * d2 + a2 * b2 * c2 * d1 := by
  set P : R[X] := C (a0 * b0) + C (a0 * b1 + a1 * b0) * X + C (a0 * b2 + a1 * b1 + a2 * b0) * X ^ 2 +
      C (a1 * b2 + a2 * b1) * X ^ 3 + C (a2 * b2) * X ^ 4
  set Q : R[X] := C (c0 * d0) + C (c0 * d1 + c1 * d0) * X + C (c0 * d2 + c1 * d1 + c2 * d0) * X ^ 2 +
      C (c1 * d2 + c2 * d1) * X ^ 3 + C (c2 * d2) * X ^ 4
  have hp : CoverParams.quadU a0 a1 a2 * CoverParams.quadU b0 b1 b2 = P := by
    simp only [P, CoverParams.quadU, map_add, map_mul]; ring
  have hq : CoverParams.quadU c0 c1 c2 * CoverParams.quadU d0 d1 d2 = Q := by
    simp only [Q, CoverParams.quadU, map_add, map_mul]; ring
  rw [mul_assoc, hp, hq, Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => P.coeff i * Q.coeff j) 7]
  simp only [P, Q, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceSub,
    Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C, Nat.reduceEqDiff, ↓reduceIte,
    mul_zero, zero_mul, zero_add, add_zero, mul_one]
  ring

lemma quadU_mul4_coeff6 {R : Type*} [CommRing R] (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : R) :
    (CoverParams.quadU a0 a1 a2 * CoverParams.quadU b0 b1 b2 *
     CoverParams.quadU c0 c1 c2 * CoverParams.quadU d0 d1 d2).coeff 6 =
      a0 * b2 * c2 * d2 + a1 * b1 * c2 * d2 + a1 * b2 * c1 * d2 + a1 * b2 * c2 * d1 +
      a2 * b0 * c2 * d2 + a2 * b1 * c1 * d2 + a2 * b1 * c2 * d1 +
      a2 * b2 * c0 * d2 + a2 * b2 * c1 * d1 + a2 * b2 * c2 * d0 := by
  set P : R[X] := C (a0 * b0) + C (a0 * b1 + a1 * b0) * X + C (a0 * b2 + a1 * b1 + a2 * b0) * X ^ 2 +
      C (a1 * b2 + a2 * b1) * X ^ 3 + C (a2 * b2) * X ^ 4
  set Q : R[X] := C (c0 * d0) + C (c0 * d1 + c1 * d0) * X + C (c0 * d2 + c1 * d1 + c2 * d0) * X ^ 2 +
      C (c1 * d2 + c2 * d1) * X ^ 3 + C (c2 * d2) * X ^ 4
  have hp : CoverParams.quadU a0 a1 a2 * CoverParams.quadU b0 b1 b2 = P := by
    simp only [P, CoverParams.quadU, map_add, map_mul]; ring
  have hq : CoverParams.quadU c0 c1 c2 * CoverParams.quadU d0 d1 d2 = Q := by
    simp only [Q, CoverParams.quadU, map_add, map_mul]; ring
  rw [mul_assoc, hp, hq, Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => P.coeff i * Q.coeff j) 6]
  simp only [P, Q, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceSub,
    Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C, Nat.reduceEqDiff, ↓reduceIte,
    mul_zero, zero_mul, zero_add, add_zero, mul_one]
  ring

lemma k5Params_Q5_c5_eq : k5Params.Q5_z.coeff 5 = Q5_c5 S_K Q_K := by
  have h : k5Params.Q5_z =
      k5Params.q20 * k5Params.cb_h * k5Params.cb_h -
      k5Params.q11 * k5Params.ca_h * k5Params.cb_h +
      k5Params.q02 * k5Params.ca_h * k5Params.ca_h := by
    unfold CoverParams.Q5_z; ring
  rw [h, Polynomial.coeff_add, Polynomial.coeff_sub]
  simp only [CoverParams.q20, CoverParams.q11, CoverParams.q02, CoverParams.ca_h, CoverParams.cb_h,
    quadU_mul3_coeff5, CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3,
    k5Params_inv7, k5Params_S, k5Params_Q, Q5_c5]
  ring

lemma k5Params_Q5_c4_eq : k5Params.Q5_z.coeff 4 = Q5_c4 S_K Q_K := by
  have h : k5Params.Q5_z =
      k5Params.q20 * k5Params.cb_h * k5Params.cb_h -
      k5Params.q11 * k5Params.ca_h * k5Params.cb_h +
      k5Params.q02 * k5Params.ca_h * k5Params.ca_h := by
    unfold CoverParams.Q5_z; ring
  rw [h, Polynomial.coeff_add, Polynomial.coeff_sub]
  simp only [CoverParams.q20, CoverParams.q11, CoverParams.q02, CoverParams.ca_h, CoverParams.cb_h,
    quadU_mul3_coeff4, CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3,
    k5Params_inv7, k5Params_S, k5Params_Q, Q5_c4]
  ring

lemma k5Params_Q7_c7_eq : k5Params.Q7_z.coeff 7 = Q7_c7 S_K Q_K := by
  have h : k5Params.Q7_z =
      k5Params.c30 * k5Params.cb_h * k5Params.cb_h * k5Params.cb_h -
      k5Params.c21 * k5Params.ca_h * k5Params.cb_h * k5Params.cb_h +
      k5Params.c12 * k5Params.ca_h * k5Params.ca_h * k5Params.cb_h -
      k5Params.c03 * k5Params.ca_h * k5Params.ca_h * k5Params.ca_h := by
    unfold CoverParams.Q7_z; ring
  rw [h, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_sub]
  simp only [CoverParams.c30, CoverParams.c21, CoverParams.c12, CoverParams.c03,
    CoverParams.ca_h, CoverParams.cb_h, quadU_mul4_coeff7, CoverParams.inv9, CoverParams.inv27,
    CoverParams.inv81, CoverParams.inv243, k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q, Q7_c7]
  ring

lemma k5Params_Q7_c6_eq : k5Params.Q7_z.coeff 6 = Q7_c6 S_K Q_K := by
  have h : k5Params.Q7_z =
      k5Params.c30 * k5Params.cb_h * k5Params.cb_h * k5Params.cb_h -
      k5Params.c21 * k5Params.ca_h * k5Params.cb_h * k5Params.cb_h +
      k5Params.c12 * k5Params.ca_h * k5Params.ca_h * k5Params.cb_h -
      k5Params.c03 * k5Params.ca_h * k5Params.ca_h * k5Params.ca_h := by
    unfold CoverParams.Q7_z; ring
  rw [h, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_sub]
  simp only [CoverParams.c30, CoverParams.c21, CoverParams.c12, CoverParams.c03,
    CoverParams.ca_h, CoverParams.cb_h, quadU_mul4_coeff6, CoverParams.inv9, CoverParams.inv27,
    CoverParams.inv81, CoverParams.inv243, k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q, Q7_c6]
  ring

lemma k5Params_p21_c3_eq :
    (-k5Params.q11 * k5Params.cb_h + 2 * k5Params.q02 * k5Params.ca_h).coeff 3 = p21_c3 S_K Q_K := by
  have h : -k5Params.q11 * k5Params.cb_h + 2 * k5Params.q02 * k5Params.ca_h =
      -(k5Params.q11 * k5Params.cb_h) + C 2 * (k5Params.q02 * k5Params.ca_h) := by
    rw [map_ofNat]; ring
  rw [h, Polynomial.coeff_add, Polynomial.coeff_neg, Polynomial.coeff_C_mul]
  simp only [CoverParams.q11, CoverParams.q02, CoverParams.ca_h, CoverParams.cb_h,
    quadU_mul2_coeff3, CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3,
    k5Params_inv7, k5Params_S, k5Params_Q, p21_c3]
  ring

lemma k5Params_p32_c5_eq :
    (-k5Params.c21 * k5Params.cb_h ^ 2 + 2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h -
      3 * k5Params.c03 * k5Params.ca_h ^ 2).coeff 5 = p32_c5 S_K Q_K := by
  have h : -k5Params.c21 * k5Params.cb_h ^ 2 + 2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h -
      3 * k5Params.c03 * k5Params.ca_h ^ 2 =
      -(k5Params.c21 * k5Params.cb_h * k5Params.cb_h) +
      C 2 * (k5Params.c12 * k5Params.ca_h * k5Params.cb_h) -
      C 3 * (k5Params.c03 * k5Params.ca_h * k5Params.ca_h) := by
    rw [map_ofNat, map_ofNat]; ring
  rw [h, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_neg,
    Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
  simp only [CoverParams.c21, CoverParams.c12, CoverParams.c03, CoverParams.ca_h, CoverParams.cb_h,
    quadU_mul3_coeff5, CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3,
    k5Params_inv7, k5Params_S, k5Params_Q, p32_c5]
  ring

lemma k5Params_p31_c3_eq :
    (k5Params.c12 * k5Params.cb_h - 3 * k5Params.c03 * k5Params.ca_h).coeff 3 = p31_c3 S_K Q_K := by
  have h : k5Params.c12 * k5Params.cb_h - 3 * k5Params.c03 * k5Params.ca_h =
      k5Params.c12 * k5Params.cb_h - C 3 * (k5Params.c03 * k5Params.ca_h) := by
    rw [map_ofNat]; ring
  rw [h, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  simp only [CoverParams.c12, CoverParams.c03, CoverParams.ca_h, CoverParams.cb_h,
    quadU_mul2_coeff3, CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3,
    k5Params_inv7, k5Params_S, k5Params_Q, p31_c3]
  ring

end SymmetricSexticResidual.LocalResidueInfAlg

noncomputable section
namespace SymmetricSexticResidual.LocalResidueInf
open Polynomial
open scoped LaurentSeries PowerSeries
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  SymmetricSexticResidual.LocalResidueU0 SymmetricSexticResidual.LocalResidueInfAlg
  QuadraticCovers

private abbrev W1_inf_weights_alg := @HodgeComputer.SymmetricSexticResidual.Proof.localInf_weights_alg.W1_inf_weights_alg

lemma W1_inf_valDual :
    ValDual 0 W1_inf ⟨-(k5Params.Cv0 / k5Params.Bv2), k5Params.Cv0 * k5Params.Bv1 / k5Params.Bv2 ^ 2⟩ := by
  have hw := HasValGe_W1_inf
  have heq : HahnSeries.C k5Params.Av0 * W1_inf ^ 2 +
      evalInvT k5Params.Bv * W1_inf + HahnSeries.C k5Params.Cv0 * HahnSeries.single (-2) 1 = 0 := by
    have h0 := congrArg (HahnSeries.C k5Params.Av0 * ·) W1_inf_eq
    rw [mul_zero] at h0
    have hAv : HahnSeries.C k5Params.Av0 * evalInvT k5Params.bW = evalInvT k5Params.Bv := by
      rw [CoverParams.bW, map_mul, evalInvT_C, ← mul_assoc, ← map_mul, k5Params_Av0_mul_inv, map_one, one_mul]
    have hCv : HahnSeries.C k5Params.Av0 * evalInvT k5Params.cW =
        HahnSeries.C k5Params.Cv0 * HahnSeries.single (-2) 1 := by
      rw [CoverParams.cW, map_mul, map_pow, evalInvT_C, evalInvT_X, HahnSeries.single_pow,
        ← mul_assoc, ← map_mul]
      have : k5Params.Av0 * (k5Params.Cv0 * k5Params.Av0_inv) = k5Params.Cv0 := by
        rw [mul_left_comm, k5Params_Av0_mul_inv, mul_one]
      rw [this]; simp
    linear_combination h0 - hAv * W1_inf - hCv
  have hBv_D : ValDual (-2) (evalInvT k5Params.Bv) ⟨k5Params.Bv2, k5Params.Bv1⟩ := by
    have hdeg : k5Params.Bv.natDegree ≤ 2 := by
      simp only [CoverParams.Bv, CoverParams.quadU]
      exact (Polynomial.natDegree_add_le _ _).trans (max_le
        ((Polynomial.natDegree_add_le _ _).trans (max_le (by simp)
          ((Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_le.trans (by omega)))))
        ((Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_pow_le 2)))
    exact ((ValDual.of_evalInvT k5Params.Bv hdeg (by omega)).eq_k (by omega)).eq_d (by
      ext <;> simp only [CoverParams.Bv, coeff_quadU])
  have hsq : HasValGe 0 (HahnSeries.C k5Params.Av0 * W1_inf ^ 2) :=
    ((HasValGe.of_C _).mul (hw.pow 2)).mono (by omega)
  have hBvW_D : ValDual (-2) (evalInvT k5Params.Bv * W1_inf)
      (⟨k5Params.Bv2, k5Params.Bv1⟩ * ⟨W1_inf.coeff 0, W1_inf.coeff 1⟩) :=
    (hBv_D.mul ⟨hw, rfl, rfl⟩).eq_k (by omega)
  have hCs : HahnSeries.C k5Params.Cv0 * HahnSeries.single (-2 : ℤ) (1 : K5) =
      HahnSeries.single (-2 : ℤ) k5Params.Cv0 := by
    rw [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
  rw [hCs] at heq
  have hc_m2 := congrArg (fun f : LaurentSeries K5 => f.coeff (-2)) heq
  rw [HahnSeries.coeff_add, HahnSeries.coeff_add, hsq (-2) (by omega), zero_add, hBvW_D.c0,
    HahnSeries.coeff_single_same, HahnSeries.coeff_zero] at hc_m2
  have hc0 : W1_inf.coeff 0 = -(k5Params.Cv0 / k5Params.Bv2) := by
    apply mul_left_cancel₀ k5Params_Bv2_ne
    rw [mul_neg, mul_div_cancel₀ _ k5Params_Bv2_ne]
    simp only [Dual.mul_val] at hc_m2; linear_combination hc_m2
  have hc_m1 := congrArg (fun f : LaurentSeries K5 => f.coeff (-1)) heq
  have hBvW_c1 : (evalInvT k5Params.Bv * W1_inf).coeff (-1) =
      (⟨k5Params.Bv2, k5Params.Bv1⟩ * ⟨W1_inf.coeff 0, W1_inf.coeff 1⟩ : Dual K5).eps := hBvW_D.c1
  rw [HahnSeries.coeff_add, HahnSeries.coeff_add, hsq (-1) (by omega), zero_add, hBvW_c1,
    HahnSeries.coeff_single_of_ne (by decide : (-1 : ℤ) ≠ -2),
    add_zero, HahnSeries.coeff_zero] at hc_m1
  have hc1 : W1_inf.coeff 1 = k5Params.Cv0 * k5Params.Bv1 / k5Params.Bv2 ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 k5Params_Bv2_ne)
    rw [mul_div_cancel₀ _ (pow_ne_zero 2 k5Params_Bv2_ne)]
    simp only [Dual.mul_eps] at hc_m1
    have hmul := congrArg (k5Params.Bv2 * ·) hc_m1
    rw [mul_zero] at hmul
    rw [hc0] at hmul
    have hmul' : k5Params.Bv2 ^ 2 * W1_inf.coeff 1 + k5Params.Bv1 * (k5Params.Bv2 * -(k5Params.Cv0 / k5Params.Bv2)) = 0 := by
      linear_combination hmul
    rw [mul_neg, mul_div_cancel₀ _ k5Params_Bv2_ne] at hmul'
    linear_combination hmul'
  exact ⟨hw, hc0, hc1⟩


private lemma W1_inf_weights :
    let d2_2 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d2_2)
    let d2_1 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d2_1)
    let d2_0 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d2_0)
    let d1 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d1_z)
    let d0 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d0_z)
    let res := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.res_z)
    let pref := -(HahnSeries.single (-1 : ℤ) (1 : K5) ^ 3 * W1_inf * evalInvT k5Params.cb_h ^ 4) /
      (81 * HahnSeries.C k5Params.Av0 * (2 * W1_inf + evalInvT k5Params.bW) * evalInvT k5Params.Q5_z ^ 3 * res)
    let A4 := pref * ((-d2_1 ^ 3 + 2 * d2_2 * d2_1 * d2_0) * d0 - (-d2_1 ^ 2 * d2_0 + d2_2 * d2_0 ^ 2) * d1)
    let A3 := pref * ((d2_2 * (d2_1 ^ 2 - d2_2 * d2_0)) * d0 - (d2_2 * d2_1 * d2_0) * d1)
    let A2 := pref * ((-d2_2 ^ 2 * d2_1) * d0 - (-d2_2 ^ 2 * d2_0) * d1)
    let A1 := pref * (d2_2 ^ 3 * d0)
    let A0 := pref * (-d2_2 ^ 3 * d1)
    let S3Q := S_K - 3 * Q_K; let T59 := 5 * T_K - 9
    ValDual 3 A4
      ⟨-(279006525 / 64 : K5) * T_K * T59 ^ 2 / (S3Q ^ 8 * L_K),
       (13286025 / 12544 : K5) * T_K * T59 ^ 2 * P44_fn S_K Q_K T_K / (S3Q ^ 11 * L_K ^ 2)⟩ ∧
    ValLead 4 A3 ((531441 / 448 : K5) * T_K * T59 * (35 * S_K * T_K + 133 * S_K - 420 * Q_K + 225 * T_K - 45) / S3Q ^ 8) ∧
    ValLead 4 A2 (-(177147 / 400 : K5) * T_K / S3Q ^ 5) ∧
    HasValGe 5 A1 ∧ HasValGe 5 A0 ∧
    HasValGe (-32) res ∧ res.coeff (-32) ≠ 0 := by
  intro d2_2 d2_1 d2_0 d1 d0 res pref A4 A3 A2 A1 A0 S3Q T59
  have hS3Q := S_K_sub_3Q_ne; have hL := L_K_ne_zero; have hT59 := fiveT_sub_9_ne
  set Bv2 : K5 := w1_Bv2 S_K Q_K
  set Bv1 : K5 := w1_Bv1 S_K Q_K T_K
  set Cv0 : K5 := w1_Cv0 T_K
  have hBv2_eq : k5Params.Bv2 = Bv2 := by
    simp only [CoverParams.Bv2, CoverParams.inv243, k5Params_inv3, k5Params_S, k5Params_Q, Bv2, w1_Bv2]; ring
  have hBv1_eq : k5Params.Bv1 = Bv1 := by
    simp only [CoverParams.Bv1, CoverParams.inv9, CoverParams.inv27, CoverParams.inv243, k5Params_inv3,
      k5Params_inv7, k5Params_S, k5Params_Q, k5Params_T, Bv1, w1_Bv1]; ring
  have hCv0_eq : k5Params.Cv0 = Cv0 := by
    simp only [CoverParams.Cv0, CoverParams.inv243, k5Params_inv3, k5Params_T, Cv0, w1_Cv0]; ring
  set w0 : K5 := w1_w0 S_K Q_K T_K
  set w1 : K5 := w1_w1 S_K Q_K T_K
  have hW_D : ValDual 0 W1_inf (w1_WD S_K Q_K T_K) := by
    simpa only [hCv0_eq, hBv2_eq, hBv1_eq, w1_WD, w1_w0, w1_w1, neg_div] using W1_inf_valDual
  set cbD : Dual K5 := w1_cbD S_K Q_K
  have hcb_D : ValDual (-2) (evalInvT k5Params.cb_h) cbD :=
    (ValDual.of_evalInvT k5Params.cb_h deg2_cb (by omega)).eq_d (by
      ext <;> (simp only [CoverParams.cb_h, coeff_quadU, CoverParams.inv9, CoverParams.inv27,
        k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q, cbD, w1_cbD]; ring))
  have hD22_D : ValDual (-5) d2_2 (w1_D22 S_K Q_K) := by
    simpa only [d2_2, CoverParams.d2_2, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using
      ((ValDual.of_evalInvT k5Params.Q5_z k5Params_Q5_z_natDegree_le (by omega)).eq_k (by omega)).eq_d
        (by ext; exact k5Params_Q5_c5_eq; exact k5Params_Q5_c4_eq)
  have hD33_D : ValDual (-7) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_3))
      (w1_D33 S_K Q_K) := by
    simpa only [CoverParams.d3_3, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using
      ((ValDual.of_evalInvT k5Params.Q7_z k5Params_Q7_z_natDegree_le (by omega)).eq_k (by omega)).eq_d
        (by ext; exact k5Params_Q7_c7_eq; exact k5Params_Q7_c6_eq)
  set c0_0 : K5 := w1_c0_0 T_K
  set k2_0 : K5 := w1_k2_0 T_K
  set k3_0 : K5 := w1_k3_0 K5
  have hc0W_L : ValLead (-2) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.c0W)) c0_0 :=
    (evalInvT_toUW_valLead_W1 _ _ _).eq_c (by simp only [CoverParams.c0_V0, CoverParams.inv81, k5Params_inv3, k5Params_T, c0_0, w1_c0_0]; ring)
  have hk2W_L : ValLead (-2) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.k2W)) k2_0 :=
    (evalInvT_toUW_valLead_W1 _ _ _).eq_c (by simp only [CoverParams.k2_V0, CoverParams.inv81, k5Params_inv3, k5Params_T, k2_0, w1_k2_0]; ring)
  have hk3W_L : ValLead (-2) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.k3W)) k3_0 :=
    (evalInvT_toUW_valLead_W1 _ _ _).eq_c (by simp only [CoverParams.k3_V0, CoverParams.inv243, k5Params_inv3, k3_0, w1_k3_0]; ring)
  have hD21_L : ValLead (-5) d2_1 (w1_D21_v S_K Q_K T_K) := by
    simp only [d2_1, CoverParams.d2_1, PairAlg.map_smul, PairAlg.evalAt_smul]
    have hp := (ValDual.of_evalInvT _ k5Params_p21_natDegree_le (by omega)).toValLead.eq_c k5Params_p21_c3_eq
    exact (hp.mul hc0W_L).eq_k (by omega)
  have hq02_L : ValLead (-2) (evalInvT k5Params.q02) (-(4 / 9 : K5) * S_K + (4 / 3) * Q_K) :=
    (ValDual.of_evalInvT k5Params.q02 deg2_q02 (by omega)).toValLead.eq_c (by
      simp only [CoverParams.q02, coeff_quadU, CoverParams.inv9, k5Params_inv3, k5Params_S, k5Params_Q]; ring)
  have hc03_L : ValLead (-2) (evalInvT k5Params.c03) (4 / 9 : K5) :=
    (ValDual.of_evalInvT k5Params.c03 deg2_c03 (by omega)).toValLead.eq_c (by
      simp only [CoverParams.c03, coeff_quadU, CoverParams.inv9, k5Params_inv3]; ring)
  set D20_v : K5 := w1_D20_v S_K Q_K T_K
  have hD20_L : ValLead (-6) d2_0 D20_v := by
    simp only [d2_0, CoverParams.d2_0, CoverParams.pmul, PairAlg.map_add, PairAlg.map_smul,
      PairAlg.map_mul, PairAlg.map_W, PairAlg.evalAt_add, PairAlg.evalAt_smul,
      PairAlg.evalAt_mul _ _ W1_inf W1_inf_eq, PairAlg.evalAt_W, map_pow]
    exact (((hq02_L.mul (hc0W_L.mul hc0W_L)).eq_k (by omega)).add
      (((hcb_D.toValLead.pow 2).mul (hW_D.toValLead.mul hk2W_L)).eq_k (by omega))).eq_c
        (by dsimp only [D20_v, w1_D20_v, w1_WD, c0_0, k2_0, cbD]; ring)
  have hD20_D : ValDual (-6) d2_0 (w1_D20 S_K Q_K T_K (d2_0.coeff (-5))) := ⟨hD20_L.val, hD20_L.c0, rfl⟩
  have hD32_L : ValLead (-7) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_2)) (w1_D32_v S_K Q_K T_K) := by
    simp only [CoverParams.d3_2, PairAlg.map_smul, PairAlg.evalAt_smul]
    have hp := (ValDual.of_evalInvT _ k5Params_p32_natDegree_le (by omega)).toValLead.eq_c k5Params_p32_c5_eq
    exact (hp.mul hc0W_L).eq_k (by omega)
  have hD31_L : ValLead (-7) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_1)) (w1_D31_v S_K Q_K T_K) := by
    simp only [CoverParams.d3_1, CoverParams.pmul, PairAlg.map_smul, PairAlg.map_mul,
      PairAlg.evalAt_smul, PairAlg.evalAt_mul _ _ W1_inf W1_inf_eq]
    have hp := (ValDual.of_evalInvT _ k5Params_p31_natDegree_le (by omega)).toValLead.eq_c k5Params_p31_c3_eq
    exact (hp.mul (hc0W_L.mul hc0W_L)).eq_k (by omega) |>.eq_c (by dsimp only [w1_D31_v, c0_0]; ring)
  set D30_v : K5 := w1_D30_v S_K Q_K T_K
  have hD30_L : ValLead (-8) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_0)) D30_v := by
    simp only [CoverParams.d3_0, CoverParams.pmul, PairAlg.map_add, PairAlg.map_smul, PairAlg.map_mul,
      PairAlg.map_W, PairAlg.evalAt_add, PairAlg.evalAt_smul, PairAlg.evalAt_mul _ _ W1_inf W1_inf_eq,
      PairAlg.evalAt_W, map_neg, map_pow]
    exact (((hc03_L.neg.mul (hc0W_L.mul (hc0W_L.mul hc0W_L))).eq_k (by omega)).add
      (((hcb_D.toValLead.pow 3).mul ((hW_D.toValLead.mul hW_D.toValLead).mul hk3W_L)).eq_k (by omega))).eq_c
        (by dsimp only [D30_v, w1_D30_v, w1_WD, c0_0, k3_0, cbD]; ring)
  -- `d1` (`ValDual (-18)`), `d0` (`ValLead (-18)`), `res` (`ValDual (-32)`):
  set D22 : Dual K5 := w1_D22 S_K Q_K
  set D33 : Dual K5 := w1_D33 S_K Q_K
  set D20 : Dual K5 := w1_D20 S_K Q_K T_K (d2_0.coeff (-5))
  set D21_v := w1_D21_v S_K Q_K T_K
  set D32_v := w1_D32_v S_K Q_K T_K
  set D31_v := w1_D31_v S_K Q_K T_K
  set diff12_v := w1_diff12_v S_K Q_K T_K
  have hdiff12_L : ValLead (-12)
      (d2_2 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_2) -
       d2_1 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_3)) diff12_v :=
    ((hD22_D.toValLead.mul hD32_L).eq_k (by omega)).sub ((hD21_L.mul hD33_D.toValLead).eq_k (by omega))
  set d1_main : Dual K5 := w1_d1_main S_K Q_K T_K (d2_0.coeff (-5))
  set d1_sub_v : K5 := w1_d1_sub_v S_K Q_K T_K
  have hd1_D : ValDual (-18) d1 (w1_d1_D S_K Q_K T_K (d2_0.coeff (-5))) := by
    have heq : d1 = -(d2_2 * d2_0 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_3)) +
        (d2_2 * (d2_2 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_1)) -
         d2_1 * (d2_2 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_2) -
                 d2_1 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_3))) := by
      simp only [d1, d2_2, d2_1, d2_0, CoverParams.d1_z, CoverParams.pmul, PairAlg.map_sub,
        PairAlg.map_mul, PairAlg.evalAt_sub, PairAlg.evalAt_mul _ _ W1_inf W1_inf_eq]; ring
    rw [heq]
    have hm : ValDual (-18) (-(d2_2 * d2_0 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_3))) d1_main :=
      (((hD22_D.mul hD20_D).mul hD33_D).neg).eq_k (by omega)
    have hs : ValLead (-17) (d2_2 * (d2_2 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_1)) -
        d2_1 * (d2_2 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_2) -
                d2_1 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_3))) d1_sub_v :=
      (((hD22_D.toValLead.mul (hD22_D.toValLead.mul hD31_L)).eq_k (by omega)).sub
        ((hD21_L.mul hdiff12_L).eq_k (by omega))).eq_c (by dsimp only [d1_sub_v, w1_d1_sub_v]; ring)
    exact (hm.add_shift1 hs).eq_d (by ext <;> simp only [w1_d1_D, d1_main, d1_sub_v, Dual.add_val, Dual.add_eps, add_zero])
  set d0_v : K5 := w1_d0_v S_K Q_K T_K
  have hd0_L : ValLead (-18) d0 d0_v := by
    have heq : d0 = d2_2 * (d2_2 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_0)) -
        d2_0 * (d2_2 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_2) -
                d2_1 * PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_3)) := by
      simp only [d0, d2_2, d2_1, d2_0, CoverParams.d0_z, CoverParams.pmul, PairAlg.map_sub,
        PairAlg.map_mul, PairAlg.evalAt_sub, PairAlg.evalAt_mul _ _ W1_inf W1_inf_eq]
    rw [heq]
    exact (((hD22_D.toValLead.mul (hD22_D.toValLead.mul hD30_L)).eq_k (by omega)).sub
      ((hD20_L.mul hdiff12_L).eq_k (by omega))).eq_c (by dsimp only [d0_v, w1_d0_v]; ring)
  set res_main : Dual K5 := w1_res_main S_K Q_K T_K (d2_0.coeff (-5))
  set res_sub_v : K5 := w1_res_sub_v S_K Q_K T_K
  have hres_D : ValDual (-32) res (w1_res_D S_K Q_K T_K (d2_0.coeff (-5))) := by
    set e3 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_3)
    set e2 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_2)
    set e1 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_1)
    set e0 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d3_0)
    have hsplit : res = (d2_0 ^ 3 * e3 ^ 2 +
        (-d2_1 * d2_0 ^ 2 * e3 * e2 + d2_2 * d2_0 ^ 2 * e2 ^ 2 -
         2 * d2_2 * d2_0 ^ 2 * e3 * e1 + 3 * d2_2 * d2_1 * d2_0 * e3 * e0 -
         2 * d2_2 ^ 2 * d2_0 * e2 * e0 + d2_2 ^ 3 * e0 ^ 2)) +
        (d2_1 ^ 2 * d2_0 * e3 * e1 - d2_2 * d2_1 * d2_0 * e2 * e1 +
         d2_2 ^ 2 * d2_0 * e1 ^ 2 - d2_1 ^ 3 * e3 * e0 +
         d2_2 * d2_1 ^ 2 * e2 * e0 - d2_2 ^ 2 * d2_1 * e1 * e0) := by
      dsimp only [res, d2_2, d2_1, d2_0, e3, e2, e1, e0]
      rw [CoverParams.res_z, map_syl5Pair, evalAt_syl5Pair _ _ _ _ _ _ _ _ _ W1_inf W1_inf_eq]
      simp only [syl5]; ring
    rw [hsplit]
    have hm : ValDual (-32) (d2_0 ^ 3 * e3 ^ 2) res_main :=
      ((hD20_D.pow 3).mul (hD33_D.pow 2)).eq_k (by omega)
    have hs : ValLead (-31)
        (-d2_1 * d2_0 ^ 2 * e3 * e2 + d2_2 * d2_0 ^ 2 * e2 ^ 2 -
         2 * d2_2 * d2_0 ^ 2 * e3 * e1 + 3 * d2_2 * d2_1 * d2_0 * e3 * e0 -
         2 * d2_2 ^ 2 * d2_0 * e2 * e0 + d2_2 ^ 3 * e0 ^ 2) res_sub_v := by
      have t1 : ValLead (-31) _ _ := ((((hD21_L.neg.mul (hD20_L.pow 2)).mul hD33_D.toValLead).mul hD32_L).eq_k (by omega))
      have t2 : ValLead (-31) _ _ := (((hD22_D.toValLead.mul (hD20_L.pow 2)).mul (hD32_L.pow 2)).eq_k (by omega))
      have t3 : ValLead (-31) _ _ := ((((((ValLead.of_ofNat 2).mul hD22_D.toValLead).mul (hD20_L.pow 2)).mul hD33_D.toValLead).mul hD31_L).eq_k (by omega))
      have t4 : ValLead (-31) _ _ := (((((((ValLead.of_ofNat 3).mul hD22_D.toValLead).mul hD21_L).mul hD20_L).mul hD33_D.toValLead).mul hD30_L).eq_k (by omega))
      have t5 : ValLead (-31) _ _ := ((((((ValLead.of_ofNat 2).mul (hD22_D.toValLead.pow 2)).mul hD20_L).mul hD32_L).mul hD30_L).eq_k (by omega))
      have t6 : ValLead (-31) _ _ := (((hD22_D.toValLead.pow 3).mul (hD30_L.pow 2)).eq_k (by omega))
      exact (((((t1.add t2).sub t3).add t4).sub t5).add t6).eq_c rfl
    have hhi : HasValGe (-30)
        (d2_1 ^ 2 * d2_0 * e3 * e1 - d2_2 * d2_1 * d2_0 * e2 * e1 +
         d2_2 ^ 2 * d2_0 * e1 ^ 2 - d2_1 ^ 3 * e3 * e0 +
         d2_2 * d2_1 ^ 2 * e2 * e0 - d2_2 ^ 2 * d2_1 * e1 * e0) := by
      have r1 : HasValGe (-30) _ := (((((hD21_L.val.pow 2).mul hD20_L.val).mul hD33_D.val).mul hD31_L.val).mono (by omega))
      have r2 : HasValGe (-30) _ := (((((hD22_D.val.mul hD21_L.val).mul hD20_L.val).mul hD32_L.val).mul hD31_L.val).mono (by omega))
      have r3 : HasValGe (-30) _ := ((((hD22_D.val.pow 2).mul hD20_L.val).mul (hD31_L.val.pow 2)).mono (by omega))
      have r4 : HasValGe (-30) _ := ((((hD21_L.val.pow 3).mul hD33_D.val).mul hD30_L.val).mono (by omega))
      have r5 : HasValGe (-30) _ := (((((hD22_D.val.mul (hD21_L.val.pow 2)).mul hD32_L.val).mul hD30_L.val)).mono (by omega))
      have r6 : HasValGe (-30) _ := (((((hD22_D.val.pow 2).mul hD21_L.val).mul hD31_L.val).mul hD30_L.val).mono (by omega))
      exact ((((r1.sub r2).add r3).sub r4).add r5).sub r6
    exact ((hm.add_shift1 hs).add_high hhi).eq_d (by ext <;> simp only [w1_res_D, res_main, res_sub_v, Dual.add_val, Dual.add_eps, add_zero])
  -- Combine `pref`, `A4`, `A3`, `A2`, `A1`, `A0` using `W1_inf_weights_alg`!
  obtain ⟨hres_val_eq, hden_ne, hA4_eq, hA3_eq, hA2_eq⟩ :=
    W1_inf_weights_alg S_K Q_K T_K (d2_0.coeff (-5)) hS3Q hL hT59
  have h81Av_D : ValDual (-2) (81 * HahnSeries.C k5Params.Av0 * (2 * W1_inf + evalInvT k5Params.bW))
      (Dual.C (81 : K5) * ⟨Bv2, Bv1⟩) := by
    have heq : 81 * HahnSeries.C k5Params.Av0 * (2 * W1_inf + evalInvT k5Params.bW) =
        HahnSeries.C (81 : K5) * evalInvT k5Params.Bv + 162 * HahnSeries.C k5Params.Av0 * W1_inf := by
      have hAv : HahnSeries.C k5Params.Av0 * evalInvT k5Params.bW = evalInvT k5Params.Bv := by
        rw [CoverParams.bW, map_mul, evalInvT_C, ← mul_assoc, ← map_mul, k5Params_Av0_mul_inv, map_one, one_mul]
      rw [show HahnSeries.C (81 : K5) = (81 : LaurentSeries K5) by rw [map_ofNat]]
      linear_combination 81 * hAv
    rw [heq]
    have hBv_D : ValDual (-2) (evalInvT k5Params.Bv) ⟨Bv2, Bv1⟩ :=
      ((ValDual.of_evalInvT k5Params.Bv (natDegree_quadU_le _ _ _) (by omega)).eq_k (by omega)).eq_d (by
        ext <;> simp only [CoverParams.Bv, coeff_quadU, hBv2_eq, hBv1_eq])
    have hhi : HasValGe 0 (162 * HahnSeries.C k5Params.Av0 * W1_inf) :=
      (((HasValGe.of_ofNat 162).mul (HasValGe.of_C _)).mul HasValGe_W1_inf).mono (by omega)
    exact (((ValDual.of_C (81 : K5)).mul hBv_D).eq_k (by omega)).add_high hhi
  set num_pref_D : Dual K5 := w1_num_pref S_K Q_K T_K
  set den_pref_D : Dual K5 := w1_den_pref S_K Q_K T_K (d2_0.coeff (-5))
  have hnum_pref_D : ValDual (-11) (-(HahnSeries.single (-1 : ℤ) (1 : K5) ^ 3 * W1_inf * evalInvT k5Params.cb_h ^ 4)) num_pref_D := by
    have hU3 : ValDual (-3) (HahnSeries.single (-1 : ℤ) (1 : K5) ^ 3) (Dual.C 1) :=
      ((ValDual.of_single (-1) 1).pow 3).eq_k (by omega) |>.eq_d (by rw [← map_pow, one_pow])
    exact (((hU3.mul hW_D).mul (hcb_D.pow 4)).neg).eq_k (by omega) |>.eq_d (by dsimp only [num_pref_D, w1_num_pref]; rw [map_one, one_mul])
  have hden_pref_D : ValDual (-49)
      (81 * HahnSeries.C k5Params.Av0 * (2 * W1_inf + evalInvT k5Params.bW) * evalInvT k5Params.Q5_z ^ 3 * res) den_pref_D := by
    have hQ5_D : ValDual (-5) (evalInvT k5Params.Q5_z) D22 := by
      simpa only [d2_2, CoverParams.d2_2, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using hD22_D
    exact (((h81Av_D.mul (hQ5_D.pow 3)).mul hres_D)).eq_k (by omega)
  have hpref_D : ValDual 38 pref (num_pref_D * ⟨den_pref_D.val⁻¹, -den_pref_D.eps / den_pref_D.val ^ 2⟩) :=
    (hnum_pref_D.div_of_ne hden_pref_D hden_ne).eq_k (by omega)
  -- `A4`: `ValDual 3`!
  have hP0_4_D : ValDual (-17) (-d2_1 ^ 2 * d2_0 + d2_2 * d2_0 ^ 2)
      (w1_P0_4_D S_K Q_K T_K (d2_0.coeff (-5))) := by
    rw [add_comm]
    have hm : ValDual (-17) _ _ := (hD22_D.mul (hD20_D.pow 2)).eq_k (by omega)
    have hs : ValLead (-16) _ _ := (((hD21_L.pow 2).neg.mul hD20_L).eq_k (by omega))
    exact (hm.add_shift1 hs).eq_d (by ext <;> simp only [w1_P0_4_D, Dual.add_val, Dual.add_eps, add_zero] <;> ring)
  have hP1_4_L : ValLead (-16) (-d2_1 ^ 3 + 2 * d2_2 * d2_1 * d2_0) (w1_P1_4_v S_K Q_K T_K) := by
    rw [add_comm]
    have hm : ValLead (-16) (2 * d2_2 * d2_1 * d2_0) (w1_P1_4_v S_K Q_K T_K) :=
      ((((ValLead.of_ofNat 2).mul hD22_D.toValLead).mul hD21_L).mul hD20_L).eq_k (by omega)
    have hhi : HasValGe (-15) (-d2_1 ^ 3) := (hD21_L.val.pow 3).neg.mono (by omega)
    exact hm.add_high hhi
  have hC4_D : ValDual (-35) ((-d2_1 ^ 3 + 2 * d2_2 * d2_1 * d2_0) * d0 - (-d2_1 ^ 2 * d2_0 + d2_2 * d2_0 ^ 2) * d1)
      (w1_C4_D S_K Q_K T_K (d2_0.coeff (-5))) := by
    rw [sub_eq_add_neg, add_comm]
    have hm : ValDual (-35) _ _ := (hP0_4_D.mul hd1_D).neg.eq_k (by omega)
    have hs : ValLead (-34) _ _ := (hP1_4_L.mul hd0_L).eq_k (by omega)
    exact (hm.add_shift1 hs).eq_d (by ext <;> simp only [w1_C4_D, d0_v, Dual.add_val, Dual.add_eps, Dual.neg_val, Dual.neg_eps, add_zero])
  have hA4_D : ValDual 3 A4 ⟨w1_A4_3 S_K Q_K T_K, w1_A4_4 S_K Q_K T_K⟩ := by
    refine ((hpref_D.mul hC4_D).eq_k (by omega)).eq_d ?_
    rw [mul_right_comm]
    exact (dual_div_eq_iff _ den_pref_D _ hden_ne).mpr hA4_eq
  -- `A3`: `ValLead 4`!
  have hA3_L : ValLead 4 A3 (w1_A3_4 S_K Q_K T_K) := by
    have hP1_3 : ValLead (-16) (d2_2 * (d2_1 ^ 2 - d2_2 * d2_0)) (-D22.val ^ 2 * D20_v) := by
      have hsub : d2_2 * (d2_1 ^ 2 - d2_2 * d2_0) = -(d2_2 ^ 2 * d2_0) + d2_2 * d2_1 ^ 2 := by ring
      rw [hsub]
      have hm : ValLead (-16) (-(d2_2 ^ 2 * d2_0)) (-D22.val ^ 2 * D20_v) :=
        (((hD22_D.toValLead.pow 2).mul hD20_L).neg.eq_k (by omega)).eq_c (by ring)
      exact hm.add_high ((hD22_D.val.mul (hD21_L.val.pow 2)).mono (by omega))
    have hP0_3 : ValLead (-16) (d2_2 * d2_1 * d2_0) (D22.val * D21_v * D20_v) :=
      ((hD22_D.toValLead.mul hD21_L).mul hD20_L).eq_k (by omega)
    have hC3 : ValLead (-34) ((d2_2 * (d2_1 ^ 2 - d2_2 * d2_0)) * d0 - (d2_2 * d2_1 * d2_0) * d1)
        (w1_C3_v S_K Q_K T_K (d2_0.coeff (-5))) :=
      ((hP1_3.mul hd0_L).eq_k (by omega)).sub ((hP0_3.mul hd1_D.toValLead).eq_k (by omega))
    refine ((hpref_D.toValLead.mul hC3).eq_k (by omega)).eq_c ?_
    apply mul_left_cancel₀ hden_ne
    simp only [Dual.mul_val]
    have : den_pref_D.val * (num_pref_D.val * den_pref_D.val⁻¹ * w1_C3_v S_K Q_K T_K (d2_0.coeff (-5))) =
        num_pref_D.val * w1_C3_v S_K Q_K T_K (d2_0.coeff (-5)) := by
      field_simp [hden_ne]
    rw [this]; exact hA3_eq
  -- `A2`: `ValLead 4`!
  have hA2_L : ValLead 4 A2 (w1_A2_4 S_K Q_K T_K) := by
    have hC2 : ValLead (-34) ((-d2_2 ^ 2 * d2_1) * d0 - (-d2_2 ^ 2 * d2_0) * d1)
        (w1_C2_v S_K Q_K T_K (d2_0.coeff (-5))) := by
      have hre : (-d2_2 ^ 2 * d2_1) * d0 - (-d2_2 ^ 2 * d2_0) * d1 =
          (d2_2 ^ 2 * d2_0) * d1 + (-d2_2 ^ 2 * d2_1) * d0 := by ring
      rw [hre]
      exact ((((hD22_D.toValLead.pow 2).mul hD20_L).mul hd1_D.toValLead).eq_k (by omega)).add_high
        ((((hD22_D.val.pow 2).neg.mul hD21_L.val).mul hd0_L.val).mono (by omega))
    refine ((hpref_D.toValLead.mul hC2).eq_k (by omega)).eq_c ?_
    apply mul_left_cancel₀ hden_ne
    simp only [Dual.mul_val]
    have : den_pref_D.val * (num_pref_D.val * den_pref_D.val⁻¹ * w1_C2_v S_K Q_K T_K (d2_0.coeff (-5))) =
        num_pref_D.val * w1_C2_v S_K Q_K T_K (d2_0.coeff (-5)) := by field_simp [hden_ne]
    rw [this]; exact hA2_eq
  have hA1 : HasValGe 5 A1 :=
    (hpref_D.val.mul ((hD22_D.val.pow 3).mul hd0_L.val)).mono (by omega)
  have hA0 : HasValGe 5 A0 :=
    (hpref_D.val.mul ((hD22_D.val.pow 3).neg.mul hd1_D.val)).mono (by omega)
  have hres_ne : res.coeff (-32) ≠ 0 := by
    rw [hres_D.c0, hres_val_eq]
    have hc : -(64000000000000 / 6461081889226673298932241 : K5) ≠ 0 :=
      neg_ne_zero.mpr (div_ne_zero (ofNat_ne_zero 64000000000000) (ofNat_ne_zero 6461081889226673298932241))
    exact mul_ne_zero (mul_ne_zero hc (pow_ne_zero 6 hT59)) (pow_ne_zero 15 hS3Q)
  exact ⟨hA4_D, hA3_L, hA2_L, hA1, hA0, hres_D.val, hres_ne⟩

private lemma res_z_W2_inf_val_ne :
    HasValGe (-41) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.res_z)) ∧
    (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.res_z)).coeff (-41) ≠ 0 := by
  have h2_val : HasValGe (-41) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.res_z)) := by
    -- Extract directly from `HasValGe_evalInvT_nm_z` components or prove cleanly in 20 lines:
    have hw := HasValGe_W2_inf; have hw_eq := W2_inf_eq
    rw [CoverParams.res_z, map_syl5Pair, evalAt_syl5Pair _ _ _ _ _ _ _ _ _ W2_inf hw_eq]
    have hw_c : W2_inf.coeff (-2) = -(k5Params.Bv2 * k5Params.Av0_inv) := by
      rw [W2_inf, HahnSeries.coeff_sub, HahnSeries.coeff_neg, HasValGe_W1_inf (-2) (by omega), sub_zero,
        evalInvT_bW_eq]
      have hmul := (HasValGe.single (-2 : ℤ) (1 : K5)).coeff_mul_min (HasValGe.of_powerSeries bInfPS)
      simp only [add_zero] at hmul
      rw [hmul, HahnSeries.coeff_single_same, one_mul]
      change -(HahnSeries.coeff ((bInfPS : PowerSeries K5) : LaurentSeries K5) (0 : ℕ)) = _
      rw [LaurentSeries.coeff_coe_powerSeries, bInfPS_coeff0]
    have htoUW (v0 v1 v2 : K5) :
        ValLead (-4) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT (k5Params.toUW v0 v1 v2)))
          (v2 * (-(k5Params.Bv2 * k5Params.Av0_inv)) ^ 2) := by
      have heq : PairAlg.evalAt W2_inf (PairAlg.map evalInvT (k5Params.toUW v0 v1 v2)) =
          HahnSeries.C v2 * W2_inf ^ 2 +
          (HahnSeries.C v1 * HahnSeries.single (-1) 1 * W2_inf + HahnSeries.C v0 * HahnSeries.single (-2) 1) := by
        simp only [PairAlg.evalAt, PairAlg.map, CoverParams.toUW, map_sub, map_mul, map_pow,
          evalInvT_C, evalInvT_X, HahnSeries.single_pow]
        have h2p : (2 : ℕ) • (-1 : ℤ) = -2 := by decide
        simp only [one_pow, h2p]; linear_combination -HahnSeries.C v2 * hw_eq
      rw [heq]
      have ht1 : ValLead (-4) (HahnSeries.C v2 * W2_inf ^ 2) (v2 * (-(k5Params.Bv2 * k5Params.Av0_inv)) ^ 2) :=
        ((ValLead.of_C v2).mul ((⟨hw, hw_c⟩ : ValLead (-2) W2_inf _).pow 2)).eq_k (by omega)
      have ht2 : HasValGe (-3) (HahnSeries.C v1 * HahnSeries.single (-1) 1 * W2_inf + HahnSeries.C v0 * HahnSeries.single (-2) 1) :=
        ((((HasValGe.of_C v1).mul (HasValGe.single (-1) 1)).mul hw).mono (by omega)).add
          (((HasValGe.of_C v0).mul (HasValGe.single (-2) 1)).mono (by omega))
      exact ht1.add_high ht2
    have hc0W := htoUW k5Params.c0_V0 k5Params.c0_V1 k5Params.c0_V2
    have hk2W := htoUW k5Params.k2_V0 k5Params.k2_V1 k5Params.k2_V2
    have hk3W := htoUW k5Params.k3_V0 k5Params.k3_V1 k5Params.k3_V2
    have hq2 : HasValGe (-5) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d2_2)) := by
      simpa [CoverParams.d2_2, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using
        HasValGe.evalInvT_of_natDegree_le _ k5Params_Q5_z_natDegree_le
    have hq1 : HasValGe (-7) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d2_1)) := by
      rw [CoverParams.d2_1, PairAlg.map_smul, PairAlg.evalAt_smul]
      exact ((HasValGe.evalInvT_of_natDegree_le _ k5Params_p21_natDegree_le).mul hc0W.val).mono (by omega)
    have hcb : ValLead (-2) (evalInvT k5Params.cb_h) (k5Params.cb_h.coeff 2) :=
      (ValDual.of_evalInvT _ deg2_cb (by omega)).toValLead
    have hq02 : ValLead (-2) (evalInvT k5Params.q02) (k5Params.q02.coeff 2) :=
      (ValDual.of_evalInvT _ deg2_q02 (by omega)).toValLead
    have hc03 : ValLead (-2) (evalInvT k5Params.c03) (k5Params.c03.coeff 2) :=
      (ValDual.of_evalInvT _ deg2_c03 (by omega)).toValLead
    have hq0 : HasValGe (-9) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d2_0)) := by
      rw [CoverParams.d2_0, PairAlg.map_add, PairAlg.evalAt_add, PairAlg.map_smul, PairAlg.map_smul,
        PairAlg.evalAt_smul, PairAlg.evalAt_smul, CoverParams.pmul, CoverParams.pmul,
        PairAlg.map_mul, PairAlg.map_mul, PairAlg.evalAt_mul _ _ W2_inf hw_eq,
        PairAlg.evalAt_mul _ _ W2_inf hw_eq, PairAlg.map_W, PairAlg.evalAt_W, map_pow]
      have hL : ValLead (-10) _ _ := ((hq02.mul (hc0W.mul hc0W)).eq_k (by omega)).add
        (((hcb.pow 2).mul ((⟨hw, hw_c⟩ : ValLead (-2) W2_inf _).mul hk2W)).eq_k (by omega))
      refine (hL.eq_c ?_).hasValGe_succ
      simp only [CoverParams.q02, CoverParams.cb_h, CoverParams.c0_V2, CoverParams.k2_V2,
        CoverParams.Bv2, CoverParams.Av0_inv, coeff_quadU, CoverParams.inv4, CoverParams.inv9,
        CoverParams.inv27, CoverParams.inv81, CoverParams.inv243, k5Params_inv2, k5Params_inv3,
        k5Params_invT3, k5Params_S, k5Params_Q, k5Params_T]
      have hT := T_K_sub_3_ne; field_simp [hT]; ring
    have he3 : HasValGe (-7) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d3_3)) := by
      simpa [CoverParams.d3_3, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using
        HasValGe.evalInvT_of_natDegree_le _ k5Params_Q7_z_natDegree_le
    have he2 : HasValGe (-9) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d3_2)) := by
      rw [CoverParams.d3_2, PairAlg.map_smul, PairAlg.evalAt_smul]
      exact ((HasValGe.evalInvT_of_natDegree_le _ k5Params_p32_natDegree_le).mul hc0W.val).mono (by omega)
    have he1 : HasValGe (-11) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d3_1)) := by
      rw [CoverParams.d3_1, PairAlg.map_smul, PairAlg.evalAt_smul, CoverParams.pmul,
        PairAlg.map_mul, PairAlg.evalAt_mul _ _ W2_inf hw_eq]
      exact ((HasValGe.evalInvT_of_natDegree_le _ k5Params_p31_natDegree_le).mul (hc0W.val.mul hc0W.val)).mono (by omega)
    have he0 : HasValGe (-13) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.d3_0)) := by
      rw [CoverParams.d3_0, PairAlg.map_add, PairAlg.evalAt_add, PairAlg.map_smul, PairAlg.map_smul,
        PairAlg.evalAt_smul, PairAlg.evalAt_smul, CoverParams.pmul, CoverParams.pmul,
        CoverParams.pmul, CoverParams.pmul, PairAlg.map_mul, PairAlg.map_mul, PairAlg.map_mul,
        PairAlg.map_mul, PairAlg.evalAt_mul _ _ W2_inf hw_eq, PairAlg.evalAt_mul _ _ W2_inf hw_eq,
        PairAlg.evalAt_mul _ _ W2_inf hw_eq, PairAlg.evalAt_mul _ _ W2_inf hw_eq, PairAlg.map_W,
        PairAlg.evalAt_W, map_neg, map_pow]
      have hL : ValLead (-14) _ _ := ((hc03.neg.mul (hc0W.mul (hc0W.mul hc0W))).eq_k (by omega)).add
        (((hcb.pow 3).mul (((⟨hw, hw_c⟩ : ValLead (-2) W2_inf _).mul ⟨hw, hw_c⟩).mul hk3W)).eq_k (by omega))
      refine (hL.eq_c ?_).hasValGe_succ
      simp only [CoverParams.c03, CoverParams.cb_h, CoverParams.c0_V2, CoverParams.k3_V2,
        CoverParams.Bv2, CoverParams.Av0_inv, coeff_quadU, CoverParams.inv4, CoverParams.inv9,
        CoverParams.inv27, CoverParams.inv81, CoverParams.inv243, k5Params_inv2, k5Params_inv3,
        k5Params_invT3, k5Params_S, k5Params_Q, k5Params_T]
      have hT := T_K_sub_3_ne; field_simp [hT]; ring
    exact HasValGe.syl5 hq2 hq1 hq0 he3 he2 he1 he0
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨h2_val, ?_⟩
  have h1_val : HasValGe (-32) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.res_z)) :=
    W1_inf_weights.2.2.2.2.2.1
  have hnm : evalInvT k5Params.nm_z =
      PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.res_z) *
      PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.res_z) := by
    rw [CoverParams.nm_z, CoverParams.pnm, PairAlg.map_nm]
    exact PairAlg.evalAt_nm _ _ W1_inf W2_inf W1_W2_inf_sum W1_W2_inf_prod _
  have hc73 : k5Params.nm_z.coeff 73 = lc34_K5 := by
    rw [nm_z_K5_factor]
    have hcbm_monic : cb_h_m_K5.Monic := cb_h_m_loc_spec.1.map LocK5.subtype
    have hcbm_deg : cb_h_m_K5.natDegree = 2 := by
      rw [cb_h_m_K5, cb_h_m_loc_spec.1.natDegree_map, cb_h_m_loc_spec.2.1]
    have hM : (X ^ 15 * cb_h_m_K5 ^ 12 * P34_K5).Monic :=
      ((monic_X_pow 15).mul (hcbm_monic.pow 12)).mul P34_K5_monic
    have hdeg : (X ^ 15 * cb_h_m_K5 ^ 12 * P34_K5).natDegree = 73 := by
      have h1 : (X ^ 15 * cb_h_m_K5 ^ 12).Monic := (monic_X_pow 15).mul (hcbm_monic.pow 12)
      rw [h1.natDegree_mul' P34_K5_monic.ne_zero, P34_K5_natDegree,
        (monic_X_pow 15).natDegree_mul' (hcbm_monic.pow 12).ne_zero,
        Polynomial.natDegree_X_pow, hcbm_monic.natDegree_pow, hcbm_deg]
    rw [show C lc34_K5 * X ^ 15 * cb_h_m_K5 ^ 12 * P34_K5 =
        C lc34_K5 * (X ^ 15 * cb_h_m_K5 ^ 12 * P34_K5) by ring,
      Polynomial.coeff_C_mul, ← hdeg, hM.coeff_natDegree, mul_one]
  have hprod : (evalInvT k5Params.nm_z).coeff (-73) =
      (PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.res_z)).coeff (-32) *
      (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.res_z)).coeff (-41) := by
    rw [hnm, show (-73 : ℤ) = -32 + -41 by omega, h1_val.coeff_mul_min h2_val]
  rw [show (-73 : ℤ) = -((73 : ℕ) : ℤ) by omega, evalInvT_coeff_neg, hc73] at hprod
  intro h0; rw [h0, mul_zero] at hprod; exact lc34_K5_ne_zero hprod

/-! ### Section 4: Branch 2 (`W2_inf`) Vanishing `(br2_inf eta_AC).coeff 1 = 0` -/

private lemma numM_Uk_valLead (k : Fin 4) (mi : Fin 10)
    {a_s b_s ξS_s ξQ_s : LaurentSeries K5} {a0 b0 ξS0 ξQ0 : K5}
    (ha_L : ValLead 0 a_s a0) (hb_L : ValLead 0 b_s b0)
    (hξS_L : ValLead 0 ξS_s ξS0) (hξQ_L : ValLead 0 ξQ_s ξQ0) :
    ValLead 0 (numM_Uk k mi a_s b_s ξS_s ξQ_s) (numM_Uk k mi a0 b0 ξS0 ξQ0) := by
  have hC (r : K5) {f : LaurentSeries K5} {v : K5} (hf : ValLead 0 f v) :
      ValLead 0 (HahnSeries.C r * f) (r * v) := ((ValLead.of_C r).mul hf).eq_k (by omega)
  have hN (n : ℕ) [n.AtLeastTwo] {f : LaurentSeries K5} {v : K5} (hf : ValLead 0 f v) :
      ValLead 0 ((no_index (OfNat.ofNat n) : LaurentSeries K5) * f) ((no_index (OfNat.ofNat n) : K5) * v) :=
    ((ValLead.of_ofNat n).mul hf).eq_k (by omega)
  have h0_L : ValLead 0 (0 : LaurentSeries K5) (0 : K5) := by simpa only [map_zero] using ValLead.of_C (0 : K5)
  have h1_L : ValLead 0 (1 : LaurentSeries K5) (1 : K5) := by simpa only [map_one] using ValLead.of_C (1 : K5)
  have hS2 {s q : LaurentSeries K5} {s0 q0 : K5} (hs : ValLead 0 s s0) (hq : ValLead 0 q q0) :
      ValLead 0 (dHS_2 s q) (dHS_2 s0 q0) := by
    unfold dHS_2
    simpa only [map_div₀, map_neg, map_ofNat] using
      hC (-(4 / 81 : K5)) (((hs.sub (hN 3 hq)).pow 2).eq_k (by omega))
  have hS1 {s q : LaurentSeries K5} {s0 q0 : K5} (hs : ValLead 0 s s0) (hq : ValLead 0 q q0) :
      ValLead 0 (dHS_1 s q) (dHS_1 s0 q0) := by
    unfold dHS_1
    simpa only [map_div₀, map_neg, map_ofNat, mul_assoc] using
      ((hC (143 / 81 : K5) ((hs.pow 2).eq_k (by omega))).sub
        (hC (184 / 27 : K5) ((hs.mul hq).eq_k (by omega)))).add
        (hC (52 / 9 : K5) ((hq.pow 2).eq_k (by omega)))
  have hS0 {s q : LaurentSeries K5} {s0 q0 : K5} (hs : ValLead 0 s s0) (hq : ValLead 0 q q0) :
      ValLead 0 (dHS_0 s q) (dHS_0 s0 q0) := by
    unfold dHS_0
    simpa only [map_div₀, map_neg, map_ofNat, mul_assoc] using
      (hC (-(25 / 243 : K5)) ((hN 5 hs).sub (hN 9 hq))).mul ((hN 15 hs).sub (hN 9 hq)) |>.eq_k (by omega)
  have hQ1 {s q : LaurentSeries K5} {s0 q0 v0 : K5} (hs : ValLead 0 s s0) (hq : ValLead 0 q q0) :
      ValLead 0 (dHQ_1 s q (HahnSeries.C v0)) (dHQ_1 s0 q0 v0) := by
    unfold dHQ_1
    simpa only [map_div₀, map_neg, map_ofNat, mul_assoc] using
      ((((hC (-(92 / 27 : K5)) ((hs.pow 2).eq_k (by omega))).add
        (hC (104 / 9 : K5) ((hs.mul hq).eq_k (by omega)))).sub
        (hC (22 / 3 : K5) ((hq.pow 2).eq_k (by omega)))).add
        (hC (10 / 7 : K5) ((hq.mul (ValLead.of_C v0)).eq_k (by omega)))).add
        (hC (10 / 7 : K5) (((ValLead.of_C v0).pow 2).eq_k (by omega)))
  have hQ0 {s q : LaurentSeries K5} {s0 q0 : K5} (hs : ValLead 0 s s0) (hq : ValLead 0 q q0) :
      ValLead 0 (dHQ_0 s q) (dHQ_0 s0 q0) := by
    unfold dHQ_0
    simpa only [map_div₀, map_neg, map_ofNat, mul_assoc] using
      ((hC (50 / 27 : K5) hs).mul ((hN 5 hs).sub (hN 9 hq))).eq_k (by omega)
  have hm3 {s1 q1 s2 q2 : LaurentSeries K5} {s10 q10 v1 s20 q20 v2 : K5}
      (h1 : ValLead 0 s1 s10) (hq1 : ValLead 0 q1 q10) (h2 : ValLead 0 s2 s20) (hq2 : ValLead 0 q2 q20) :
      ValLead 0 (minor_U3 s1 q1 (HahnSeries.C v1) s2 q2 (HahnSeries.C v2)) (minor_U3 s10 q10 v1 s20 q20 v2) :=
    (((hS2 h1 hq1).mul ((hQ1 h2 hq2).add (hN 3 (hS1 h2 hq2)))).eq_k (by omega)).sub
      (((hS2 h2 hq2).mul ((hQ1 h1 hq1).add (hN 3 (hS1 h1 hq1)))).eq_k (by omega))
  have hm2 {s1 q1 s2 q2 : LaurentSeries K5} {s10 q10 v1 s20 q20 v2 : K5}
      (h1 : ValLead 0 s1 s10) (hq1 : ValLead 0 q1 q10) (h2 : ValLead 0 s2 s20) (hq2 : ValLead 0 q2 q20) :
      ValLead 0 (minor_U2 s1 q1 (HahnSeries.C v1) s2 q2 (HahnSeries.C v2)) (minor_U2 s10 q10 v1 s20 q20 v2) :=
    (((((hS2 h1 hq1).mul ((hQ0 h2 hq2).add (hN 3 (hS0 h2 hq2)))).eq_k (by omega)).sub
      (((hS2 h2 hq2).mul ((hQ0 h1 hq1).add (hN 3 (hS0 h1 hq1)))).eq_k (by omega))).add
      (((hS1 h1 hq1).mul (hQ1 h2 hq2)).eq_k (by omega))).sub
      (((hS1 h2 hq2).mul (hQ1 h1 hq1)).eq_k (by omega))
  have hm1 {s1 q1 s2 q2 : LaurentSeries K5} {s10 q10 v1 s20 q20 v2 : K5}
      (h1 : ValLead 0 s1 s10) (hq1 : ValLead 0 q1 q10) (h2 : ValLead 0 s2 s20) (hq2 : ValLead 0 q2 q20) :
      ValLead 0 (minor_U1 s1 q1 (HahnSeries.C v1) s2 q2 (HahnSeries.C v2)) (minor_U1 s10 q10 v1 s20 q20 v2) :=
    (((((hS1 h1 hq1).mul (hQ0 h2 hq2)).eq_k (by omega)).sub
      (((hS1 h2 hq2).mul (hQ0 h1 hq1)).eq_k (by omega))).add
      (((hS0 h1 hq1).mul (hQ1 h2 hq2)).eq_k (by omega))).sub
      (((hS0 h2 hq2).mul (hQ1 h1 hq1)).eq_k (by omega))
  have hm0 {s1 q1 s2 q2 : LaurentSeries K5} {s10 q10 s20 q20 : K5}
      (h1 : ValLead 0 s1 s10) (hq1 : ValLead 0 q1 q10) (h2 : ValLead 0 s2 s20) (hq2 : ValLead 0 q2 q20) :
      ValLead 0 (minor_U0 s1 q1 s2 q2) (minor_U0 s10 q10 s20 q20) :=
    (((hS0 h1 hq1).mul (hQ0 h2 hq2)).eq_k (by omega)).sub (((hS0 h2 hq2).mul (hQ0 h1 hq1)).eq_k (by omega))
  have htriples {d10s d20s d21s : LaurentSeries K5} {d100 d200 d210 : K5}
      (hd10 : ValLead 0 d10s d100) (hd20 : ValLead 0 d20s d200) (hd21 : ValLead 0 d21s d210) :
      ValLead 0
        (let (m2, m1, m0) : LaurentSeries K5 × LaurentSeries K5 × LaurentSeries K5 := match mi with
          | 0 => (a_s ^ 2, 2 * a_s * ξS_s, ξS_s ^ 2)
          | 1 => (a_s * b_s, a_s * ξQ_s + b_s * ξS_s, ξS_s * ξQ_s)
          | 2 => (b_s ^ 2, 2 * b_s * ξQ_s, ξQ_s ^ 2)
          | 3 => (a_s, ξS_s, 0) | 4 => (0, a_s, ξS_s)
          | 5 => (b_s, ξQ_s, 0) | 6 => (0, b_s, ξQ_s)
          | 7 => (1, 0, 0) | 8 => (0, 1, 0) | 9 => (0, 0, 1)
         (1 / 16 : LaurentSeries K5) * (m2 * d10s - m1 * d20s + m0 * d21s))
        (let (m2, m1, m0) : K5 × K5 × K5 := match mi with
          | 0 => (a0 ^ 2, 2 * a0 * ξS0, ξS0 ^ 2)
          | 1 => (a0 * b0, a0 * ξQ0 + b0 * ξS0, ξS0 * ξQ0)
          | 2 => (b0 ^ 2, 2 * b0 * ξQ0, ξQ0 ^ 2)
          | 3 => (a0, ξS0, 0) | 4 => (0, a0, ξS0)
          | 5 => (b0, ξQ0, 0) | 6 => (0, b0, ξQ0)
          | 7 => (1, 0, 0) | 8 => (0, 1, 0) | 9 => (0, 0, 1)
         (1 / 16 : K5) * (m2 * d100 - m1 * d200 + m0 * d210)) := by
    have hcomb {m2 m1 m0 : LaurentSeries K5} {m20 m10 m00 : K5}
        (h2 : ValLead 0 m2 m20) (h1 : ValLead 0 m1 m10) (h0 : ValLead 0 m0 m00) :
        ValLead 0 ((1 / 16 : LaurentSeries K5) * (m2 * d10s - m1 * d20s + m0 * d21s))
          ((1 / 16 : K5) * (m20 * d100 - m10 * d200 + m00 * d210)) := by
      simpa only [map_div₀, map_ofNat, map_one] using
        hC (1 / 16 : K5) ((((h2.mul hd10).eq_k (by omega)).sub ((h1.mul hd20).eq_k (by omega))).add ((h0.mul hd21).eq_k (by omega)))
    fin_cases mi
    · exact hcomb ((ha_L.pow 2).eq_k (by omega)) (((hN 2 ha_L).mul hξS_L).eq_k (by omega)) ((hξS_L.pow 2).eq_k (by omega))
    · exact hcomb ((ha_L.mul hb_L).eq_k (by omega))
        (((ha_L.mul hξQ_L).eq_k (by omega)).add ((hb_L.mul hξS_L).eq_k (by omega))) ((hξS_L.mul hξQ_L).eq_k (by omega))
    · exact hcomb ((hb_L.pow 2).eq_k (by omega)) (((hN 2 hb_L).mul hξQ_L).eq_k (by omega)) ((hξQ_L.pow 2).eq_k (by omega))
    · exact hcomb ha_L hξS_L h0_L
    · exact hcomb h0_L ha_L hξS_L
    · exact hcomb hb_L hξQ_L h0_L
    · exact hcomb h0_L hb_L hξQ_L
    · exact hcomb h1_L h0_L h0_L
    · exact hcomb h0_L h1_L h0_L
    · exact hcomb h0_L h0_L h1_L
  fin_cases k
  · exact htriples
      (((hm0 (ha_L.add hξS_L) (hb_L.add hξQ_L) hξS_L hξQ_L).sub (hm0 ha_L hb_L hξS_L hξQ_L)).sub (hm0 hξS_L hξQ_L hξS_L hξQ_L))
      (hm0 ha_L hb_L hξS_L hξQ_L)
      ((hm0 ha_L hb_L (ha_L.add hξS_L) (hb_L.add hξQ_L)).sub (hm0 ha_L hb_L hξS_L hξQ_L))
  · exact htriples
      (by simpa only [d10_U1, map_div₀, map_ofNat, map_zero, map_one, mul_assoc] using
            (((hm1 (v1 := 0) (v2 := 1) (ha_L.add hξS_L) (hb_L.add hξQ_L) hξS_L hξQ_L).sub
              (hm1 (v1 := 0) (v2 := 1) ha_L hb_L hξS_L hξQ_L)).sub (hm1 (v1 := 0) (v2 := 1) hξS_L hξQ_L hξS_L hξQ_L)).sub
              (hC (10 / 7 : K5) ((hb_L.mul (hS0 hξS_L hξQ_L)).eq_k (by omega))))
      (by simpa only [d20_U1, map_zero, map_one] using hm1 (v1 := 0) (v2 := 1) ha_L hb_L hξS_L hξQ_L)
      (by simpa only [d21_U1, map_div₀, map_ofNat, map_zero, mul_assoc] using
            ((hm1 (v1 := 0) (v2 := 0) ha_L hb_L (ha_L.add hξS_L) (hb_L.add hξQ_L)).sub
              (hm1 (v1 := 0) (v2 := 0) ha_L hb_L hξS_L hξQ_L)).add
              (hC (10 / 7 : K5) ((hb_L.mul (hS0 ha_L hb_L)).eq_k (by omega))))
  · exact htriples
      (by simpa only [d10_U2, map_div₀, map_ofNat, map_zero, map_one, mul_assoc] using
            (((hm2 (v1 := 0) (v2 := 1) (ha_L.add hξS_L) (hb_L.add hξQ_L) hξS_L hξQ_L).sub
              (hm2 (v1 := 0) (v2 := 1) ha_L hb_L hξS_L hξQ_L)).sub (hm2 (v1 := 0) (v2 := 1) hξS_L hξQ_L hξS_L hξQ_L)).sub
              (hC (10 / 7 : K5) ((hb_L.mul (hS1 hξS_L hξQ_L)).eq_k (by omega))))
      (by simpa only [d20_U2, map_zero, map_one] using hm2 (v1 := 0) (v2 := 1) ha_L hb_L hξS_L hξQ_L)
      (by simpa only [d21_U2, map_div₀, map_ofNat, map_zero, mul_assoc] using
            ((hm2 (v1 := 0) (v2 := 0) ha_L hb_L (ha_L.add hξS_L) (hb_L.add hξQ_L)).sub
              (hm2 (v1 := 0) (v2 := 0) ha_L hb_L hξS_L hξQ_L)).add
              (hC (10 / 7 : K5) ((hb_L.mul (hS1 ha_L hb_L)).eq_k (by omega))))
  · exact htriples
      (by simpa only [d10_U3, map_div₀, map_ofNat, map_zero, map_one, mul_assoc] using
            (((hm3 (v1 := 0) (v2 := 1) (ha_L.add hξS_L) (hb_L.add hξQ_L) hξS_L hξQ_L).sub
              (hm3 (v1 := 0) (v2 := 1) ha_L hb_L hξS_L hξQ_L)).sub (hm3 (v1 := 0) (v2 := 1) hξS_L hξQ_L hξS_L hξQ_L)).sub
              (hC (10 / 7 : K5) ((hb_L.mul (hS2 hξS_L hξQ_L)).eq_k (by omega))))
      (by simpa only [d20_U3, map_zero, map_one] using hm3 (v1 := 0) (v2 := 1) ha_L hb_L hξS_L hξQ_L)
      (by simpa only [d21_U3, map_div₀, map_ofNat, map_zero, mul_assoc] using
            ((hm3 (v1 := 0) (v2 := 0) ha_L hb_L (ha_L.add hξS_L) (hb_L.add hξQ_L)).sub
              (hm3 (v1 := 0) (v2 := 0) ha_L hb_L hξS_L hξQ_L)).add
              (hC (10 / 7 : K5) ((hb_L.mul (hS2 ha_L hb_L)).eq_k (by omega))))

private lemma numM_Uk_hasValGe (k : Fin 4) (mi : Fin 10)
    {a_s b_s ξS_s ξQ_s : LaurentSeries K5}
    (ha : HasValGe 0 a_s) (hb : HasValGe 0 b_s)
    (hξS : HasValGe 0 ξS_s) (hξQ : HasValGe 0 ξQ_s) :
    HasValGe 0 (numM_Uk k mi a_s b_s ξS_s ξQ_s) :=
  (numM_Uk_valLead k mi ⟨ha, rfl⟩ ⟨hb, rfl⟩ ⟨hξS, rfl⟩ ⟨hξQ, rfl⟩).val


private theorem localInf_weights_and_jets_proof : LocalInfWeightsSpec :=
  ⟨W1_inf_valDual, W1_inf_weights, res_z_W2_inf_val_ne,
   numM_Uk_valLead, numM_Uk_hasValGe⟩

end SymmetricSexticResidual.LocalResidueInf

theorem solution : SymmetricSexticResidual.LocalResidueInf.LocalInfWeightsSpec :=
  SymmetricSexticResidual.LocalResidueInf.localInf_weights_and_jets_proof
