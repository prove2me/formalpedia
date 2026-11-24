-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.cover_X15_W1_val
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T08:31:05.267597+00:00
-- url     : https://prove2.me/submissions/83dc79f5-8465-4f3d-8460-6cf1c8164c51

import Definitions.Def_HodgeComputerFormal_LaurentJets
import Definitions.Def_HodgeComputerSSR_K5Field
import Definitions.Def_HodgeComputerSSR_CoverParams
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

namespace SymmetricSexticResidual.CoverAlgebra
open SymmetricSexticResidual.K5Field QuadraticCovers Polynomial
open scoped BigOperators LaurentSeries PowerSeries

noncomputable section CoverX15W1
private lemma evalT_toUW_eq (v0 v1 v2 : K5) (w : LaurentSeries K5)
    (hw_eq : w ^ 2 + evalT k5Params.bW * w + evalT k5Params.cW = 0) :
    PairAlg.evalAt w (PairAlg.map evalT (k5Params.toUW v0 v1 v2)) =
      HahnSeries.C v2 * w ^ 2 + HahnSeries.C v1 * HahnSeries.single 1 1 * w +
      HahnSeries.C v0 * HahnSeries.single 2 1 := by
  simp only [PairAlg.evalAt, PairAlg.map, CoverParams.toUW, map_sub, map_mul, map_pow,
    evalT_C, evalT_X, HahnSeries.single_pow]
  have h2p : (2 : ℕ) • (1 : ℤ) = 2 := by decide
  simp only [one_pow, h2p]
  linear_combination -HahnSeries.C v2 * hw_eq


lemma res_z_W1_0_hasValGe_13 :
    HasValGe 13 (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.res_z)) := by
  have hQ5 : HasValGe 0 (evalT k5Params.Q5_z) := HasValGe.evalT _
  have hQ7 : HasValGe 0 (evalT k5Params.Q7_z) := HasValGe.evalT _
  have hq02 : HasValGe 0 (evalT k5Params.q02) := HasValGe.evalT _
  have hc03_0 : k5Params.c03.coeff 0 = 0 := by
    simp [CoverParams.c03, CoverParams.quadU]
  have hc03 : HasValGe 1 (evalT k5Params.c03) :=
    (HasValGe.evalT _).inc (by rw [show (0 : ℤ) = (0 : ℕ) by rfl, evalT_coeff, hc03_0])
  have hcb : HasValGe 0 (evalT k5Params.cb_h) := HasValGe.evalT _
  have hd2_1_sc : HasValGe 0 (evalT (-k5Params.q11 * k5Params.cb_h + 2 * k5Params.q02 * k5Params.ca_h)) :=
    HasValGe.evalT _
  have hd3_2_sc : HasValGe 0 (evalT (-k5Params.c21 * k5Params.cb_h ^ 2 +
      2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h - 3 * k5Params.c03 * k5Params.ca_h ^ 2)) :=
    HasValGe.evalT _
  have hd3_1_sc : HasValGe 0 (evalT (k5Params.c12 * k5Params.cb_h - 3 * k5Params.c03 * k5Params.ca_h)) :=
    HasValGe.evalT _
  have hcoeff0_evalT (p : K5[X]) : (evalT p).coeff 0 = p.coeff 0 := by
    change (evalT p).coeff (0 : ℕ) = p.coeff 0; exact evalT_coeff p 0
  -- Single-monomial factorizations of all `U = 0` scalar coefficients (so every `ring` below is instant!)
  have hcb0 : k5Params.cb_h.coeff 0 = (50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K) := by
    simp only [Polynomial.coeff_zero_eq_eval_zero, CoverParams.cb_h, CoverParams.quadU,
      CoverParams.inv27, CoverParams.inv9, k5Params_inv3, k5Params_S, k5Params_Q,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]; ring
  have hq02_0 : k5Params.q02.coeff 0 = -(25 / 3 : K5) * S_K := by
    simp only [Polynomial.coeff_zero_eq_eval_zero, CoverParams.q02, CoverParams.quadU,
      k5Params_inv3, k5Params_S, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]; ring
  have hQ5_0 : k5Params.Q5_z.coeff 0 = (15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4 := by
    simp only [Polynomial.coeff_zero_eq_eval_zero, CoverParams.Q5_z, CoverParams.q20, CoverParams.q11,
      CoverParams.q02, CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3, k5Params_S, k5Params_Q,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]; ring
  have hq1_s : (-k5Params.q11 * k5Params.cb_h + 2 * k5Params.q02 * k5Params.ca_h).coeff 0 =
      -(1250 / 729 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 2 := by
    simp only [Polynomial.coeff_zero_eq_eval_zero, CoverParams.q11, CoverParams.q02,
      CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3, k5Params_S, k5Params_Q,
      Polynomial.eval_add, Polynomial.eval_neg, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]; ring
  have hQ7_0 : k5Params.Q7_z.coeff 0 = -(781250 / 4782969 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 5 := by
    simp only [Polynomial.coeff_zero_eq_eval_zero, CoverParams.Q7_z, CoverParams.c30, CoverParams.c21,
      CoverParams.c12, CoverParams.c03, CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, CoverParams.inv243,
      k5Params_inv3, k5Params_S, k5Params_Q,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]; ring
  have he2_s : (-k5Params.c21 * k5Params.cb_h ^ 2 + 2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h -
      3 * k5Params.c03 * k5Params.ca_h ^ 2).coeff 0 =
      (62500 / 19683 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 3 := by
    simp only [Polynomial.coeff_zero_eq_eval_zero, CoverParams.c21, CoverParams.c12, CoverParams.c03,
      CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3, k5Params_S, k5Params_Q,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]; ring
  have he1_s : (k5Params.c12 * k5Params.cb_h - 3 * k5Params.c03 * k5Params.ca_h).coeff 0 =
      -(1250 / 81 : K5) * S_K * (5 * S_K - 9 * Q_K) := by
    simp only [Polynomial.coeff_zero_eq_eval_zero, CoverParams.c12, CoverParams.c03,
      CoverParams.ca_h, CoverParams.cb_h, CoverParams.quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3, k5Params_S, k5Params_Q,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]; ring

  have h1 : HasValGe 13 (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.res_z)) := by
    have hw := HasValGe_W1_0
    have hw_eq := W1_0_eq
    rw [CoverParams.res_z, map_syl5Pair, evalAt_syl5Pair _ _ _ _ _ _ _ _ _ W1_0 hw_eq]
    have htoUW_1 (v0 v1 v2 : K5) :
        HasValGe 2 (PairAlg.evalAt W1_0 (PairAlg.map evalT (k5Params.toUW v0 v1 v2))) ∧
        (PairAlg.evalAt W1_0 (PairAlg.map evalT (k5Params.toUW v0 v1 v2))).coeff 2 = v0 := by
      rw [evalT_toUW_eq v0 v1 v2 W1_0 hw_eq]
      have ht1 : HasValGe 3 (HahnSeries.C v2 * W1_0 ^ 2 + HahnSeries.C v1 * HahnSeries.single 1 1 * W1_0) :=
        (((HasValGe.of_C v2).mul (hw.pow 2)).mono (by omega)).add
          ((((HasValGe.of_C v1).mul (HasValGe.single 1 1)).mul hw).mono (by omega))
      have ht0 : HasValGe 2 (HahnSeries.C v0 * HahnSeries.single 2 1) :=
        ((HasValGe.of_C v0).mul (HasValGe.single 2 1)).mono (by omega)
      refine ⟨(ht1.mono (by omega)).add ht0, ?_⟩
      rw [add_comm, HasValGe.coeff_of_add ht1]
      have hm := (HasValGe.of_C v0).coeff_mul_min (HasValGe.single (2 : ℤ) (1 : K5))
      simp only [zero_add] at hm
      rw [hm, HahnSeries.C_apply, HahnSeries.coeff_single_same, HahnSeries.coeff_single_same, mul_one]
    obtain ⟨hc0W, hc0W_c⟩ : HasValGe 2 (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.c0W)) ∧
        (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.c0W)).coeff 2 = k5Params.c0_V0 :=
      htoUW_1 k5Params.c0_V0 k5Params.c0_V1 k5Params.c0_V2
    obtain ⟨hk2W, hk2W_c⟩ : HasValGe 2 (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.k2W)) ∧
        (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.k2W)).coeff 2 = k5Params.k2_V0 :=
      htoUW_1 k5Params.k2_V0 k5Params.k2_V1 k5Params.k2_V2
    obtain ⟨hk3W, hk3W_c⟩ : HasValGe 2 (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.k3W)) ∧
        (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.k3W)).coeff 2 = k5Params.k3_V0 :=
      htoUW_1 k5Params.k3_V0 k5Params.k3_V1 k5Params.k3_V2
    set q2 := PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d2_2)
    set q1 := PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d2_1)
    set q0 := PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d2_0)
    set e3 := PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_3)
    set e2 := PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_2)
    set e1 := PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_1)
    set e0 := PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.d3_0)
    have hq2 : HasValGe 0 q2 := by simpa [q2, CoverParams.d2_2, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using hQ5
    have hq1 : HasValGe 2 q1 := by
      simp only [q1, CoverParams.d2_1, PairAlg.map_smul, PairAlg.evalAt_smul]
      exact (hd2_1_sc.mul hc0W).mono (by omega)
    have hq0 : HasValGe 4 q0 := by
      simp only [q0, CoverParams.d2_0, PairAlg.map_add, PairAlg.evalAt_add, PairAlg.map_smul, PairAlg.evalAt_smul,
        CoverParams.pmul, PairAlg.map_mul, PairAlg.evalAt_mul _ _ W1_0 hw_eq, PairAlg.map_W, PairAlg.evalAt_W, map_pow]
      exact ((hq02.mul (hc0W.mul hc0W)).mono (by omega)).add (((hcb.pow 2).mul (hw.mul hk2W)).mono (by omega))
    have he3 : HasValGe 0 e3 := by simpa [e3, CoverParams.d3_3, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using hQ7
    have he2 : HasValGe 2 e2 := by
      simp only [e2, CoverParams.d3_2, PairAlg.map_smul, PairAlg.evalAt_smul]
      exact (hd3_2_sc.mul hc0W).mono (by omega)
    have he1 : HasValGe 4 e1 := by
      simp only [e1, CoverParams.d3_1, PairAlg.map_smul, PairAlg.evalAt_smul, CoverParams.pmul,
        PairAlg.map_mul, PairAlg.evalAt_mul _ _ W1_0 hw_eq]
      exact (hd3_1_sc.mul (hc0W.mul hc0W)).mono (by omega)
    have he0 : HasValGe 6 e0 := by
      simp only [e0, CoverParams.d3_0, PairAlg.map_add, PairAlg.evalAt_add, PairAlg.map_smul, PairAlg.evalAt_smul,
        CoverParams.pmul, PairAlg.map_mul, PairAlg.evalAt_mul _ _ W1_0 hw_eq, PairAlg.map_W, PairAlg.evalAt_W,
        map_neg, map_pow]
      exact ((hc03.neg.mul (hc0W.mul (hc0W.mul hc0W))).mono (by omega)).add
        (((hcb.pow 3).mul ((hw.mul hw).mul hk3W)).mono (by omega))
    -- Shift `z = z' + β` where `β = single 2 (-(Cv0 / Bv0) * S_K / T_K)`!
    let z1 : K5 := -(k5Params.Cv0 / k5Params.Bv0) * S_K / T_K
    let β : LaurentSeries K5 := HahnSeries.single 2 z1
    have hβ : HasValGe 2 β := HasValGe.single 2 z1
    have hshift := syl5_affine q2 q1 q0 e3 e2 e1 e0 1 β
    simp only [one_pow, mul_one, one_mul] at hshift
    rw [← hshift]
    have hq1' : HasValGe 2 (2 * q2 * β + q1) :=
      ((((HasValGe.of_nat 2).mul hq2).mul hβ).mono (by omega)).add hq1
    have he2' : HasValGe 2 (3 * e3 * β + e2) :=
      ((((HasValGe.of_nat 3).mul he3).mul hβ).mono (by omega)).add he2
    have he1' : HasValGe 4 (3 * e3 * β ^ 2 + 2 * e2 * β + e1) :=
      (((((HasValGe.of_nat 3).mul he3).mul (hβ.pow 2)).mono (by omega)).add
        ((((HasValGe.of_nat 2).mul he2).mul hβ).mono (by omega))).add he1
    have hq2_c : q2.coeff 0 = k5Params.Q5_z.coeff 0 := by
      simp only [q2, CoverParams.d2_2, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar, hcoeff0_evalT]
    have hq1_c : q1.coeff 2 = (-k5Params.q11 * k5Params.cb_h + 2 * k5Params.q02 * k5Params.ca_h).coeff 0 * k5Params.c0_V0 := by
      simp only [q1, CoverParams.d2_1, PairAlg.map_smul, PairAlg.evalAt_smul]
      rw [show (2 : ℤ) = 0 + 2 by norm_num, hd2_1_sc.coeff_mul_min hc0W, hcoeff0_evalT, hc0W_c]
    have hq0_c : q0.coeff 4 = k5Params.q02.coeff 0 * k5Params.c0_V0 ^ 2 +
        k5Params.cb_h.coeff 0 ^ 2 * (-(k5Params.Cv0 / k5Params.Bv0)) * k5Params.k2_V0 := by
      simp only [q0, CoverParams.d2_0, PairAlg.map_add, PairAlg.evalAt_add, PairAlg.map_smul, PairAlg.evalAt_smul,
        CoverParams.pmul, PairAlg.map_mul, PairAlg.evalAt_mul _ _ W1_0 hw_eq, PairAlg.map_W, PairAlg.evalAt_W,
        map_pow, HahnSeries.coeff_add]
      have ha := hq02.coeff_mul_min (hc0W.mul hc0W)
      have hb := (hcb.pow 2).coeff_mul_min (hw.mul hk2W)
      rw [show (4 : ℤ) = 0 + (2 + 2) by norm_num, ha, hc0W.coeff_mul_min hc0W]
      rw [show (0 + (2 + 2) : ℤ) = (2 : ℕ) * (0 : ℤ) + (2 + 2) by norm_num, hb, hcb.coeff_pow_min 2,
        hw.coeff_mul_min hk2W, W1_0_coeff2, hcoeff0_evalT, hcoeff0_evalT, hc0W_c, hk2W_c]; ring
    have he3_c : e3.coeff 0 = k5Params.Q7_z.coeff 0 := by
      simp only [e3, CoverParams.d3_3, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar, hcoeff0_evalT]
    have he2_c : e2.coeff 2 = (-k5Params.c21 * k5Params.cb_h ^ 2 +
        2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h - 3 * k5Params.c03 * k5Params.ca_h ^ 2).coeff 0 * k5Params.c0_V0 := by
      simp only [e2, CoverParams.d3_2, PairAlg.map_smul, PairAlg.evalAt_smul]
      rw [show (2 : ℤ) = 0 + 2 by norm_num, hd3_2_sc.coeff_mul_min hc0W, hcoeff0_evalT, hc0W_c]
    have he1_c : e1.coeff 4 = (k5Params.c12 * k5Params.cb_h - 3 * k5Params.c03 * k5Params.ca_h).coeff 0 * k5Params.c0_V0 ^ 2 := by
      simp only [e1, CoverParams.d3_1, PairAlg.map_smul, PairAlg.evalAt_smul, CoverParams.pmul,
        PairAlg.map_mul, PairAlg.evalAt_mul _ _ W1_0 hw_eq]
      rw [show (4 : ℤ) = 0 + (2 + 2) by norm_num, hd3_1_sc.coeff_mul_min (hc0W.mul hc0W),
        hc0W.coeff_mul_min hc0W, hcoeff0_evalT, hc0W_c]; ring
    have he0_c : e0.coeff 6 = k5Params.cb_h.coeff 0 ^ 3 * (-(k5Params.Cv0 / k5Params.Bv0)) ^ 2 * k5Params.k3_V0 := by
      simp only [e0, CoverParams.d3_0, PairAlg.map_add, PairAlg.evalAt_add, PairAlg.map_smul, PairAlg.evalAt_smul,
        CoverParams.pmul, PairAlg.map_mul, PairAlg.evalAt_mul _ _ W1_0 hw_eq, PairAlg.map_W, PairAlg.evalAt_W,
        map_neg, map_pow]
      have ht7 : HasValGe 7 (-evalT k5Params.c03 * (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.c0W) *
          (PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.c0W) *
           PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.c0W)))) :=
        (hc03.neg.mul (hc0W.mul (hc0W.mul hc0W))).mono (by omega)
      rw [add_comm, HasValGe.coeff_of_add ht7]
      have hb := (hcb.pow 3).coeff_mul_min ((hw.mul hw).mul hk3W)
      rw [show (6 : ℤ) = (3 : ℕ) * (0 : ℤ) + (2 + 2 + 2) by norm_num, hb, hcb.coeff_pow_min 3,
        (hw.mul hw).coeff_mul_min hk3W, hw.coeff_mul_min hw, W1_0_coeff2, hcoeff0_evalT, hk3W_c]; ring
    have hCvBv_mul : S_K * (5 * S_K - 9 * Q_K) ^ 2 * (k5Params.Cv0 / k5Params.Bv0) =
        T_K * (5 * T_K - 9) ^ 2 := by
      have hBv_ne : k5Params.Bv0 ≠ 0 := by
        simp only [CoverParams.Bv0, CoverParams.inv243, k5Params_inv3, k5Params_S, k5Params_Q]
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 5 (by norm_num)))
          S_K_ne_zero) (pow_ne_zero 2 fiveS_sub_9Q_ne)
      rw [mul_div_assoc', div_eq_iff hBv_ne]
      simp only [CoverParams.Cv0, CoverParams.Bv0, CoverParams.inv243, k5Params_inv3,
        k5Params_S, k5Params_Q, k5Params_T]
      ring
    have hz1_mul : (5 * S_K - 9 * Q_K) ^ 2 * z1 = -(5 * T_K - 9) ^ 2 := by
      apply mul_left_cancel₀ T_K_ne_zero
      have h1 : T_K * ((5 * S_K - 9 * Q_K) ^ 2 * z1) =
          -(S_K * (5 * S_K - 9 * Q_K) ^ 2 * (k5Params.Cv0 / k5Params.Bv0)) := by
        simp only [z1]
        have hT := T_K_ne_zero
        field_simp [hT]
      rw [h1, hCvBv_mul]; ring
    have hq0' : HasValGe 5 (q2 * β ^ 2 + q1 * β + q0) := by
      have h4 : HasValGe 4 (q2 * β ^ 2 + q1 * β + q0) :=
        (((hq2.mul (hβ.pow 2)).mono (by omega)).add ((hq1.mul hβ).mono (by omega))).add hq0
      apply h4.inc
      rw [HahnSeries.coeff_add, HahnSeries.coeff_add]
      have ha := hq2.coeff_mul_min (hβ.pow 2)
      have hb := hq1.coeff_mul_min hβ
      rw [show (4 : ℤ) = 0 + (2 : ℕ) * (2 : ℤ) by norm_num, ha, hβ.coeff_pow_min 2]
      rw [show (0 + (2 : ℕ) * (2 : ℤ) : ℤ) = 2 + 2 by norm_num, hb]
      rw [show (2 + 2 : ℤ) = 4 by norm_num, hq2_c, hq1_c, hq0_c]
      simp only [β, HahnSeries.coeff_single_same]
      apply mul_left_cancel₀ (mul_ne_zero S_K_ne_zero (pow_ne_zero 4 fiveS_sub_9Q_ne))
      rw [mul_zero]
      have hstep :
          S_K * (5 * S_K - 9 * Q_K) ^ 4 *
            (k5Params.Q5_z.coeff 0 * z1 ^ 2 +
              (-k5Params.q11 * k5Params.cb_h + 2 * k5Params.q02 * k5Params.ca_h).coeff 0 * k5Params.c0_V0 * z1 +
              (k5Params.q02.coeff 0 * k5Params.c0_V0 ^ 2 +
                k5Params.cb_h.coeff 0 ^ 2 * -(k5Params.Cv0 / k5Params.Bv0) * k5Params.k2_V0)) =
          k5Params.Q5_z.coeff 0 * S_K * ((5 * S_K - 9 * Q_K) ^ 2 * z1) ^ 2 +
          (-k5Params.q11 * k5Params.cb_h + 2 * k5Params.q02 * k5Params.ca_h).coeff 0 * k5Params.c0_V0 *
            S_K * (5 * S_K - 9 * Q_K) ^ 2 * ((5 * S_K - 9 * Q_K) ^ 2 * z1) +
          k5Params.q02.coeff 0 * k5Params.c0_V0 ^ 2 * S_K * (5 * S_K - 9 * Q_K) ^ 4 -
          k5Params.cb_h.coeff 0 ^ 2 * k5Params.k2_V0 * (5 * S_K - 9 * Q_K) ^ 2 *
            (S_K * (5 * S_K - 9 * Q_K) ^ 2 * (k5Params.Cv0 / k5Params.Bv0)) := by ring
      rw [hstep, hz1_mul, hCvBv_mul, hQ5_0, hq1_s, hq02_0, hcb0]
      simp only [CoverParams.c0_V0, CoverParams.k2_V0, CoverParams.inv81, k5Params_inv3, k5Params_T]
      generalize 5 * S_K - 9 * Q_K = A
      ring
    have he0' : HasValGe 7 (e3 * β ^ 3 + e2 * β ^ 2 + e1 * β + e0) := by
      have h6 : HasValGe 6 (e3 * β ^ 3 + e2 * β ^ 2 + e1 * β + e0) :=
        ((((he3.mul (hβ.pow 3)).mono (by omega)).add ((he2.mul (hβ.pow 2)).mono (by omega))).add
          ((he1.mul hβ).mono (by omega))).add he0
      apply h6.inc
      rw [HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_add]
      have ha := he3.coeff_mul_min (hβ.pow 3)
      have hb := he2.coeff_mul_min (hβ.pow 2)
      have hc := he1.coeff_mul_min hβ
      rw [show (6 : ℤ) = 0 + (3 : ℕ) * (2 : ℤ) by norm_num, ha, hβ.coeff_pow_min 3]
      rw [show (0 + (3 : ℕ) * (2 : ℤ) : ℤ) = 2 + (2 : ℕ) * (2 : ℤ) by norm_num, hb, hβ.coeff_pow_min 2]
      rw [show (2 + (2 : ℕ) * (2 : ℤ) : ℤ) = 4 + 2 by norm_num, hc]
      rw [show (4 + 2 : ℤ) = 6 by norm_num, he3_c, he2_c, he1_c, he0_c]
      simp only [β, HahnSeries.coeff_single_same]
      apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 S_K_ne_zero) (pow_ne_zero 6 fiveS_sub_9Q_ne))
      rw [mul_zero]
      have hstep :
          S_K ^ 2 * (5 * S_K - 9 * Q_K) ^ 6 *
            (k5Params.Q7_z.coeff 0 * z1 ^ 3 +
              (-k5Params.c21 * k5Params.cb_h ^ 2 + 2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h -
                3 * k5Params.c03 * k5Params.ca_h ^ 2).coeff 0 * k5Params.c0_V0 * z1 ^ 2 +
              (k5Params.c12 * k5Params.cb_h - 3 * k5Params.c03 * k5Params.ca_h).coeff 0 * k5Params.c0_V0 ^ 2 * z1 +
              k5Params.cb_h.coeff 0 ^ 3 * (-(k5Params.Cv0 / k5Params.Bv0)) ^ 2 * k5Params.k3_V0) =
          k5Params.Q7_z.coeff 0 * S_K ^ 2 * ((5 * S_K - 9 * Q_K) ^ 2 * z1) ^ 3 +
          (-k5Params.c21 * k5Params.cb_h ^ 2 + 2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h -
            3 * k5Params.c03 * k5Params.ca_h ^ 2).coeff 0 * k5Params.c0_V0 *
            S_K ^ 2 * (5 * S_K - 9 * Q_K) ^ 2 * ((5 * S_K - 9 * Q_K) ^ 2 * z1) ^ 2 +
          (k5Params.c12 * k5Params.cb_h - 3 * k5Params.c03 * k5Params.ca_h).coeff 0 * k5Params.c0_V0 ^ 2 *
            S_K ^ 2 * (5 * S_K - 9 * Q_K) ^ 4 * ((5 * S_K - 9 * Q_K) ^ 2 * z1) +
          k5Params.cb_h.coeff 0 ^ 3 * k5Params.k3_V0 * (5 * S_K - 9 * Q_K) ^ 2 *
            (S_K * (5 * S_K - 9 * Q_K) ^ 2 * (k5Params.Cv0 / k5Params.Bv0)) ^ 2 := by ring
      rw [hstep, hz1_mul, hCvBv_mul, hQ7_0, he2_s, he1_s, hcb0]
      simp only [CoverParams.c0_V0, CoverParams.k3_V0, CoverParams.inv81, CoverParams.inv243, k5Params_inv3, k5Params_T]
      generalize 5 * S_K - 9 * Q_K = A
      ring
    exact HasValGe.syl5 hq2 hq1' hq0' he3 he2' he1' he0'
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

  exact h1
end CoverX15W1
end SymmetricSexticResidual.CoverAlgebra

theorem solution :
    QuadraticCovers.HasValGe 13
      (QuadraticCovers.PairAlg.evalAt SymmetricSexticResidual.CoverAlgebra.W1_0
        (QuadraticCovers.PairAlg.map QuadraticCovers.evalT
          SymmetricSexticResidual.CoverAlgebra.k5Params.res_z)) :=
  SymmetricSexticResidual.CoverAlgebra.res_z_W1_0_hasValGe_13
