-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.cover_X15_W2_val
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T08:39:35.558168+00:00
-- url     : https://prove2.me/submissions/7efbc787-bb80-45ac-aa03-fb466b935714

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

noncomputable section CoverX15W2
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


lemma res_z_W2_0_hasValGe_2 :
    HasValGe 2 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.res_z)) := by
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

  have h2 : HasValGe 2 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.res_z)) := by
    have hw := HasValGe_W2_0
    have hw_eq := W2_0_eq
    rw [CoverParams.res_z, map_syl5Pair, evalAt_syl5Pair _ _ _ _ _ _ _ _ _ W2_0 hw_eq]
    have htoUW_2 (v0 v1 v2 : K5) :
        HasValGe 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT (k5Params.toUW v0 v1 v2))) ∧
        (PairAlg.evalAt W2_0 (PairAlg.map evalT (k5Params.toUW v0 v1 v2))).coeff 0 =
          v2 * (-(k5Params.Bv0 * k5Params.Av0_inv)) ^ 2 := by
      rw [evalT_toUW_eq v0 v1 v2 W2_0 hw_eq]
      have ht2 : HasValGe 0 (HahnSeries.C v2 * W2_0 ^ 2) :=
        ((HasValGe.of_C v2).mul (hw.pow 2)).mono (by omega)
      have ht1 : HasValGe 1 (HahnSeries.C v1 * HahnSeries.single 1 1 * W2_0 +
          HahnSeries.C v0 * HahnSeries.single 2 1) :=
        ((((HasValGe.of_C v1).mul (HasValGe.single 1 1)).mul hw).mono (by omega)).add
          (((HasValGe.of_C v0).mul (HasValGe.single 2 1)).mono (by omega))
      rw [add_assoc]
      refine ⟨ht2.add (ht1.mono (by omega)), ?_⟩
      rw [HasValGe.coeff_of_add ht1]
      have hm := (HasValGe.of_C v2).coeff_mul_min (hw.pow 2)
      simp only [zero_add] at hm
      change (HahnSeries.C v2 * W2_0 ^ 2).coeff ((2 : ℕ) * (0 : ℤ)) = _
      rw [hm, HahnSeries.C_apply, HahnSeries.coeff_single_same, hw.coeff_pow_min 2, W2_0_coeff0]
    obtain ⟨hc0W, hc0W_c⟩ : HasValGe 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.c0W)) ∧
        (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.c0W)).coeff 0 =
          k5Params.c0_V2 * (-(k5Params.Bv0 * k5Params.Av0_inv)) ^ 2 :=
      htoUW_2 k5Params.c0_V0 k5Params.c0_V1 k5Params.c0_V2
    obtain ⟨hk2W, hk2W_c⟩ : HasValGe 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.k2W)) ∧
        (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.k2W)).coeff 0 =
          k5Params.k2_V2 * (-(k5Params.Bv0 * k5Params.Av0_inv)) ^ 2 :=
      htoUW_2 k5Params.k2_V0 k5Params.k2_V1 k5Params.k2_V2
    obtain ⟨hk3W, hk3W_c⟩ : HasValGe 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.k3W)) ∧
        (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.k3W)).coeff 0 =
          k5Params.k3_V2 * (-(k5Params.Bv0 * k5Params.Av0_inv)) ^ 2 :=
      htoUW_2 k5Params.k3_V0 k5Params.k3_V1 k5Params.k3_V2
    set q2 := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d2_2)
    set q1 := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d2_1)
    set q0 := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d2_0)
    set e3 := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d3_3)
    set e2 := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d3_2)
    set e1 := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d3_1)
    set e0 := PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.d3_0)
    have hq2 : HasValGe 0 q2 := by simpa [q2, CoverParams.d2_2, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using hQ5
    have hq1 : HasValGe 0 q1 := by
      simp only [q1, CoverParams.d2_1, PairAlg.map_smul, PairAlg.evalAt_smul]
      exact (hd2_1_sc.mul hc0W).mono (by omega)
    have hq0 : HasValGe 0 q0 := by
      simp only [q0, CoverParams.d2_0, PairAlg.map_add, PairAlg.evalAt_add, PairAlg.map_smul, PairAlg.evalAt_smul,
        CoverParams.pmul, PairAlg.map_mul, PairAlg.evalAt_mul _ _ W2_0 hw_eq, PairAlg.map_W, PairAlg.evalAt_W, map_pow]
      exact ((hq02.mul (hc0W.mul hc0W)).mono (by omega)).add (((hcb.pow 2).mul (hw.mul hk2W)).mono (by omega))
    have he3 : HasValGe 0 e3 := by simpa [e3, CoverParams.d3_3, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar] using hQ7
    have he2 : HasValGe 0 e2 := by
      simp only [e2, CoverParams.d3_2, PairAlg.map_smul, PairAlg.evalAt_smul]
      exact (hd3_2_sc.mul hc0W).mono (by omega)
    have he1 : HasValGe 0 e1 := by
      simp only [e1, CoverParams.d3_1, PairAlg.map_smul, PairAlg.evalAt_smul, CoverParams.pmul,
        PairAlg.map_mul, PairAlg.evalAt_mul _ _ W2_0 hw_eq]
      exact (hd3_1_sc.mul (hc0W.mul hc0W)).mono (by omega)
    have he0 : HasValGe 0 e0 := by
      simp only [e0, CoverParams.d3_0, PairAlg.map_add, PairAlg.evalAt_add, PairAlg.map_smul, PairAlg.evalAt_smul,
        CoverParams.pmul, PairAlg.map_mul, PairAlg.evalAt_mul _ _ W2_0 hw_eq, PairAlg.map_W, PairAlg.evalAt_W,
        map_neg, map_pow]
      exact ((hc03.neg.mul (hc0W.mul (hc0W.mul hc0W))).mono (by omega)).add
        (((hcb.pow 3).mul ((hw.mul hw).mul hk3W)).mono (by omega))
    let z2 : K5 := -(k5Params.Bv0 * k5Params.Av0_inv) * S_K / (T_K - 3)
    let β : LaurentSeries K5 := HahnSeries.C z2
    have hβ : HasValGe 0 β := HasValGe.of_C z2
    have hshift := syl5_affine q2 q1 q0 e3 e2 e1 e0 1 β
    simp only [one_pow, mul_one, one_mul] at hshift
    rw [← hshift]
    have hq2_c : q2.coeff 0 = k5Params.Q5_z.coeff 0 := by
      simp only [q2, CoverParams.d2_2, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar, hcoeff0_evalT]
    have hq1_c : q1.coeff 0 = (-k5Params.q11 * k5Params.cb_h + 2 * k5Params.q02 * k5Params.ca_h).coeff 0 *
        (k5Params.c0_V2 * (-(k5Params.Bv0 * k5Params.Av0_inv)) ^ 2) := by
      simp only [q1, CoverParams.d2_1, PairAlg.map_smul, PairAlg.evalAt_smul]
      rw [show (0 : ℤ) = 0 + 0 by norm_num, hd2_1_sc.coeff_mul_min hc0W, hcoeff0_evalT, hc0W_c]
    have hq0_c : q0.coeff 0 = k5Params.q02.coeff 0 * (k5Params.c0_V2 * (-(k5Params.Bv0 * k5Params.Av0_inv)) ^ 2) ^ 2 +
        k5Params.cb_h.coeff 0 ^ 2 * (-(k5Params.Bv0 * k5Params.Av0_inv)) *
          (k5Params.k2_V2 * (-(k5Params.Bv0 * k5Params.Av0_inv)) ^ 2) := by
      simp only [q0, CoverParams.d2_0, PairAlg.map_add, PairAlg.evalAt_add, PairAlg.map_smul, PairAlg.evalAt_smul,
        CoverParams.pmul, PairAlg.map_mul, PairAlg.evalAt_mul _ _ W2_0 hw_eq, PairAlg.map_W, PairAlg.evalAt_W,
        map_pow, HahnSeries.coeff_add]
      have ha := hq02.coeff_mul_min (hc0W.mul hc0W)
      have hb := (hcb.pow 2).coeff_mul_min (hw.mul hk2W)
      rw [show (0 : ℤ) = 0 + (0 + 0) by norm_num, ha, hc0W.coeff_mul_min hc0W]
      rw [show (0 + (0 + 0) : ℤ) = (2 : ℕ) * (0 : ℤ) + (0 + 0) by norm_num, hb, hcb.coeff_pow_min 2,
        hw.coeff_mul_min hk2W, W2_0_coeff0, hcoeff0_evalT, hcoeff0_evalT, hc0W_c, hk2W_c]; ring
    have he3_c : e3.coeff 0 = k5Params.Q7_z.coeff 0 := by
      simp only [e3, CoverParams.d3_3, PairAlg.map_ofScalar, PairAlg.evalAt_ofScalar, hcoeff0_evalT]
    have he2_c : e2.coeff 0 = (-k5Params.c21 * k5Params.cb_h ^ 2 +
        2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h - 3 * k5Params.c03 * k5Params.ca_h ^ 2).coeff 0 *
        (k5Params.c0_V2 * (-(k5Params.Bv0 * k5Params.Av0_inv)) ^ 2) := by
      simp only [e2, CoverParams.d3_2, PairAlg.map_smul, PairAlg.evalAt_smul]
      rw [show (0 : ℤ) = 0 + 0 by norm_num, hd3_2_sc.coeff_mul_min hc0W, hcoeff0_evalT, hc0W_c]
    have he1_c : e1.coeff 0 = (k5Params.c12 * k5Params.cb_h - 3 * k5Params.c03 * k5Params.ca_h).coeff 0 *
        (k5Params.c0_V2 * (-(k5Params.Bv0 * k5Params.Av0_inv)) ^ 2) ^ 2 := by
      simp only [e1, CoverParams.d3_1, PairAlg.map_smul, PairAlg.evalAt_smul, CoverParams.pmul,
        PairAlg.map_mul, PairAlg.evalAt_mul _ _ W2_0 hw_eq]
      rw [show (0 : ℤ) = 0 + (0 + 0) by norm_num, hd3_1_sc.coeff_mul_min (hc0W.mul hc0W),
        hc0W.coeff_mul_min hc0W, hcoeff0_evalT, hc0W_c]; ring
    have he0_c : e0.coeff 0 = k5Params.cb_h.coeff 0 ^ 3 * (-(k5Params.Bv0 * k5Params.Av0_inv)) ^ 2 *
        (k5Params.k3_V2 * (-(k5Params.Bv0 * k5Params.Av0_inv)) ^ 2) := by
      simp only [e0, CoverParams.d3_0, PairAlg.map_add, PairAlg.evalAt_add, PairAlg.map_smul, PairAlg.evalAt_smul,
        CoverParams.pmul, PairAlg.map_mul, PairAlg.evalAt_mul _ _ W2_0 hw_eq, PairAlg.map_W, PairAlg.evalAt_W,
        map_neg, map_pow]
      have ht1 : HasValGe 1 (-evalT k5Params.c03 * (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.c0W) *
          (PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.c0W) *
           PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.c0W)))) :=
        (hc03.neg.mul (hc0W.mul (hc0W.mul hc0W))).mono (by omega)
      rw [add_comm, HasValGe.coeff_of_add ht1]
      have hb := (hcb.pow 3).coeff_mul_min ((hw.mul hw).mul hk3W)
      rw [show (0 : ℤ) = (3 : ℕ) * (0 : ℤ) + (0 + 0 + 0) by norm_num, hb, hcb.coeff_pow_min 3,
        (hw.mul hw).coeff_mul_min hk3W, hw.coeff_mul_min hw, W2_0_coeff0, hcoeff0_evalT, hk3W_c]; ring
    have hβ_c : β.coeff 0 = z2 := by simp only [β, HahnSeries.C_apply, HahnSeries.coeff_single_same]
    have hnc (m : ℕ) : ((m : LaurentSeries K5)).coeff 0 = (m : K5) := by
      rw [show (m : LaurentSeries K5) = HahnSeries.C (m : K5) by simp, HahnSeries.C_apply, HahnSeries.coeff_single_same]
    have hw0_eq : -(k5Params.Bv0 * k5Params.Av0_inv) =
        -(25 / 4 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 2 / (T_K - 3) ^ 3 := by
      simp only [CoverParams.Bv0, CoverParams.Av0_inv, CoverParams.inv4, CoverParams.inv243,
        k5Params_inv2, k5Params_inv3, k5Params_invT3, k5Params_S, k5Params_Q]
      have hT := T_K_sub_3_ne
      field_simp [hT]; ring
    have hq1' : HasValGe 1 (2 * q2 * β + q1) := by
      apply (((((HasValGe.of_nat 2).mul hq2).mul hβ).mono (by omega)).add hq1).inc
      rw [HahnSeries.coeff_add]
      have hm := ((HasValGe.of_nat 2).mul hq2).coeff_mul_min hβ
      have hm2 := (HasValGe.of_nat 2).coeff_mul_min hq2
      simp only [zero_add] at hm hm2
      rw [hm, hm2, hnc 2, hq2_c, hq1_c, hβ_c]
      simp only [Nat.cast_ofNat, z2, hw0_eq, hQ5_0, hq1_s, CoverParams.c0_V2, CoverParams.inv81,
        k5Params_inv3, k5Params_T]
      have hT := T_K_sub_3_ne
      generalize 5 * S_K - 9 * Q_K = A
      generalize T_K - 3 = B at hT ⊢
      field_simp [hT]; ring
    have hq0' : HasValGe 1 (q2 * β ^ 2 + q1 * β + q0) := by
      apply ((((hq2.mul (hβ.pow 2)).mono (by omega)).add ((hq1.mul hβ).mono (by omega))).add hq0).inc
      rw [HahnSeries.coeff_add, HahnSeries.coeff_add]
      have ha := hq2.coeff_mul_min (hβ.pow 2)
      have hb := hq1.coeff_mul_min hβ
      have hp2 := hβ.coeff_pow_min 2
      simp only [mul_zero, zero_add] at ha hb hp2
      rw [ha, hp2, hb, hq2_c, hq1_c, hq0_c, hβ_c]
      simp only [z2, hw0_eq, hQ5_0, hq1_s, hq02_0, hcb0, CoverParams.c0_V2, CoverParams.k2_V2,
        CoverParams.inv81, k5Params_inv3, k5Params_T]
      have hT := T_K_sub_3_ne
      generalize 5 * S_K - 9 * Q_K = A
      generalize T_K - 3 = B at hT ⊢
      field_simp [hT]; ring
    have he2' : HasValGe 0 (3 * e3 * β + e2) :=
      ((((HasValGe.of_nat 3).mul he3).mul hβ).mono (by omega)).add he2
    have he1' : HasValGe 1 (3 * e3 * β ^ 2 + 2 * e2 * β + e1) := by
      apply (((((HasValGe.of_nat 3).mul he3).mul (hβ.pow 2)).mono (by omega)).add
        ((((HasValGe.of_nat 2).mul he2).mul hβ).mono (by omega)) |>.add he1).inc
      rw [HahnSeries.coeff_add, HahnSeries.coeff_add]
      have ha := ((HasValGe.of_nat 3).mul he3).coeff_mul_min (hβ.pow 2)
      have ha3 := (HasValGe.of_nat 3).coeff_mul_min he3
      have hb := ((HasValGe.of_nat 2).mul he2).coeff_mul_min hβ
      have hb2 := (HasValGe.of_nat 2).coeff_mul_min he2
      have hp2 := hβ.coeff_pow_min 2
      simp only [mul_zero, zero_add] at ha ha3 hb hb2 hp2
      rw [ha, ha3, hp2, hb, hb2, hnc 2, hnc 3, he3_c, he2_c, he1_c, hβ_c]
      simp only [Nat.cast_ofNat, z2, hw0_eq, hQ7_0, he2_s, he1_s, CoverParams.c0_V2,
        CoverParams.inv81, k5Params_inv3, k5Params_T]
      have hT := T_K_sub_3_ne
      generalize 5 * S_K - 9 * Q_K = A
      generalize T_K - 3 = B at hT ⊢
      field_simp [hT]; ring
    have he0' : HasValGe 1 (e3 * β ^ 3 + e2 * β ^ 2 + e1 * β + e0) := by
      apply (((((he3.mul (hβ.pow 3)).mono (by omega)).add ((he2.mul (hβ.pow 2)).mono (by omega))).add
        ((he1.mul hβ).mono (by omega))).add he0).inc
      rw [HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_add]
      have ha := he3.coeff_mul_min (hβ.pow 3)
      have hb := he2.coeff_mul_min (hβ.pow 2)
      have hc := he1.coeff_mul_min hβ
      have hp3 := hβ.coeff_pow_min 3
      have hp2 := hβ.coeff_pow_min 2
      simp only [mul_zero, zero_add] at ha hb hc hp3 hp2
      rw [ha, hp3, hb, hp2, hc, he3_c, he2_c, he1_c, he0_c, hβ_c]
      simp only [z2, hw0_eq, hQ7_0, he2_s, he1_s, hcb0, CoverParams.c0_V2, CoverParams.k3_V2,
        CoverParams.inv81, CoverParams.inv243, k5Params_inv3, k5Params_T]
      have hT := T_K_sub_3_ne
      generalize 5 * S_K - 9 * Q_K = A
      generalize T_K - 3 = B at hT ⊢
      field_simp [hT]; ring
    exact HasValGe.syl5 hq2 hq1' hq0' he3 he2' he1' he0'
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

  exact h2
end CoverX15W2
end SymmetricSexticResidual.CoverAlgebra

theorem solution :
    QuadraticCovers.HasValGe 2
      (QuadraticCovers.PairAlg.evalAt SymmetricSexticResidual.CoverAlgebra.W2_0
        (QuadraticCovers.PairAlg.map QuadraticCovers.evalT
          SymmetricSexticResidual.CoverAlgebra.k5Params.res_z)) :=
  SymmetricSexticResidual.CoverAlgebra.res_z_W2_0_hasValGe_2
