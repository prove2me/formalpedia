-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localU0_br1_g_scaled
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T11:56:19.439045+00:00
-- url     : https://prove2.me/submissions/b5195b4a-d722-48bb-be72-13fff2b89e94

import Definitions.Def_HodgeComputerSSR_BranchHelpers
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_branch_jet_helpers

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueU0
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  PolynomialEncoding.KroneckerCheck QuadraticCovers CrossedRationalResidue Polynomial
open scoped BigOperators LaurentSeries PowerSeries

private abbrev numM_ValLead_of := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.numM_ValLead
private abbrev A0U_ValLead_of := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.A0U_ValLead
private abbrev A0V_ValLead_of := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.A0V_ValLead
private abbrev EB_bilinear_UV := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.EB_bilinear
private abbrev QY_bilinear_UV := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.QY_bilinear
private abbrev QX_bilinear_UV := @HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers.QX_bilinear

private lemma A0U_at_zero {R : Type*} [Field R] (a b xS xQ w : R) :
    A_0U a b xS xQ 0 w = 0 := by
  simp only [A_0U, numM, q1_a2, q1_a1, q1_a0, q2_b2, q2_b1, q2_b0, dH_dS, dH_dQ]; ring

private lemma AY_t1_at_zero {R : Type*} [Field R] (a b xS xQ w : R) :
    25 * numM 3 a b xS xQ 0 w - 45 * numM 4 a b xS xQ 0 w -
    45 * numM 5 a b xS xQ 0 w + 81 * numM 6 a b xS xQ 0 w = 0 := by
  simp only [numM, q1_a2, q1_a1, q1_a0, q2_b2, q2_b1, q2_b0, dH_dS, dH_dQ]; ring

private lemma A0V_at_zero_xiS0 {R : Type*} [Field R] [CharZero R] (a b xQ w : R)
    (hrel : 5 * a - 9 * b = 5 * xQ) :
    A_0V a b 0 xQ 0 w = 0 := by
  have hxQ : xQ = a - (9 / 5 : R) * b := by
    have h5 : (5 : R) ≠ 0 := by exact_mod_cast (by decide : (5 : ℕ) ≠ 0)
    apply mul_left_cancel₀ h5
    linear_combination -hrel
  rw [hxQ]
  simp only [A_0V, numM, q1_a2, q1_a1, q1_a0, q2_b2, q2_b1, q2_b0, dH_dS, dH_dQ]
  ring

private lemma QY_num_00_factor {R : Type*} [Field R] [CharZero R] (S Q T x y a b : R) :
    (5 * S - 9 * Q) * (5 * T - 9) * dot_ab (QY_num S Q T x y 0 0) a b =
    4 * y * (-25 * S + 45 * Q + 27 * x) * S ^ 2 * T ^ 2 * DY2_of T y *
      ((-(25 / 81 : R) * (5 * S - 9 * Q) * (5 * S - 3 * Q)) * a * (-T * (5 * T - 9) ^ 2) +
       ((50 / 27 : R) * S * (5 * S - 9 * Q)) * b * (-T * (5 * T - 9) ^ 2) +
       S * (5 * S - 9 * Q) ^ 2 * (-(25 / 81 : R) * (5 * T - 9) * (5 * T - 3))) := by
  simp only [dot_ab, QY_num, Omega_F, dDX2_F, F_contract, dF5_fn, dH0_fn, dDX2_fn,
    u3_of, v3_of, om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u_of, v_of]
  ring

private lemma QX_num_00_factor {R : Type*} [Field R] [CharZero R] (S Q T x y a b : R) :
    (5 * S - 9 * Q) * (5 * T - 9) * dot_ab (QX_num S Q T x y 0 0) a b =
    4 * x * (-25 * T + 45 + 27 * y) * S ^ 2 * T ^ 2 * DX2_of S Q x *
      ((-(25 / 81 : R) * (5 * S - 9 * Q) * (5 * S - 3 * Q)) * a * (-T * (5 * T - 9) ^ 2) +
       ((50 / 27 : R) * S * (5 * S - 9 * Q)) * b * (-T * (5 * T - 9) ^ 2) +
       S * (5 * S - 9 * Q) ^ 2 * (-(25 / 81 : R) * (5 * T - 9) * (5 * T - 3))) := by
  simp only [dot_ab, QX_num, Omega_F, dDY2_F, F_contract, dF5_fn, dH0_fn, dDY2_fn,
    u3_of, v3_of, om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u_of, v_of]
  ring


private lemma br1_0_numM_bounds
    {a_s b_s U V : LaurentSeries K5} {a0 b0 w2 : K5}
    (hw2_ne : w2 ≠ 0)
    (ha_L : ValLead 0 a_s a0) (hb_L : ValLead 0 b_s b0)
    (hU_L : ValLead 1 U 1) (hV_L : ValLead 1 V w2) :
    let ξS_s := HahnSeries.C S_K - a_s * HahnSeries.C T_K
    let ξQ_s := HahnSeries.C Q_K - b_s * HahnSeries.C T_K
    let ξS0 : K5 := S_K - a0 * T_K
    let ξQ0 : K5 := Q_K - b0 * T_K
    ValLead 1 (A_0U a_s b_s ξS_s ξQ_s U V / U + A_0V a_s b_s ξS_s ξQ_s U V / V)
      (A_0V a0 b0 ξS0 ξQ0 0 w2 / w2) ∧
    HasValGe 3 (A_Y a_s b_s ξS_s ξQ_s U V) ∧
    HasValGe 3 (A_X a_s b_s ξS_s ξQ_s U V) := by
  intro ξS_s ξQ_s ξS0 ξQ0
  have hξS_L : ValLead 0 ξS_s ξS0 :=
    (ValLead.of_C S_K).sub ((ha_L.mul (ValLead.of_C T_K)).eq_k (by omega))
  have hξQ_L : ValLead 0 ξQ_s ξQ0 :=
    (ValLead.of_C Q_K).sub ((hb_L.mul (ValLead.of_C T_K)).eq_k (by omega))
  -- At `U = O(t), V = w2*t + O(t^2)`, `dH_dS` and `dH_dQ` have `ValLead 1` with `U = 0`!
  have hdH_S_L {s q : LaurentSeries K5} {s0 q0 : K5} (hs : ValLead 0 s s0) (hq : ValLead 0 q q0) :
      ValLead 1 (dH_dS s q U V) (-(25 / 243 : K5) * (5 * s0 - 9 * q0) * (15 * s0 - 9 * q0) * w2) := by
    unfold dH_dS
    have h1 : HasValGe 2 (-(4 / 81 : LaurentSeries K5) * (s - 3 * q) ^ 2 * U ^ 2 * V) := by
      have hsq : HasValGe 0 ((s - 3 * q) ^ 2) := ((hs.val.sub ((HasValGe.of_nat 3).mul hq.val |>.mono (by omega))).pow 2).mono (by omega)
      have hc4 : HasValGe 0 (-(4 / 81 : LaurentSeries K5)) := by
        have : -(4 / 81 : LaurentSeries K5) = HahnSeries.C (-(4 / 81 : K5)) := by simp only [map_div₀, map_neg, map_ofNat]
        rw [this]; exact HasValGe.of_C _
      exact (((hc4.mul hsq).mul (hU_L.val.pow 2)).mul hV_L.val).mono (by omega)
    have h2 : HasValGe 2 (((143 / 81 : LaurentSeries K5) * s ^ 2 - (184 / 27) * s * q +
        (52 / 9) * q ^ 2) * U * V) := by
      have hq0 : HasValGe 0 ((143 / 81 : LaurentSeries K5) * s ^ 2 - (184 / 27) * s * q + (52 / 9) * q ^ 2) := by
        have hc (r : K5) : HasValGe 0 (HahnSeries.C r) := HasValGe.of_C r
        have ha : HasValGe 0 ((143 / 81 : LaurentSeries K5) * s ^ 2) := by
          rw [show (143 / 81 : LaurentSeries K5) = HahnSeries.C (143 / 81 : K5) by simp only [map_div₀, map_ofNat]]
          exact ((hc _).mul (hs.val.pow 2)).mono (by omega)
        have hb : HasValGe 0 ((184 / 27 : LaurentSeries K5) * s * q) := by
          rw [show (184 / 27 : LaurentSeries K5) = HahnSeries.C (184 / 27 : K5) by simp only [map_div₀, map_ofNat]]
          exact (((hc _).mul hs.val).mul hq.val).mono (by omega)
        have hcc : HasValGe 0 ((52 / 9 : LaurentSeries K5) * q ^ 2) := by
          rw [show (52 / 9 : LaurentSeries K5) = HahnSeries.C (52 / 9 : K5) by simp only [map_div₀, map_ofNat]]
          exact ((hc _).mul (hq.val.pow 2)).mono (by omega)
        exact (ha.sub hb).add hcc
      exact ((hq0.mul hU_L.val).mul hV_L.val).mono (by omega)
    have h3 : ValLead 1 ((25 / 243 : LaurentSeries K5) * (5 * s - 9 * q) * (15 * s - 9 * q) * V)
        ((25 / 243 : K5) * (5 * s0 - 9 * q0) * (15 * s0 - 9 * q0) * w2) := by
      have hc : ValLead 0 (25 / 243 : LaurentSeries K5) (25 / 243 : K5) := by
        rw [show (25 / 243 : LaurentSeries K5) = HahnSeries.C (25 / 243 : K5) by simp only [map_div₀, map_ofNat]]; exact ValLead.of_C _
      have hl1 : ValLead 0 (5 * s - 9 * q) (5 * s0 - 9 * q0) :=
        (((ValLead.of_nat 5).mul hs).eq_k (by omega)).sub (((ValLead.of_nat 9).mul hq).eq_k (by omega))
          |>.eq_c (by push_cast; rfl)
      have hl2 : ValLead 0 (15 * s - 9 * q) (15 * s0 - 9 * q0) :=
        (((ValLead.of_nat 15).mul hs).eq_k (by omega)).sub (((ValLead.of_nat 9).mul hq).eq_k (by omega))
          |>.eq_c (by push_cast; rfl)
      exact (((hc.mul hl1).mul hl2).mul hV_L).eq_k (by omega)
    rw [sub_eq_add_neg, add_comm]
    exact (h3.neg.add_high (h1.add h2)).eq_c (by ring)
  have hdH_Q_L {s q : LaurentSeries K5} {s0 q0 v0 : K5} (hs : ValLead 0 s s0) (hq : ValLead 0 q q0) :
      ValLead 1 (dH_dQ s q (HahnSeries.C v0) U V) ((50 / 27 : K5) * s0 * (5 * s0 - 9 * q0) * w2) := by
    unfold dH_dQ
    have h1 : HasValGe 2 ((4 / 27 : LaurentSeries K5) * (s - 3 * q) ^ 2 * U ^ 2 * V) := by
      rw [show (4 / 27 : LaurentSeries K5) = HahnSeries.C (4 / 27 : K5) by simp only [map_div₀, map_ofNat]]
      have hsq : HasValGe 0 ((s - 3 * q) ^ 2) :=
        ((hs.val.sub ((HasValGe.of_nat 3).mul hq.val |>.mono (by omega))).pow 2).mono (by omega)
      exact ((((HasValGe.of_C _).mul hsq).mul (hU_L.val.pow 2)).mul hV_L.val).mono (by omega)
    have h2 : HasValGe 2 ((-(92 / 27 : LaurentSeries K5) * s ^ 2 + (104 / 9) * s * q -
        (22 / 3) * q ^ 2 + (10 / 7) * q * HahnSeries.C v0 +
        (10 / 7) * HahnSeries.C v0 ^ 2) * U * V) := by
      have hq0 : HasValGe 0 (-(92 / 27 : LaurentSeries K5) * s ^ 2 + (104 / 9) * s * q -
          (22 / 3) * q ^ 2 + (10 / 7) * q * HahnSeries.C v0 + (10 / 7) * HahnSeries.C v0 ^ 2) := by
        have ha : HasValGe 0 (-(92 / 27 : LaurentSeries K5) * s ^ 2) := by
          rw [show -(92 / 27 : LaurentSeries K5) = HahnSeries.C (-(92 / 27 : K5)) by simp only [map_div₀, map_neg, map_ofNat]]
          exact ((HasValGe.of_C _).mul (hs.val.pow 2)).mono (by omega)
        have hb : HasValGe 0 ((104 / 9 : LaurentSeries K5) * s * q) := by
          rw [show (104 / 9 : LaurentSeries K5) = HahnSeries.C (104 / 9 : K5) by simp only [map_div₀, map_ofNat]]
          exact (((HasValGe.of_C _).mul hs.val).mul hq.val).mono (by omega)
        have hc : HasValGe 0 ((22 / 3 : LaurentSeries K5) * q ^ 2) := by
          rw [show (22 / 3 : LaurentSeries K5) = HahnSeries.C (22 / 3 : K5) by simp only [map_div₀, map_ofNat]]
          exact ((HasValGe.of_C _).mul (hq.val.pow 2)).mono (by omega)
        have hd : HasValGe 0 ((10 / 7 : LaurentSeries K5) * q * HahnSeries.C v0) := by
          rw [show (10 / 7 : LaurentSeries K5) = HahnSeries.C (10 / 7 : K5) by simp only [map_div₀, map_ofNat]]
          exact (((HasValGe.of_C _).mul hq.val).mul (HasValGe.of_C v0)).mono (by omega)
        have he : HasValGe 0 ((10 / 7 : LaurentSeries K5) * HahnSeries.C v0 ^ 2) := by
          rw [show (10 / 7 : LaurentSeries K5) = HahnSeries.C (10 / 7 : K5) by simp only [map_div₀, map_ofNat]]
          exact ((HasValGe.of_C _).mul ((HasValGe.of_C v0).pow 2)).mono (by omega)
        exact (((ha.add hb).sub hc).add hd).add he
      exact ((hq0.mul hU_L.val).mul hV_L.val).mono (by omega)
    have h3 : ValLead 1 ((50 / 27 : LaurentSeries K5) * s * (5 * s - 9 * q) * V)
        ((50 / 27 : K5) * s0 * (5 * s0 - 9 * q0) * w2) := by
      have hc : ValLead 0 (50 / 27 : LaurentSeries K5) (50 / 27 : K5) := by
        rw [show (50 / 27 : LaurentSeries K5) = HahnSeries.C (50 / 27 : K5) by simp only [map_div₀, map_ofNat]]; exact ValLead.of_C _
      have hl1 : ValLead 0 (5 * s - 9 * q) (5 * s0 - 9 * q0) :=
        (((ValLead.of_nat 5).mul hs).eq_k (by omega)).sub (((ValLead.of_nat 9).mul hq).eq_k (by omega))
          |>.eq_c (by push_cast; rfl)
      exact (((hc.mul hs).mul hl1).mul hV_L).eq_k (by omega)
    rw [add_comm]
    exact h3.add_high (h1.add h2)
  -- All `numM i` have `ValLead 2` equal to `numM i a0 b0 ξS0 ξQ0 0 w2`!
  have hnumM_L (mi : Fin 10) :
      ValLead 2 (numM mi a_s b_s ξS_s ξQ_s U V) (numM mi a0 b0 ξS0 ξQ0 0 w2) := by
    have ha2 := hdH_S_L ha_L hb_L
    have ha0 := hdH_S_L hξS_L hξQ_L
    have ha1 := ((hdH_S_L (ha_L.add hξS_L) (hb_L.add hξQ_L)).sub ha2).sub ha0
    have hb2 : ValLead 1 (q2_b2 a_s b_s U V) ((50 / 27 : K5) * a0 * (5 * a0 - 9 * b0) * w2) := by
      simpa [q2_b2] using hdH_Q_L (v0 := 0) ha_L hb_L
    have hb0 : ValLead 1 (q2_b0 ξS_s ξQ_s U V) ((50 / 27 : K5) * ξS0 * (5 * ξS0 - 9 * ξQ0) * w2) := by
      simpa [q2_b0] using hdH_Q_L (v0 := 1) hξS_L hξQ_L
    have hb1 : ValLead 1 (q2_b1 a_s b_s ξS_s ξQ_s U V)
        ((50 / 27 : K5) * (a0 + ξS0) * (5 * (a0 + ξS0) - 9 * (b0 + ξQ0)) * w2 -
         (50 / 27 : K5) * a0 * (5 * a0 - 9 * b0) * w2 -
         (50 / 27 : K5) * ξS0 * (5 * ξS0 - 9 * ξQ0) * w2) := by
      unfold q2_b1
      have hbase := ((hdH_Q_L (v0 := 0) (ha_L.add hξS_L) (hb_L.add hξQ_L)).sub
        (hdH_Q_L (v0 := 0) ha_L hb_L)).sub (hdH_Q_L (v0 := 0) hξS_L hξQ_L)
      have hbase' : ValLead 1 (dH_dQ (a_s + ξS_s) (b_s + ξQ_s) 0 U V - dH_dQ a_s b_s 0 U V -
          dH_dQ ξS_s ξQ_s 0 U V)
          ((50 / 27 : K5) * (a0 + ξS0) * (5 * (a0 + ξS0) - 9 * (b0 + ξQ0)) * w2 -
           (50 / 27 : K5) * a0 * (5 * a0 - 9 * b0) * w2 -
           (50 / 27 : K5) * ξS0 * (5 * ξS0 - 9 * ξQ0) * w2) := by
        simpa only [map_zero] using hbase
      have hextra : HasValGe 2 ((10 / 7 : LaurentSeries K5) * b_s * U * V) := by
        rw [show (10 / 7 : LaurentSeries K5) = HahnSeries.C (10 / 7 : K5) by simp only [map_div₀, map_ofNat]]
        exact ((((HasValGe.of_C _).mul hb_L.val).mul hU_L.val).mul hV_L.val).mono (by omega)
      exact hbase'.add_high hextra
    let a2_0 : K5 := -(25 / 243 : K5) * (5 * a0 - 9 * b0) * (15 * a0 - 9 * b0) * w2
    let a0_0 : K5 := -(25 / 243 : K5) * (5 * ξS0 - 9 * ξQ0) * (15 * ξS0 - 9 * ξQ0) * w2
    let a1_0 : K5 := -(25 / 243 : K5) * (5 * (a0 + ξS0) - 9 * (b0 + ξQ0)) * (15 * (a0 + ξS0) - 9 * (b0 + ξQ0)) * w2 - a2_0 - a0_0
    let b2_0 : K5 := (50 / 27 : K5) * a0 * (5 * a0 - 9 * b0) * w2
    let b0_0 : K5 := (50 / 27 : K5) * ξS0 * (5 * ξS0 - 9 * ξQ0) * w2
    let b1_0 : K5 := (50 / 27 : K5) * (a0 + ξS0) * (5 * (a0 + ξS0) - 9 * (b0 + ξQ0)) * w2 - b2_0 - b0_0
    have ha2_0 : q1_a2 a0 b0 0 w2 = a2_0 := by simp only [q1_a2, dH_dS, a2_0]; ring
    have ha0_0 : q1_a0 ξS0 ξQ0 0 w2 = a0_0 := by simp only [q1_a0, dH_dS, a0_0]; ring
    have ha1_0 : q1_a1 a0 b0 ξS0 ξQ0 0 w2 = a1_0 := by simp only [q1_a1, dH_dS, a1_0, a2_0, a0_0]; ring
    have hb2_0 : q2_b2 a0 b0 0 w2 = b2_0 := by simp only [q2_b2, dH_dQ, b2_0]; ring
    have hb0_0 : q2_b0 ξS0 ξQ0 0 w2 = b0_0 := by simp only [q2_b0, dH_dQ, b0_0]; ring
    have hb1_0 : q2_b1 a0 b0 ξS0 ξQ0 0 w2 = b1_0 := by simp only [q2_b1, dH_dQ, b1_0, b2_0, b0_0]; ring
    have hraw := (numM_ValLead_of ha_L hb_L hξS_L hξQ_L ha2 ha1 ha0 hb2 hb1 hb0 mi).eq_k (k' := 2) (by omega)
    exact hraw.eq_c (by
      dsimp only [numM]; rw [ha2_0, ha1_0, ha0_0, hb2_0, hb1_0, hb0_0]; rfl)
  -- Helper: `ValLead 2 (A_0U ...) 0` -> `HasValGe 3 (A_0U ...)`!
  have hA0U_3 : HasValGe 3 (A_0U a_s b_s ξS_s ξQ_s U V) :=
    ((A0U_ValLead_of hnumM_L).eq_c (A0U_at_zero a0 b0 ξS0 ξQ0 w2)).hasValGe_succ
  have hA0V_L : ValLead 2 (A_0V a_s b_s ξS_s ξQ_s U V) (A_0V a0 b0 ξS0 ξQ0 0 w2) :=
    (A0V_ValLead_of hnumM_L).eq_c rfl
  have hM0_L : ValLead 1 (A_0U a_s b_s ξS_s ξQ_s U V / U + A_0V a_s b_s ξS_s ξQ_s U V / V)
      (A_0V a0 b0 ξS0 ξQ0 0 w2 / w2) := by
    have hU2 : HasValGe 2 (A_0U a_s b_s ξS_s ξQ_s U V / U) :=
      (hA0U_3.div_of_lead_ne hU_L.val (by rw [hU_L.c0]; exact one_ne_zero)).1.mono (by omega)
    have hV1 : ValLead 1 (A_0V a_s b_s ξS_s ξQ_s U V / V) (A_0V a0 b0 ξS0 ξQ0 0 w2 / w2) :=
      (hA0V_L.div_of_ne hV_L hw2_ne).eq_k (by omega)
    rw [add_comm]; exact hV1.add_high hU2
  have hAY_3 : HasValGe 3 (A_Y a_s b_s ξS_s ξQ_s U V) := by
    unfold A_Y
    have ht1 : HasValGe 3 (-(100 / 243 : LaurentSeries K5) *
        (25 * numM 3 a_s b_s ξS_s ξQ_s U V - 45 * numM 4 a_s b_s ξS_s ξQ_s U V -
         45 * numM 5 a_s b_s ξS_s ξQ_s U V + 81 * numM 6 a_s b_s ξS_s ξQ_s U V)) := by
      have h25 := ((ValLead.of_C (25 : K5)).mul (hnumM_L 3)).eq_k (k' := 2) (by omega)
      have h45a := ((ValLead.of_C (45 : K5)).mul (hnumM_L 4)).eq_k (k' := 2) (by omega)
      have h45b := ((ValLead.of_C (45 : K5)).mul (hnumM_L 5)).eq_k (k' := 2) (by omega)
      have h81 := ((ValLead.of_C (81 : K5)).mul (hnumM_L 6)).eq_k (k' := 2) (by omega)
      simp only [map_ofNat] at h25 h45a h45b h81
      have hcomb : HasValGe 3 (25 * numM 3 a_s b_s ξS_s ξQ_s U V - 45 * numM 4 a_s b_s ξS_s ξQ_s U V -
          45 * numM 5 a_s b_s ξS_s ξQ_s U V + 81 * numM 6 a_s b_s ξS_s ξQ_s U V) :=
        ((((h25.sub h45a).sub h45b).add h81).eq_c (AY_t1_at_zero a0 b0 ξS0 ξQ0 w2)).hasValGe_succ.mono (by omega)
      exact hasValGe_neg_div_nat_mul 100 243 hcomb
    have hm2 (i : Fin 10) : HasValGe 2 (numM i a_s b_s ξS_s ξQ_s U V) := (hnumM_L i).val
    have hnat2 (n : ℕ) {f : LaurentSeries K5} (hf : HasValGe 2 f) : HasValGe 2 ((n : LaurentSeries K5) * f) :=
      ((HasValGe.of_nat n).mul hf).mono (by omega)
    have ht2 : HasValGe 3 (V * (-(907876 / 33949125) * (5 * numM 0 a_s b_s ξS_s ξQ_s U V - 9 * numM 1 a_s b_s ξS_s ξQ_s U V) +
        (2258324 / 33949125) * (5 * numM 1 a_s b_s ξS_s ξQ_s U V - 9 * numM 2 a_s b_s ξS_s ξQ_s U V) +
        (8 / 243) * (5 * numM 3 a_s b_s ξS_s ξQ_s U V - 9 * numM 5 a_s b_s ξS_s ξQ_s U V) -
        (64 / 675) * (5 * numM 4 a_s b_s ξS_s ξQ_s U V - 9 * numM 6 a_s b_s ξS_s ξQ_s U V))) := by
      have hinner : HasValGe 2 (-(907876 / 33949125 : LaurentSeries K5) * (5 * numM 0 a_s b_s ξS_s ξQ_s U V - 9 * numM 1 a_s b_s ξS_s ξQ_s U V) +
          (2258324 / 33949125) * (5 * numM 1 a_s b_s ξS_s ξQ_s U V - 9 * numM 2 a_s b_s ξS_s ξQ_s U V) +
          (8 / 243) * (5 * numM 3 a_s b_s ξS_s ξQ_s U V - 9 * numM 5 a_s b_s ξS_s ξQ_s U V) -
          (64 / 675) * (5 * numM 4 a_s b_s ξS_s ξQ_s U V - 9 * numM 6 a_s b_s ξS_s ξQ_s U V)) := by
        have hp (i j : Fin 10) : HasValGe 2 (5 * numM i a_s b_s ξS_s ξQ_s U V - 9 * numM j a_s b_s ξS_s ξQ_s U V) :=
          (hnat2 5 (hm2 i)).sub (hnat2 9 (hm2 j))
        exact (((hasValGe_neg_div_nat_mul 907876 33949125 (hp 0 1)).add
          (hasValGe_div_nat_mul 2258324 33949125 (hp 1 2))).add
          (hasValGe_div_nat_mul 8 243 (hp 3 5))).sub
          (hasValGe_div_nat_mul 64 675 (hp 4 6))
      exact (hV_L.val.mul hinner).mono (by omega)
    have ht3 : HasValGe 3 (U * V * (-(123236 / 24249375) * (numM 0 a_s b_s ξS_s ξQ_s U V +
        (2790 / 77) * numM 6 a_s b_s ξS_s ξQ_s U V + 28 * numM 8 a_s b_s ξS_s ξQ_s U V -
        (5904 / 77) * numM 9 a_s b_s ξS_s ξQ_s U V) +
        (492944 / 33949125) * (numM 1 a_s b_s ξS_s ξQ_s U V +
        (927 / 77) * numM 6 a_s b_s ξS_s ξQ_s U V + (49 / 5) * numM 8 a_s b_s ξS_s ξQ_s U V -
        (21159 / 770) * numM 9 a_s b_s ξS_s ξQ_s U V))) := by
      have hinner : HasValGe 2 (-(123236 / 24249375 : LaurentSeries K5) * (numM 0 a_s b_s ξS_s ξQ_s U V +
          (2790 / 77) * numM 6 a_s b_s ξS_s ξQ_s U V + 28 * numM 8 a_s b_s ξS_s ξQ_s U V -
          (5904 / 77) * numM 9 a_s b_s ξS_s ξQ_s U V) +
          (492944 / 33949125) * (numM 1 a_s b_s ξS_s ξQ_s U V +
          (927 / 77) * numM 6 a_s b_s ξS_s ξQ_s U V + (49 / 5) * numM 8 a_s b_s ξS_s ξQ_s U V -
          (21159 / 770) * numM 9 a_s b_s ξS_s ξQ_s U V)) :=
        (hasValGe_neg_div_nat_mul 123236 24249375
          ((((hm2 0).add (hasValGe_div_nat_mul 2790 77 (hm2 6))).add (hnat2 28 (hm2 8))).sub
            (hasValGe_div_nat_mul 5904 77 (hm2 9)))).add
        (hasValGe_div_nat_mul 492944 33949125
          ((((hm2 1).add (hasValGe_div_nat_mul 927 77 (hm2 6))).add (hasValGe_div_nat_mul 49 5 (hm2 8))).sub
            (hasValGe_div_nat_mul 21159 770 (hm2 9))))
      exact ((hU_L.val.mul hV_L.val).mul hinner).mono (by omega)
    exact (ht1.add ht2).add ht3
  have hAX_3 : HasValGe 3 (A_X a_s b_s ξS_s ξQ_s U V) := by
    unfold A_X
    have hm2 (i : Fin 10) : HasValGe 2 (numM i a_s b_s ξS_s ξQ_s U V) := (hnumM_L i).val
    have hnat2 (n : ℕ) {f : LaurentSeries K5} (hf : HasValGe 2 f) : HasValGe 2 ((n : LaurentSeries K5) * f) :=
      ((HasValGe.of_nat n).mul hf).mono (by omega)
    have hp (i j : Fin 10) : HasValGe 2 (5 * numM i a_s b_s ξS_s ξQ_s U V - 9 * numM j a_s b_s ξS_s ξQ_s U V) :=
      (hnat2 5 (hm2 i)).sub (hnat2 9 (hm2 j))
    have hinner : HasValGe 2 (-(8 / 405 : LaurentSeries K5) * (5 * numM 3 a_s b_s ξS_s ξQ_s U V - 9 * numM 4 a_s b_s ξS_s ξQ_s U V) -
        (476 / 7185) * (5 * numM 7 a_s b_s ξS_s ξQ_s U V - 9 * numM 8 a_s b_s ξS_s ξQ_s U V) +
        (6916 / 35925) * (5 * numM 8 a_s b_s ξS_s ξQ_s U V - 9 * numM 9 a_s b_s ξS_s ξQ_s U V)) :=
      ((hasValGe_neg_div_nat_mul 8 405 (hp 3 4)).sub (hasValGe_div_nat_mul 476 7185 (hp 7 8))).add
        (hasValGe_div_nat_mul 6916 35925 (hp 8 9))
    exact (hU_L.val.mul hinner).mono (by omega)
  exact ⟨hM0_L, hAY_3, hAX_3⟩


private lemma br1_0_q1_bound {a_s b_s U V : LaurentSeries K5} {w2 a0 b0 : K5}
    (ha_L : ValLead 0 a_s a0) (hb_L : ValLead 0 b_s b0)
    (hU_L : ValLead 1 U 1) (hV_L : ValLead 1 V w2)
    (hw2_eq : S_K * (5 * S_K - 9 * Q_K) ^ 2 * w2 = -T_K * (5 * T_K - 9) ^ 2)
    (hlin0 : (-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * (w2 * a0) +
      ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) * (w2 * b0) + k5Params.c0_V0 = 0) :
    HasValGe 1 (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V) ∧
    HasValGe 1 (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U) ∧
    HasValGe 2
      (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) *
        A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V *
        (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V) +
      H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) *
        B1_of (HahnSeries.C T_K) U V *
        (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U) +
      (cA1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) a_s b_s U V / v_of V) *
        EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V) ∧
    HasValGe 0 (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) := by
  have hA := fiveS_sub_9Q_ne; have hC := fiveT_sub_9_ne
  have hA1_1 : HasValGe 1 (A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V) := by
    unfold A1_of
    have h0 : HasValGe 0 (25 * HahnSeries.C S_K * (5 * HahnSeries.C S_K - 9 * HahnSeries.C Q_K) ^ 2 -
        4 * (HahnSeries.C S_K - 3 * HahnSeries.C Q_K) ^ 3 * U) := by
      have ha : HasValGe 0 (25 * HahnSeries.C S_K * (5 * HahnSeries.C S_K - 9 * HahnSeries.C Q_K) ^ 2) :=
        (((HasValGe.of_nat 25).mul (HasValGe.of_C S_K)).mul
          ((((HasValGe.of_nat 5).mul (HasValGe.of_C S_K)).sub ((HasValGe.of_nat 9).mul (HasValGe.of_C Q_K))).pow 2)).mono (by omega)
      have hb : HasValGe 0 (4 * (HahnSeries.C S_K - 3 * HahnSeries.C Q_K) ^ 3 * U) :=
        (((HasValGe.of_nat 4).mul (((HasValGe.of_C S_K).sub ((HasValGe.of_nat 3).mul (HasValGe.of_C Q_K) |>.mono (k2 := 0) (by omega))).pow 3)).mul
          (hU_L.val.mono (k2 := 0) (by omega))).mono (by omega)
      exact ha.sub hb
    rw [show (1 / 27 : LaurentSeries K5) = HahnSeries.C (1 / 27 : K5) by simp only [map_div₀, map_ofNat, map_one]]
    exact (((HasValGe.of_C _).mul hV_L.val).mul h0).mono (by omega)
  have hB1_1 : HasValGe 1 (B1_of (HahnSeries.C T_K) U V) := by
    unfold B1_of
    have h0 : HasValGe 0 (25 * HahnSeries.C T_K * (5 * HahnSeries.C T_K - 9) ^ 2 -
        4 * (HahnSeries.C T_K - 3) ^ 3 * V) := by
      have ha : HasValGe 0 (25 * HahnSeries.C T_K * (5 * HahnSeries.C T_K - 9) ^ 2) :=
        (((HasValGe.of_nat 25).mul (HasValGe.of_C T_K)).mul
          ((((HasValGe.of_nat 5).mul (HasValGe.of_C T_K)).sub (HasValGe.of_nat 9)).pow 2)).mono (by omega)
      have hb : HasValGe 0 (4 * (HahnSeries.C T_K - 3) ^ 3 * V) :=
        (((HasValGe.of_nat 4).mul (((HasValGe.of_C T_K).sub (HasValGe.of_nat 3)).pow 3)).mul
          (hV_L.val.mono (k2 := 0) (by omega))).mono (by omega)
      exact ha.sub hb
    rw [show (1 / 27 : LaurentSeries K5) = HahnSeries.C (1 / 27 : K5) by simp only [map_div₀, map_ofNat, map_one]]
    exact (((HasValGe.of_C _).mul hU_L.val).mul h0).mono (by omega)
  have hH0_0 : HasValGe 0 (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) := by
    have h : H0_of (HahnSeries.C S_K : LaurentSeries K5) (HahnSeries.C Q_K) (HahnSeries.C T_K) =
        HahnSeries.C (H0_of S_K Q_K T_K) := by
      simp only [H0_of, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]
    rw [h]; exact HasValGe.of_C _
  have hcA1_1 : HasValGe 1 (cA1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) a_s b_s U V) := by
    have hdA1 (k : Fin 3) : HasValGe 1 (dA1_fn k (HahnSeries.C S_K) (HahnSeries.C Q_K) U V) := by
      fin_cases k
      · unfold dA1_fn
        rw [show (1 / 27 : LaurentSeries K5) = HahnSeries.C (1 / 27 : K5) by simp only [map_div₀, map_ofNat, map_one]]
        have h0 : HasValGe 0 (25 * (5 * HahnSeries.C S_K - 9 * HahnSeries.C Q_K) *
            (15 * HahnSeries.C S_K - 9 * HahnSeries.C Q_K) - 12 * (HahnSeries.C S_K - 3 * HahnSeries.C Q_K) ^ 2 * U) := by
          have ha : HasValGe 0 _ := (((HasValGe.of_nat 25).mul (((HasValGe.of_nat 5).mul (HasValGe.of_C S_K)).sub
            ((HasValGe.of_nat 9).mul (HasValGe.of_C Q_K)))).mul
            (((HasValGe.of_nat 15).mul (HasValGe.of_C S_K)).sub ((HasValGe.of_nat 9).mul (HasValGe.of_C Q_K)))).mono (by omega)
          have hb : HasValGe 0 _ := (((HasValGe.of_nat 12).mul (((HasValGe.of_C S_K).sub
            ((HasValGe.of_nat 3).mul (HasValGe.of_C Q_K) |>.mono (k2 := 0) (by omega))).pow 2)).mul
            (hU_L.val.mono (k2 := 0) (by omega))).mono (by omega)
          exact ha.sub hb
        exact (((HasValGe.of_C _).mul hV_L.val).mul h0).mono (by omega)
      · unfold dA1_fn
        rw [show (1 / 27 : LaurentSeries K5) = HahnSeries.C (1 / 27 : K5) by simp only [map_div₀, map_ofNat, map_one]]
        have h0 : HasValGe 0 (-(450 : LaurentSeries K5) * HahnSeries.C S_K * (5 * HahnSeries.C S_K - 9 * HahnSeries.C Q_K) +
            36 * (HahnSeries.C S_K - 3 * HahnSeries.C Q_K) ^ 2 * U) := by
          have ha : HasValGe 0 _ := ((((HasValGe.of_nat 450).neg).mul (HasValGe.of_C S_K)).mul
            (((HasValGe.of_nat 5).mul (HasValGe.of_C S_K)).sub ((HasValGe.of_nat 9).mul (HasValGe.of_C Q_K)))).mono (by omega)
          have hb : HasValGe 0 _ := (((HasValGe.of_nat 36).mul (((HasValGe.of_C S_K).sub
            ((HasValGe.of_nat 3).mul (HasValGe.of_C Q_K) |>.mono (k2 := 0) (by omega))).pow 2)).mul
            (hU_L.val.mono (k2 := 0) (by omega))).mono (by omega)
          exact ha.add hb
        exact (((HasValGe.of_C _).mul hV_L.val).mul h0).mono (by omega)
      · exact HasValGe.zero 1
    have hdH0_0 (k : Fin 3) : HasValGe 0 (dH0_fn k (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)) := by
      have h : dH0_fn k (HahnSeries.C S_K : LaurentSeries K5) (HahnSeries.C Q_K) (HahnSeries.C T_K) =
          HahnSeries.C (dH0_fn k S_K Q_K T_K) := by
        fin_cases k <;> simp only [dH0_fn, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]
      rw [h]; exact HasValGe.of_C _
    unfold cA1_of
    exact ((((hH0_0.mul (hdA1 0)).sub (hA1_1.mul (hdH0_0 0) |>.mono (by omega))).mul ha_L.val |>.mono (by omega)).add
      (((hH0_0.mul (hdA1 1)).sub (hA1_1.mul (hdH0_0 1) |>.mono (by omega))).mul hb_L.val |>.mono (by omega))).add
      (((hH0_0.mul (hdA1 2)).sub (hA1_1.mul (hdH0_0 2) |>.mono (by omega))).mono (by omega))
  have hU0 : ValLead 0 U 0 := ValLead.of_hasValGe_succ hU_L.val
  have hV0 : ValLead 0 V 0 := ValLead.of_hasValGe_succ hV_L.val
  have hu_L : ValLead 0 (u_of U) (-(1 / 9 : K5)) := by
    unfold u_of
    have h9 : (9 : K5) ≠ 0 := by exact_mod_cast (by decide : (9 : ℕ) ≠ 0)
    exact ((hU0.sub (ValLead.of_C 1)).div_of_ne (ValLead.of_nat 9) h9).eq_k (by omega) |>.eq_c (by ring)
  have hv_L : ValLead 0 (v_of V) (-(1 / 9 : K5)) := by
    unfold v_of
    have h9 : (9 : K5) ≠ 0 := by exact_mod_cast (by decide : (9 : ℕ) ≠ 0)
    exact ((hV0.sub (ValLead.of_C 1)).div_of_ne (ValLead.of_nat 9) h9).eq_k (by omega) |>.eq_c (by ring)
  have hneg19_ne : (-(1 / 9 : K5)) ≠ 0 := neg_ne_zero.mpr (div_ne_zero one_ne_zero (by exact_mod_cast (by decide : (9 : ℕ) ≠ 0)))
  have hlinUV0 {f0 f1 f2 f3 : K5} :
      ValLead 0 (HahnSeries.C f0 + HahnSeries.C f1 * V + HahnSeries.C f2 * U + HahnSeries.C f3 * U * V) f0 := by
    have hhi : HasValGe 1 (HahnSeries.C f1 * V + HahnSeries.C f2 * U + HahnSeries.C f3 * U * V) :=
      ((((HasValGe.of_C f1).mul hV_L.val).mono (by omega)).add
        (((HasValGe.of_C f2).mul hU_L.val).mono (by omega))).add
        ((((HasValGe.of_C f3).mul hU_L.val).mul hV_L.val).mono (by omega))
    have hre : HahnSeries.C f0 + HahnSeries.C f1 * V + HahnSeries.C f2 * U + HahnSeries.C f3 * U * V =
        HahnSeries.C f0 + (HahnSeries.C f1 * V + HahnSeries.C f2 * U + HahnSeries.C f3 * U * V) := by ring
    rw [hre]; exact (ValLead.of_C f0).add_high hhi
  have hEB_1 : HasValGe 1 (EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V) := by
    have hbi := EB_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V
    have h00 := map_EB_of (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 0 0
    have h01 := map_EB_of (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 0 1
    have h10 := map_EB_of (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 1 0
    have h11 := map_EB_of (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 1 1
    simp only [map_zero, map_one] at h00 h01 h10 h11
    rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
    exact (hlinUV0.eq_c (EB_of_zero_zero S_K Q_K T_K x_K y_K)).hasValGe_succ
  have hQY_0 (i : Fin 3) : ValLead 0 (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K)
      (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V i)
      (QY_num S_K Q_K T_K x_K y_K 0 0 i) := by
    have hbi := QY_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V i
    have h00 := map_QY_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 0 0 i
    have h01 := map_QY_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 0 1 i
    have h10 := map_QY_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 1 0 i
    have h11 := map_QY_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 1 1 i
    simp only [map_zero, map_one] at h00 h01 h10 h11
    rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
    exact hlinUV0
  have hQX_0 (i : Fin 3) : ValLead 0 (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K)
      (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V i)
      (QX_num S_K Q_K T_K x_K y_K 0 0 i) := by
    have hbi := QX_bilinear_UV (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V i
    have h00 := map_QX_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 0 0 i
    have h01 := map_QX_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 0 1 i
    have h10 := map_QX_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 1 0 i
    have h11 := map_QX_num (HahnSeries.C : K5 →+* LaurentSeries K5) S_K Q_K T_K x_K y_K 1 1 i
    simp only [map_zero, map_one] at h00 h01 h10 h11
    rw [hbi, h00, h01, h10, h11, ← map_sub, ← map_sub, ← map_sub, ← map_sub, ← map_add]
    exact hlinUV0
  have hqY_1 : HasValGe 1 (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V) := by
    have hdot : ValLead 0 (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s)
        (dot_ab (QY_num S_K Q_K T_K x_K y_K 0 0) a0 b0) := by
      unfold dot_ab
      exact (((hQY_0 0).mul ha_L).eq_k (by omega)).add (((hQY_0 1).mul hb_L).eq_k (by omega)) |>.add (hQY_0 2)
    have hzero : dot_ab (QY_num S_K Q_K T_K x_K y_K 0 0) a0 b0 = 0 := by
      apply mul_left_cancel₀ (mul_ne_zero hA hC)
      rw [mul_zero]
      have hstep : (5 * S_K - 9 * Q_K) * (5 * T_K - 9) *
          dot_ab (QY_num S_K Q_K T_K x_K y_K 0 0) a0 b0 =
          4 * y_K * (-25 * S_K + 45 * Q_K + 27 * x_K) * S_K ^ 2 * T_K ^ 2 * DY2_of T_K y_K *
            (S_K * (5 * S_K - 9 * Q_K) ^ 2 *
              ((-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * (w2 * a0) +
               ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) * (w2 * b0) + k5Params.c0_V0)) := by
        have hlin' : S_K * (5 * S_K - 9 * Q_K) ^ 2 *
            ((-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * (w2 * a0) +
             ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) * (w2 * b0) + k5Params.c0_V0) =
            (-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * a0 * (S_K * (5 * S_K - 9 * Q_K) ^ 2 * w2) +
            ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) * b0 * (S_K * (5 * S_K - 9 * Q_K) ^ 2 * w2) +
            S_K * (5 * S_K - 9 * Q_K) ^ 2 * k5Params.c0_V0 := by ring
        rw [hlin', hw2_eq]
        have hc0 : k5Params.c0_V0 = -(25 / 81 : K5) * (5 * T_K - 9) * (5 * T_K - 3) := by
          simp only [CoverParams.c0_V0, CoverParams.inv81, k5Params_inv3, k5Params_T]; ring
        rw [hc0]
        exact QY_num_00_factor S_K Q_K T_K x_K y_K a0 b0
      rw [hstep, hlin0, mul_zero, mul_zero]
    exact (((hdot.eq_c hzero).div_of_ne hv_L hneg19_ne).eq_k (k' := 0) (by omega) |>.eq_c (zero_div _)).hasValGe_succ
  have hqX_1 : HasValGe 1 (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
      (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U) := by
    have hdot : ValLead 0 (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s)
        (dot_ab (QX_num S_K Q_K T_K x_K y_K 0 0) a0 b0) := by
      unfold dot_ab
      exact (((hQX_0 0).mul ha_L).eq_k (by omega)).add (((hQX_0 1).mul hb_L).eq_k (by omega)) |>.add (hQX_0 2)
    have hzero : dot_ab (QX_num S_K Q_K T_K x_K y_K 0 0) a0 b0 = 0 := by
      apply mul_left_cancel₀ (mul_ne_zero hA hC)
      rw [mul_zero]
      have hstep : (5 * S_K - 9 * Q_K) * (5 * T_K - 9) *
          dot_ab (QX_num S_K Q_K T_K x_K y_K 0 0) a0 b0 =
          4 * x_K * (-25 * T_K + 45 + 27 * y_K) * S_K ^ 2 * T_K ^ 2 * DX2_of S_K Q_K x_K *
            (S_K * (5 * S_K - 9 * Q_K) ^ 2 *
              ((-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * (w2 * a0) +
               ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) * (w2 * b0) + k5Params.c0_V0)) := by
        have hlin' : S_K * (5 * S_K - 9 * Q_K) ^ 2 *
            ((-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * (w2 * a0) +
             ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) * (w2 * b0) + k5Params.c0_V0) =
            (-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * a0 * (S_K * (5 * S_K - 9 * Q_K) ^ 2 * w2) +
            ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) * b0 * (S_K * (5 * S_K - 9 * Q_K) ^ 2 * w2) +
            S_K * (5 * S_K - 9 * Q_K) ^ 2 * k5Params.c0_V0 := by ring
        rw [hlin', hw2_eq]
        have hc0 : k5Params.c0_V0 = -(25 / 81 : K5) * (5 * T_K - 9) * (5 * T_K - 3) := by
          simp only [CoverParams.c0_V0, CoverParams.inv81, k5Params_inv3, k5Params_T]; ring
        rw [hc0]
        exact QX_num_00_factor S_K Q_K T_K x_K y_K a0 b0
      rw [hstep, hlin0, mul_zero, mul_zero]
    exact (((hdot.eq_c hzero).div_of_ne hu_L hneg19_ne).eq_k (k' := 0) (by omega) |>.eq_c (zero_div _)).hasValGe_succ
  have hq1_2 : HasValGe 2
      (H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) *
        A1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) U V *
        (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V) +
      H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) *
        B1_of (HahnSeries.C T_K) U V *
        (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U) +
      (cA1_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) a_s b_s U V / v_of V) *
        EB_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) (HahnSeries.C x_K) (HahnSeries.C y_K) U V) := by
    have ht1 : HasValGe 2 _ := ((hH0_0.mul hA1_1).mul hqY_1).mono (by omega)
    have ht2 : HasValGe 2 _ := ((hH0_0.mul hB1_1).mul hqX_1).mono (by omega)
    have ht3 : HasValGe 2 _ := ((hcA1_1.div_of_lead_ne hv_L.val (hv_L.c0.symm ▸ hneg19_ne)).1.mul hEB_1).mono (by omega)
    exact (ht1.add ht2).add ht3
  exact ⟨hqY_1, hqX_1, hq1_2, hH0_0⟩


private lemma br1_0_g_scaled_core {a_s b_s U V : LaurentSeries K5} {w2 a0 b0 : K5}
    (hw2_ne : w2 ≠ 0) (ha_L : ValLead 0 a_s a0) (hb_L : ValLead 0 b_s b0)
    (hU_L : ValLead 1 U 1) (hV_L : ValLead 1 V w2)
    (hw2_eq : S_K * (5 * S_K - 9 * Q_K) ^ 2 * w2 = -T_K * (5 * T_K - 9) ^ 2)
    (hlin0 : (-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * (w2 * a0) +
      ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) * (w2 * b0) + k5Params.c0_V0 = 0) :
    HasValGe 3 (P18_of (R := LaurentSeries K5) (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K) a_s b_s U V) ∧
      (a0 = S_K / T_K → 5 * a0 - 9 * b0 = 5 * (Q_K - b0 * T_K) →
        (P18_of (R := LaurentSeries K5) (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) a_s b_s U V).coeff 3 = 0) := by
  have hT := T_K_ne_zero
  obtain ⟨hM0_L, hAY_3, hAX_3⟩ := br1_0_numM_bounds hw2_ne ha_L hb_L hU_L hV_L
  obtain ⟨hqY_1, hqX_1, hq1_2, hH0_0⟩ := br1_0_q1_bound ha_L hb_L hU_L hV_L hw2_eq hlin0
  have hrest_4 : HasValGe 4
      ((A_Y a_s b_s (HahnSeries.C S_K - a_s * HahnSeries.C T_K) (HahnSeries.C Q_K - b_s * HahnSeries.C T_K) U V *
        (dot_ab (QY_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / v_of V) +
        A_X a_s b_s (HahnSeries.C S_K - a_s * HahnSeries.C T_K) (HahnSeries.C Q_K - b_s * HahnSeries.C T_K) U V *
        (dot_ab (QX_num (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
          (HahnSeries.C x_K) (HahnSeries.C y_K) U V) a_s b_s / u_of U)) *
      H0_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K) ^ 2) :=
    (((hAY_3.mul hqY_1).mono (k2 := 4) (by omega)).add ((hAX_3.mul hqX_1).mono (k2 := 4) (by omega))).mul
      (hH0_0.pow 2) |>.mono (by omega)
  rw [P18_of_HahnC_eq]
  refine ⟨((hM0_L.val.mul hq1_2).mono (by omega)).add (hrest_4.mono (by omega)), ?_⟩
  intro ha0_eq hrel
  have hξS0 : S_K - a0 * T_K = 0 := by rw [ha0_eq, div_mul_cancel₀ _ hT, sub_self]
  have hA0V_0 : A_0V a0 b0 (S_K - a0 * T_K) (Q_K - b0 * T_K) 0 w2 = 0 := by
    rw [hξS0]; exact A0V_at_zero_xiS0 a0 b0 (Q_K - b0 * T_K) w2 hrel
  have hM0_2 : HasValGe 2
      (A_0U a_s b_s (HahnSeries.C S_K - a_s * HahnSeries.C T_K) (HahnSeries.C Q_K - b_s * HahnSeries.C T_K) U V / U +
       A_0V a_s b_s (HahnSeries.C S_K - a_s * HahnSeries.C T_K) (HahnSeries.C Q_K - b_s * HahnSeries.C T_K) U V / V) :=
    (hM0_L.eq_c (by rw [hA0V_0, zero_div])).hasValGe_succ
  have hg_4 : HasValGe 4 _ :=
    ((hM0_2.mul hq1_2).mono (k2 := 4) (by omega)).add hrest_4
  exact hg_4 3 (by omega)

private lemma br1_0_g_scaled {W1s U V ca cb c0W : LaurentSeries K5} {w2 z1 : K5}
    (hw2_ne : w2 ≠ 0) (hcb0_ne : (50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K) ≠ 0)
    (hw2_L : ValLead 2 W1s w2) (hU_L : ValLead 1 U 1) (hV_L : ValLead 1 V w2)
    (hca_L : ValLead 0 ca (-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)))
    (hcb_L : ValLead 0 cb ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)))
    (hc0W_L : ValLead 2 c0W k5Params.c0_V0)
    (hz1_def : z1 = w2 * S_K / T_K)
    (hw2_eq : S_K * (5 * S_K - 9 * Q_K) ^ 2 * w2 = -T_K * (5 * T_K - 9) ^ 2)
    (hz1_mul : (5 * S_K - 9 * Q_K) ^ 2 * z1 = -(5 * T_K - 9) ^ 2) :
    let g : LaurentSeries K5 → LaurentSeries K5 := fun z =>
      P18_of (R := LaurentSeries K5) (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K)
        (z / W1s) (-(ca * z + c0W) / (W1s * cb)) U V
    ∀ c : K5, HasValGe 3 (g (HahnSeries.single 2 c)) ∧
      (c = z1 → (g (HahnSeries.single 2 c)).coeff 3 = 0) := by
  have hS := S_K_ne_zero; have hT := T_K_ne_zero
  have hA := fiveS_sub_9Q_ne; have hC := fiveT_sub_9_ne
  intro g c
  set z : LaurentSeries K5 := HahnSeries.single 2 c
  let a0 : K5 := c / w2
  let b0 : K5 := -((-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * c + k5Params.c0_V0) /
    (w2 * ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)))
  have hz_L : ValLead 2 z c := ValLead.of_single 2 c
  have ha_L : ValLead 0 (z / W1s) a0 :=
    (hz_L.div_of_ne hw2_L hw2_ne).eq_k (by omega)
  have hb_L : ValLead 0 (-(ca * z + c0W) / (W1s * cb)) b0 := by
    have hnum : ValLead 2 (-(ca * z + c0W))
        (-((-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * c + k5Params.c0_V0)) :=
      (((hca_L.mul hz_L).eq_k (by omega)).add hc0W_L).neg
    have hden : ValLead 2 (W1s * cb) (w2 * ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K))) :=
      (hw2_L.mul hcb_L).eq_k (by omega)
    exact (hnum.div_of_ne hden (mul_ne_zero hw2_ne hcb0_ne)).eq_k (by omega)
  have hlin0 : (-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * (w2 * a0) +
      ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) * (w2 * b0) + k5Params.c0_V0 = 0 := by
    dsimp only [a0, b0]; field_simp [hw2_ne, hcb0_ne]; ring
  obtain ⟨hge, hzero⟩ := br1_0_g_scaled_core hw2_ne ha_L hb_L hU_L hV_L hw2_eq hlin0
  refine ⟨hge, fun hcz1 => ?_⟩
  have ha0_eq : a0 = S_K / T_K := by dsimp only [a0]; rw [hcz1, hz1_def]; field_simp [hw2_ne, hT]
  have hrel : 5 * a0 - 9 * b0 = 5 * (Q_K - b0 * T_K) := by
    have hwa : w2 * a0 = z1 := by dsimp only [a0]; rw [hcz1]; field_simp [hw2_ne]
    have h50_27 : (50 / 27 : K5) ≠ 0 := div_ne_zero
      (by exact_mod_cast (by decide : (50 : ℕ) ≠ 0))
      (by exact_mod_cast (by decide : (27 : ℕ) ≠ 0))
    have hTb : T_K * (5 * T_K - 9) * b0 = 5 * (Q_K * T_K - S_K) := by
      apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero h50_27 hA) hC)
      have h1 : (5 * S_K - 9 * Q_K) ^ 2 *
          ((-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * z1 +
           ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) * (w2 * b0) + k5Params.c0_V0) = 0 := by
        rw [← hwa, hlin0, mul_zero]
      have h2 : (5 * S_K - 9 * Q_K) ^ 2 *
          ((-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * z1 +
           ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) * (w2 * b0) + k5Params.c0_V0) =
          (-(25 / 81 : K5) * (5 * S_K - 9 * Q_K) * (5 * S_K - 3 * Q_K)) * ((5 * S_K - 9 * Q_K) ^ 2 * z1) +
          ((50 / 27 : K5) * (5 * S_K - 9 * Q_K)) * (S_K * (5 * S_K - 9 * Q_K) ^ 2 * w2) * b0 +
          (5 * S_K - 9 * Q_K) ^ 2 * k5Params.c0_V0 := by ring
      rw [h2, hz1_mul, hw2_eq] at h1
      simp only [CoverParams.c0_V0, CoverParams.inv81, k5Params_inv3, k5Params_T] at h1
      linear_combination -h1
    apply mul_left_cancel₀ hT
    have haT : T_K * a0 = S_K := by rw [ha0_eq, mul_div_cancel₀ _ hT]
    linear_combination hTb + 5 * haT
  exact hzero ha0_eq hrel


end SymmetricSexticResidual.LocalResidueU0

open scoped LaurentSeries in
theorem solution
    {W1s U V ca cb c0W : LaurentSeries SymmetricSexticResidual.K5Field.K5}
    {w2 z1 : SymmetricSexticResidual.K5Field.K5}
    (hw2_ne : w2 ≠ 0)
    (hcb0_ne : (50 / 27 : SymmetricSexticResidual.K5Field.K5) *
      SymmetricSexticResidual.K5Field.S_K *
      (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ≠ 0)
    (hw2_L : QuadraticCovers.ValLead 2 W1s w2)
    (hU_L : QuadraticCovers.ValLead 1 U 1)
    (hV_L : QuadraticCovers.ValLead 1 V w2)
    (hca_L : QuadraticCovers.ValLead 0 ca
      (-(25 / 81 : SymmetricSexticResidual.K5Field.K5) *
        (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) *
        (5 * SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K)))
    (hcb_L : QuadraticCovers.ValLead 0 cb
      ((50 / 27 : SymmetricSexticResidual.K5Field.K5) *
        SymmetricSexticResidual.K5Field.S_K *
        (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)))
    (hc0W_L : QuadraticCovers.ValLead 2 c0W SymmetricSexticResidual.CoverAlgebra.k5Params.c0_V0)
    (hz1_def : z1 = w2 * SymmetricSexticResidual.K5Field.S_K / SymmetricSexticResidual.K5Field.T_K)
    (hw2_eq : SymmetricSexticResidual.K5Field.S_K *
      (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 2 * w2 =
      -SymmetricSexticResidual.K5Field.T_K * (5 * SymmetricSexticResidual.K5Field.T_K - 9) ^ 2)
    (hz1_mul : (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 2 * z1 =
      -(5 * SymmetricSexticResidual.K5Field.T_K - 9) ^ 2) :
    let g : LaurentSeries SymmetricSexticResidual.K5Field.K5 →
        LaurentSeries SymmetricSexticResidual.K5Field.K5 := fun z =>
      SymmetricSexticResidual.SheetCalculus.P18_of
        (R := LaurentSeries SymmetricSexticResidual.K5Field.K5)
        (HahnSeries.C SymmetricSexticResidual.K5Field.S_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.Q_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.T_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.x_K)
        (HahnSeries.C SymmetricSexticResidual.K5Field.y_K)
        (z / W1s) (-(ca * z + c0W) / (W1s * cb)) U V
    ∀ c : SymmetricSexticResidual.K5Field.K5,
      QuadraticCovers.HasValGe 3 (g (HahnSeries.single 2 c)) ∧
      (c = z1 → (g (HahnSeries.single 2 c)).coeff 3 = 0) :=
  SymmetricSexticResidual.LocalResidueU0.br1_0_g_scaled hw2_ne hcb0_ne hw2_L hU_L hV_L
    hca_L hcb_L hc0W_L hz1_def hw2_eq hz1_mul
