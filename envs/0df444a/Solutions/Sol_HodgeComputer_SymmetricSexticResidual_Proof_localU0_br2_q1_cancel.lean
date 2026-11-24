-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localU0_br2_q1_cancel
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T14:21:00.892712+00:00
-- url     : https://prove2.me/submissions/6acd07b8-8e82-4090-b6fd-ecf4360758ae

import Definitions.Def_HodgeComputerSSR_CoverParams
import Definitions.Def_HodgeComputerSSR_U0Biv
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localU0_biv_identity

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueU0
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra
  SymmetricSexticResidual.LocalResidueData SymmetricSexticResidual.VerticalIdentity
  QuadraticCovers
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions

private lemma U0_biv_identity : evalBivK5 LHS_U0_biv = evalBivK5 RHS_U0_biv :=
  HodgeComputer.SymmetricSexticResidual.Proof.localU0_biv_identity

private lemma evalBivK5_DX2 : evalBivK5 DX2_biv = DX2_of S_K Q_K x_K := by
  simp only [evalBivK5, DX2_biv, denote, ringEval, eS, eQ, vK5, DX2_of, u3_of,
    Int.cast_neg, Int.cast_ofNat]; ring

private lemma evalBivK5_DY2 : evalBivK5 DY2_biv = DY2_of T_K y_K := by
  simp only [evalBivK5, DY2_biv, denote, ringEval, eT, vK5, DY2_of, v3_of,
    Int.cast_neg, Int.cast_ofNat]; ring

private lemma evalBivK5_W2 : evalBivK5 W2_biv = W2_of S_K Q_K T_K x_K y_K := by
  rw [W2_biv, evalBivK5_bivMul, evalBivK5_scale, evalBivK5_DX2, evalBivK5_DY2]
  simp only [ringEval, eS, eT, vK5, W2_of, pow_zero, mul_one]

private lemma ringEval_dH0_7 (k : Fin 3) : ringEval vK5 (dH0_7_e k) = 7 * dH0_fn k S_K Q_K T_K := by
  fin_cases k <;> (simp only [dH0_7_e, dH0_fn, ringEval, eS, eQ, eT, vK5, Int.cast_neg, Int.cast_ofNat]; ring)

private lemma evalBivK5_dF5_7 (k : Fin 5) : evalBivK5 (dF5_7_biv k) = 7 * dF5_fn k S_K Q_K T_K x_K y_K := by
  fin_cases k <;>
    (simp only [evalBivK5, dF5_7_biv, dF5_fn, denote, ringEval, eS, eQ, eT, vK5,
      Int.cast_neg, Int.cast_ofNat, dH0_fn, dH0_7_e]; ring)

private lemma evalBivK5_dDX2 (k : Fin 5) : evalBivK5 (dDX2_biv k) = dDX2_fn k S_K Q_K x_K := by
  fin_cases k <;>
    simp only [evalBivK5, dDX2_biv, dDX2_fn,
       denote, ringEval, eS, eQ, vK5, u3_of, Int.cast_neg, Int.cast_ofNat]
  all_goals ring

private lemma evalBivK5_br_V0_243 (k : Fin 5) :
    evalBivK5 (br_V0_243_biv k) = 243 * (br_fn k S_K Q_K T_K x_K y_K 0 1 - br_fn k S_K Q_K T_K x_K y_K 0 0) := by
  fin_cases k <;>
    (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, evalBivK5, br_V0_243_biv, br_fn,
      LY_V1_27_biv, LY_V1_9_biv, eA5, e5S3Q, 
      scale_denote, denote, ringEval, eS, eQ, eT, vK5,
      LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of,
      Int.cast_neg, Int.cast_ofNat]; ring)

private lemma evalBivK5_om_V0_81 (p q : Fin 5) :
    evalBivK5 (om_V0_81_biv p q) = 81 * (om_fn p q S_K Q_K T_K x_K y_K 0 1 - om_fn p q S_K Q_K T_K x_K y_K 0 0) := by
  fin_cases p <;> fin_cases q <;>
    (rw [om_V0_81_biv, evalBivK5_bivSub]; simp only [evalBivK5_scale];
     simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, omX0_e, omY_V1_biv, om_fn,
       evalBivK5, denote, ringEval, eS, eQ, eT, vK5, Int.cast_neg, Int.cast_ofNat]; ring)

private lemma evalBivK5_QY_V0_1701 (i : Fin 3) :
    evalBivK5 (QY_V0_1701_biv i) =
      1701 * (QY_num S_K Q_K T_K x_K y_K 0 1 i - QY_num S_K Q_K T_K x_K y_K 0 0 i) := by
  have hQY_lin (V : K5) :
      QY_num S_K Q_K T_K x_K y_K 0 V i - QY_num S_K Q_K T_K x_K y_K 0 0 i =
      DY2_of T_K y_K * (DX2_of S_K Q_K x_K *
        F_contract S_K Q_K T_K x_K y_K (fun p q => S_K * T_K *
          (om_fn p q S_K Q_K T_K x_K y_K 0 V - om_fn p q S_K Q_K T_K x_K y_K 0 0)) i -
        F_contract S_K Q_K T_K x_K y_K (fun p q => S_K * T_K *
          (dDX2_fn p S_K Q_K x_K * (br_fn q S_K Q_K T_K x_K y_K 0 V - br_fn q S_K Q_K T_K x_K y_K 0 0) -
           dDX2_fn q S_K Q_K x_K * (br_fn p S_K Q_K T_K x_K y_K 0 V - br_fn p S_K Q_K T_K x_K y_K 0 0))) i) := by
    simp only [QY_num, Omega_F, dDX2_F, F_contract]; ring
  rw [hQY_lin 1, QY_V0_1701_biv, evalBivK5_bivMul, evalBivK5_DY2, evalBivK5_bivSub,
    evalBivK5_bivMul, evalBivK5_DX2]
  fin_cases i <;> (
    dsimp only [F_contract_7_biv, F_contract]
    simp only [evalBivK5_bivAdd, evalBivK5_bivMul, evalBivK5_scale,
      evalBivK5_bivSub, evalBivK5_dF5_7, evalBivK5_om_V0_81, evalBivK5_dDX2, evalBivK5_br_V0_243,
      ringEval, eS, eT, vK5, Int.cast_ofNat, pow_zero, mul_one]
    ring)

private lemma evalBivK5_EB_V0 :
    S_K * (5 * S_K - 9 * Q_K) * evalBivK5 EB_V0_9_div_SA5_biv = 9 * EB_of S_K Q_K T_K x_K y_K 0 1 := by
  rw [EB_V0_9_div_SA5_biv, evalBivK5_scale, evalBivK5_W2]
  simp only [ringEval, eS, eT, vK5, Int.cast_neg, Int.cast_ofNat, pow_one, pow_zero, mul_one,
    EB_of, dF5_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of]
  ring


private lemma br2_0_q1_biv_eval (w0 : K5) :
    let A := 5 * S_K - 9 * Q_K
    let B := T_K - 3
    let q1_c := fun k : Fin 3 =>
      9 * w0 * (H0_of S_K Q_K T_K * A1_of S_K Q_K 0 1 *
          (QY_num S_K Q_K T_K x_K y_K 0 1 k - QY_num S_K Q_K T_K x_K y_K 0 0 k) +
        (H0_of S_K Q_K T_K * dA1_fn k S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn k S_K Q_K T_K) *
          EB_of S_K Q_K T_K x_K y_K 0 1)
    w0 * S_K * A ^ 2 * evalBivK5 q1_v_35721_biv =
      35721 * (q1_c 0 * (6 * S_K ^ 2) + q1_c 1 * (6 * S_K * Q_K) + q1_c 2 * (6 * S_K * B)) ∧
    w0 * S_K * A ^ 2 * B * evalBivK5 q1_e_35721_divB5_biv =
      35721 * (q1_c 0 * (6 * S_K * B) + q1_c 1 * ((5 * S_K - 3 * Q_K) * B)) := by
  intro A B q1_c
  have hH0_ev : ringEval vK5 H0_int_e = 7 * H0_of S_K Q_K T_K := by
    simp only [H0_int_e, ringEval, eS, eQ, eT, vK5, H0_of, Int.cast_neg, Int.cast_ofNat]; ring
  have hcA1_ev (k : Fin 3) : A * ringEval vK5 (cA1_21_div_A5_e k) =
      189 * (H0_of S_K Q_K T_K * dA1_fn k S_K Q_K 0 1 - A1_of S_K Q_K 0 1 * dH0_fn k S_K Q_K T_K) := by
    fin_cases k <;>
      (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        cA1_21_div_A5_e, ringEval, hH0_ev, ringEval_dH0_7, eA5, eS, eQ, vK5,
        A1_of, dA1_fn, Int.cast_neg, Int.cast_ofNat, A]; ring)
  have hA1_01 : A1_of S_K Q_K 0 1 = (25 / 27 : K5) * S_K * A ^ 2 := by
    simp only [A1_of, A]; ring
  have hEB : S_K * A * evalBivK5 EB_V0_9_div_SA5_biv = 9 * EB_of S_K Q_K T_K x_K y_K 0 1 :=
    evalBivK5_EB_V0
  constructor
  · simp only [q1_v_35721_biv, evalBivK5_bivAdd, evalBivK5_scale, evalBivK5_QY_V0_1701,
      ringEval, hH0_ev, eS, eQ, eB5, eT, vK5, Int.cast_ofNat, pow_zero, mul_one]
    have he1 : w0 * S_K * A ^ 2 *
        (189 * (ringEval vK5 (cA1_21_div_A5_e 0) * (6 * S_K ^ 2) +
          ringEval vK5 (cA1_21_div_A5_e 1) * (6 * (S_K * Q_K)) +
          ringEval vK5 (cA1_21_div_A5_e 2) * (6 * (S_K * (T_K - 3)))) *
          evalBivK5 EB_V0_9_div_SA5_biv) =
        189 * w0 * (A * ringEval vK5 (cA1_21_div_A5_e 0) * (6 * S_K ^ 2) +
          A * ringEval vK5 (cA1_21_div_A5_e 1) * (6 * S_K * Q_K) +
          A * ringEval vK5 (cA1_21_div_A5_e 2) * (6 * S_K * B)) *
        (S_K * A * evalBivK5 EB_V0_9_div_SA5_biv) := by dsimp only [B]; ring
    rw [mul_add, he1, hcA1_ev 0, hcA1_ev 1, hcA1_ev 2, hEB]
    simp only [q1_c, hA1_01, B]; ring
  · simp only [q1_e_35721_divB5_biv, evalBivK5_bivAdd, evalBivK5_scale, evalBivK5_QY_V0_1701,
      ringEval, hH0_ev, eS, eQ, e5S3Q, vK5, Int.cast_ofNat, pow_zero, mul_one]
    have he1 : w0 * S_K * A ^ 2 * B *
        (189 * (ringEval vK5 (cA1_21_div_A5_e 0) * (6 * S_K) +
          ringEval vK5 (cA1_21_div_A5_e 1) * (5 * S_K - 3 * Q_K)) *
          evalBivK5 EB_V0_9_div_SA5_biv) =
        189 * w0 * B * (A * ringEval vK5 (cA1_21_div_A5_e 0) * (6 * S_K) +
          A * ringEval vK5 (cA1_21_div_A5_e 1) * (5 * S_K - 3 * Q_K)) *
        (S_K * A * evalBivK5 EB_V0_9_div_SA5_biv) := by ring
    rw [mul_add, he1, hcA1_ev 0, hcA1_ev 1, hEB]
    simp only [q1_c, hA1_01]; ring

private lemma br2_0_final_cancel
    {w0 P_val P_eps P1_0 P0_0 : K5}
    (hw0_eq : w0 = -(25 / 4 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 2 / (T_K - 3) ^ 3)
    (hw0_ne : w0 ≠ 0)
    (hden_ne : 81 * k5Params.Av0 * w0 * ((15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4) ^ 3 *
      (((-59604644775390625 / 4941387170271576 : K5) * S_K ^ 8 * (-(5 * S_K - 9 * Q_K)) ^ 17 / (T_K - 3) ^ 12) ^ 2 /
        ((15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4)) ≠ 0)
    (hq2_ne : (15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4 ≠ 0)
    (hcd_eq : ((-59604644775390625 / 103769130575703096 : K5) *
        (225 * S_K - 45 * Q_K + 77 * T_K - 189) * S_K ^ 8 * (-(5 * S_K - 9 * Q_K)) ^ 17 / (T_K - 3) ^ 12) +
      (w0 * S_K / (T_K - 3)) *
        ((-2384185791015625 / 25942282643925774 : K5) *
          (225 * S_K - 45 * Q_K + 77 * T_K - 210) * S_K ^ 6 * (-(5 * S_K - 9 * Q_K)) ^ 15 / (T_K - 3) ^ 8) =
      (-59604644775390625 / 4941387170271576 : K5) * S_K ^ 8 * (-(5 * S_K - 9 * Q_K)) ^ 17 / (T_K - 3) ^ 12)
    (hP_val : ((15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4) ^ 3 * P_val =
      P1_0 * (w0 * S_K / (T_K - 3)) + P0_0)
    (hP_eps : ((15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4) ^ 3 * P_eps = P1_0 * w0)
    (hPg0_Z2_prod : Dual.C (35721 * (6 * S_K * (T_K - 3)) ^ 4) * ⟨P_val, P_eps⟩ =
      Dual.C (w0 ^ 2) *
        ⟨(8248380 / 51331077 : K5) * (5 * S_K - 3 * Q_K) * S_K ^ 3 * (5 * S_K - 9 * Q_K) ^ 2,
         -(2 / 51331077 : K5) * (T_K - 3) * S_K ^ 2 * (5 * S_K - 9 * Q_K) ^ 2 *
           (11943020 * S_K ^ 2 - 876486 * S_K * Q_K + 8382500 * S_K * T_K +
            5029500 * Q_K * T_K - 14837025 * S_K - 33647355 * Q_K)⟩ *
        ⟨w0 * S_K * (5 * S_K - 9 * Q_K) ^ 2 * evalBivK5 q1_v_35721_biv,
         w0 * S_K * (5 * S_K - 9 * Q_K) ^ 2 * (T_K - 3) * evalBivK5 q1_e_35721_divB5_biv⟩) :
    -(P1_0 * ((-59604644775390625 / 103769130575703096 : K5) *
        (225 * S_K - 45 * Q_K + 77 * T_K - 189) * S_K ^ 8 * (-(5 * S_K - 9 * Q_K)) ^ 17 / (T_K - 3) ^ 12) -
      P0_0 * ((-2384185791015625 / 25942282643925774 : K5) *
        (225 * S_K - 45 * Q_K + 77 * T_K - 210) * S_K ^ 6 * (-(5 * S_K - 9 * Q_K)) ^ 15 / (T_K - 3) ^ 8)) *
      w0 * ((50 / 27 : K5) * S_K * (5 * S_K - 9 * Q_K)) ^ 4 /
      (81 * k5Params.Av0 * w0 * ((15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4) ^ 3 *
        (((-59604644775390625 / 4941387170271576 : K5) * S_K ^ 8 * (-(5 * S_K - 9 * Q_K)) ^ 17 / (T_K - 3) ^ 12) ^ 2 /
          ((15625 / 59049 : K5) * S_K * (5 * S_K - 9 * Q_K) ^ 4))) =
    toK5_RU := by
  have hS := S_K_ne_zero; have hB := T_K_sub_3_ne
  have h21_ne : (21 : K5) ≠ 0 := by exact_mod_cast (by decide : (21 : ℕ) ≠ 0)
  have h6_ne : (6 : K5) ≠ 0 := by exact_mod_cast (by decide : (6 : ℕ) ≠ 0)
  have h35_ne : (35721 : K5) ≠ 0 := by exact_mod_cast (by decide : (35721 : ℕ) ≠ 0)
  have hL_U0_eq : ringEval vK5 L_U0_e = 225 * S_K - 45 * Q_K + 77 * T_K - 210 := by
    simp only [L_U0_e, ringEval, eS, eQ, eT, vK5, Int.cast_neg, Int.cast_ofNat]; ring
  have hQ_quad_eq : ringEval vK5 Q_quad_U0_e =
      11943020 * S_K ^ 2 - 876486 * S_K * Q_K + 8382500 * S_K * T_K +
        5029500 * Q_K * T_K - 14837025 * S_K - 33647355 * Q_K := by
    simp only [Q_quad_U0_e, ringEval, eS, eQ, eT, vK5, Int.cast_neg, Int.cast_ofNat]; ring
  have hU0_id : 21 * S_K * (173215980 * S_K * (5 * S_K - 3 * Q_K) * evalBivK5 q1_e_35721_divB5_biv -
      42 * (11943020 * S_K ^ 2 - 876486 * S_K * Q_K + 8382500 * S_K * T_K +
          5029500 * Q_K * T_K - 14837025 * S_K - 33647355 * Q_K) * evalBivK5 q1_v_35721_biv +
      8248380 * (5 * S_K - 3 * Q_K) * (225 * S_K - 45 * Q_K + 77 * T_K - 210) *
        evalBivK5 q1_v_35721_biv) =
      11907000 * S_K ^ 3 * (5 * S_K - 9 * Q_K) * ((D_RU : K5) * toK5_RU) := by
    have h := U0_biv_identity
    rw [LHS_U0_biv, RHS_U0_biv, evalBivK5_bivReduceX2, evalBivK5_bivAdd, evalBivK5_bivAdd,
      evalBivK5_scale, evalBivK5_scale, evalBivK5_scale, evalBivK5_scale, evalBivK5_RU] at h
    simp only [ringEval, hL_U0_eq, hQ_quad_eq, eS, e5S3Q, eA5, eQ, vK5,
      Int.cast_neg, Int.cast_ofNat, pow_zero, mul_one] at h
    linear_combination h
  have hk1 : (21 * (-(25 / 4 : K5)) * (-2384185791015625 / 25942282643925774) : K5) =
      -(-59604644775390625 / 4941387170271576) := by
    have hq : (21 * (-(25 / 4 : ℚ)) * (-2384185791015625 / 25942282643925774) : ℚ) =
        -(-59604644775390625 / 4941387170271576) := by norm_num
    simpa only [map_mul, map_div₀, map_neg, map_ofNat] using congrArg (Rat.castHom K5) hq
  have hk2 : (-(15625 / 59049 : K5) ^ 3 * (50 / 27) ^ 4 * (1 / (21 * 51331077)) *
      11907000 * (D_RU : K5) * (-(25 / 4)) ^ 4 : K5) =
      21 * 35721 * 81 * (-(4 / 243)) * 6 ^ 4 * (15625 / 59049) ^ 2 *
      (-(-59604644775390625 / 4941387170271576)) * (-(25 / 4)) ^ 2 := by
    have hq : (-(15625 / 59049 : ℚ) ^ 3 * (50 / 27) ^ 4 * (1 / (21 * 51331077)) *
        11907000 * (11644549875 : ℚ) * (-(25 / 4)) ^ 4 : ℚ) =
        21 * 35721 * 81 * (-(4 / 243)) * 6 ^ 4 * (15625 / 59049) ^ 2 *
        (-(-59604644775390625 / 4941387170271576)) * (-(25 / 4)) ^ 2 := by norm_num
    have hDRU : (D_RU : K5) = (11644549875 : K5) := by unfold D_RU; push_cast; rfl
    rw [hDRU]
    simpa only [map_mul, map_div₀, map_neg, map_pow, map_one, map_ofNat] using congrArg (Rat.castHom K5) hq
  have hk3 : (1 / (21 * 51331077) : K5) * 173215980 = 8248380 / 51331077 ∧
      (1 / (21 * 51331077) : K5) * 42 = 2 / 51331077 ∧
      (1 / (21 * 51331077) : K5) * 8248380 * 21 = 8248380 / 51331077 := by
    have hq : (1 / (21 * 51331077) : ℚ) * 173215980 = 8248380 / 51331077 ∧
        (1 / (21 * 51331077) : ℚ) * 42 = 2 / 51331077 ∧
        (1 / (21 * 51331077) : ℚ) * 8248380 * 21 = 8248380 / 51331077 := by norm_num
    refine ⟨?_, ?_, ?_⟩
    · simpa only [map_mul, map_div₀, map_one, map_ofNat] using congrArg (Rat.castHom K5) hq.1
    · simpa only [map_mul, map_div₀, map_one, map_ofNat] using congrArg (Rat.castHom K5) hq.2.1
    · simpa only [map_mul, map_div₀, map_one, map_ofNat] using congrArg (Rat.castHom K5) hq.2.2
  have hAv0_eq : k5Params.Av0 = -(4 / 243 : K5) * (T_K - 3) ^ 3 := by
    simp only [CoverParams.Av0, CoverParams.inv243, k5Params_inv3, k5Params_T]; ring
  rw [hAv0_eq] at hden_ne ⊢
  generalize evalBivK5 q1_v_35721_biv = q1_v at hPg0_Z2_prod hU0_id
  generalize evalBivK5 q1_e_35721_divB5_biv = q1_e at hPg0_Z2_prod hU0_id
  generalize toK5_RU = RU_val at hU0_id ⊢
  generalize (-(25 / 4 : K5)) = r25 at hw0_eq hk1 hk2
  generalize (15625 / 59049 : K5) = r15 at hden_ne hq2_ne hP_val hP_eps hk2 ⊢
  generalize (-59604644775390625 / 4941387170271576 : K5) = rcd at hden_ne hcd_eq hk1 hk2 ⊢
  generalize (-59604644775390625 / 103769130575703096 : K5) = rd0 at hcd_eq ⊢
  generalize (-2384185791015625 / 25942282643925774 : K5) = rd1 at hcd_eq hk1 ⊢
  generalize (50 / 27 : K5) = r50 at hk2 ⊢
  generalize (-(4 / 243 : K5)) = r4 at hden_ne hk2 ⊢
  generalize (8248380 / 51331077 : K5) = r82 at hPg0_Z2_prod hk3
  generalize (2 / 51331077 : K5) = r2 at hPg0_Z2_prod hk3
  generalize (1 / (21 * 51331077) : K5) = rinv at hk2 hk3
  generalize (173215980 : K5) = r173 at hU0_id hk3
  generalize (8248380 : K5) = r82i at hU0_id hk3
  generalize (11907000 : K5) = r119 at hU0_id hk2
  generalize (D_RU : K5) = rDRU at hU0_id hk2
  generalize (35721 : K5) = r35 at h35_ne hPg0_Z2_prod hk2
  generalize (11943020 * S_K ^ 2 - 876486 * S_K * Q_K + 8382500 * S_K * T_K +
      5029500 * Q_K * T_K - 14837025 * S_K - 33647355 * Q_K : K5) = Qq at hPg0_Z2_prod hU0_id
  generalize (225 * S_K - 45 * Q_K + 77 * T_K - 210 : K5) = L210 at hcd_eq hU0_id ⊢
  generalize (225 * S_K - 45 * Q_K + 77 * T_K - 189 : K5) = L189 at hcd_eq ⊢
  generalize (5 * S_K - 9 * Q_K : K5) = A at hw0_eq hden_ne hq2_ne hcd_eq hP_val hP_eps hPg0_Z2_prod hU0_id ⊢
  generalize (5 * S_K - 3 * Q_K : K5) = A3 at hPg0_Z2_prod hU0_id
  generalize (T_K - 3 : K5) = B at hB hw0_eq hden_ne hcd_eq hP_val hPg0_Z2_prod ⊢
  have hB3 : B ^ 3 ≠ 0 := pow_ne_zero 3 hB
  have hB8 : B ^ 8 ≠ 0 := pow_ne_zero 8 hB
  have hB12 : B ^ 12 ≠ 0 := pow_ne_zero 12 hB
  have hw0_B3 : w0 * B ^ 3 = r25 * S_K * A ^ 2 := by rw [hw0_eq, div_mul_cancel₀ _ hB3]
  have hd_ab_ne : 6 * S_K * B ≠ 0 := mul_ne_zero (mul_ne_zero h6_ne hS) hB
  have hPv : r35 * (6 * S_K * B) ^ 4 * P_val = w0 ^ 3 * r82 * A3 * S_K ^ 4 * A ^ 4 * q1_v := by
    have h := congrArg Dual.val hPg0_Z2_prod
    simp only [Dual.mul_val, Dual.C_val] at h; rw [h]; ring
  have hPe : r35 * (6 * S_K * B) ^ 4 * P_eps =
      w0 ^ 3 * S_K ^ 3 * A ^ 4 * B * (r82 * S_K * A3 * q1_e - r2 * Qq * q1_v) := by
    have h := congrArg Dual.eps hPg0_Z2_prod
    simp only [Dual.mul_val, Dual.mul_eps, Dual.C_val, Dual.C_eps, zero_mul, add_zero] at h; rw [h]; ring
  set cd : K5 := rcd * S_K ^ 8 * (-A) ^ 17 / B ^ 12
  set d1 : K5 := rd1 * L210 * S_K ^ 6 * (-A) ^ 15 / B ^ 8
  set d0 : K5 := rd0 * L189 * S_K ^ 8 * (-A) ^ 17 / B ^ 12
  set q2 : K5 := r15 * S_K * A ^ 4
  have hcd_B12 : cd * B ^ 12 = rcd * S_K ^ 8 * (-A) ^ 17 := by dsimp only [cd]; rw [div_mul_cancel₀ _ hB12]
  have hw0_d1 : 21 * S_K * (w0 * d1) = -L210 * B * cd := by
    apply mul_left_cancel₀ hB12
    have h1 : B ^ 12 * (21 * S_K * (w0 * d1)) = 21 * S_K * B * (w0 * B ^ 3) * (d1 * B ^ 8) := by ring
    have hd1_B8 : d1 * B ^ 8 = rd1 * L210 * S_K ^ 6 * (-A) ^ 15 := by dsimp only [d1]; rw [div_mul_cancel₀ _ hB8]
    rw [h1, hw0_B3, hd1_B8, show B ^ 12 * (-L210 * B * cd) = -L210 * B * (cd * B ^ 12) by ring, hcd_B12]
    linear_combination (L210 * S_K ^ 8 * A ^ 2 * (-A) ^ 15 * B) * hk1
  have hinner : 21 * S_K * (r35 * (6 * S_K * B) ^ 4 * P_eps) + L210 * B * (r35 * (6 * S_K * B) ^ 4 * P_val) =
      w0 ^ 3 * rinv * S_K ^ 3 * A ^ 4 * B * (r119 * S_K ^ 3 * A * (rDRU * RU_val)) := by
    rw [hPe, hPv, ← hU0_id]
    linear_combination -(w0 ^ 3 * S_K ^ 5 * A ^ 4 * B * A3 * q1_e * 21) * hk3.1 +
      (w0 ^ 3 * S_K ^ 4 * A ^ 4 * B * Qq * q1_v * 21) * hk3.2.1 -
      (w0 ^ 3 * S_K ^ 4 * A ^ 4 * B * L210 * A3 * q1_v) * hk3.2.2
  rw [div_eq_iff hden_ne]
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero h21_ne hS) (mul_ne_zero h35_ne (pow_ne_zero 4 hd_ab_ne))) hw0_ne)
  have hcomb : 21 * S_K * (r35 * (6 * S_K * B) ^ 4) * w0 * (-(P1_0 * d0 - P0_0 * d1) * w0 * (r50 * S_K * A) ^ 4) =
      -q2 ^ 3 * (r50 * S_K * A) ^ 4 * cd * w0 *
        (21 * S_K * (r35 * (6 * S_K * B) ^ 4 * P_eps) + L210 * B * (r35 * (6 * S_K * B) ^ 4 * P_val)) := by
    have h1 : w0 * (P1_0 * d0 - P0_0 * d1) = (P1_0 * w0) * cd - (P1_0 * (w0 * S_K / B) + P0_0) * (w0 * d1) := by
      rw [← hcd_eq]; ring
    have hs1 : 21 * S_K * (r35 * (6 * S_K * B) ^ 4) * w0 * (-(P1_0 * d0 - P0_0 * d1) * w0 * (r50 * S_K * A) ^ 4) =
        -(r35 * (6 * S_K * B) ^ 4) * (r50 * S_K * A) ^ 4 * w0 * (21 * S_K * (w0 * (P1_0 * d0 - P0_0 * d1))) := by ring
    rw [hs1, h1, ← hP_eps, ← hP_val]
    have hs2 : 21 * S_K * (q2 ^ 3 * P_eps * cd - q2 ^ 3 * P_val * (w0 * d1)) =
        21 * S_K * (q2 ^ 3 * P_eps) * cd - q2 ^ 3 * P_val * (21 * S_K * (w0 * d1)) := by ring
    rw [hs2, hw0_d1]; ring
  rw [hcomb, hinner]
  apply mul_left_cancel₀ (mul_ne_zero hB12 hB12)
  have hq2_div : q2 ^ 3 * (cd ^ 2 / q2) = q2 ^ 2 * cd ^ 2 := by
    rw [show q2 ^ 3 * (cd ^ 2 / q2) = q2 ^ 2 * (cd ^ 2 / q2 * q2) by ring, div_mul_cancel₀ _ hq2_ne]
  have hL : B ^ 12 * B ^ 12 * (-q2 ^ 3 * (r50 * S_K * A) ^ 4 * cd * w0 *
      (w0 ^ 3 * rinv * S_K ^ 3 * A ^ 4 * B * (r119 * S_K ^ 3 * A * (rDRU * RU_val)))) =
      (-r15 ^ 3 * r50 ^ 4 * rinv * r119 * rDRU * r25 ^ 4) * (B ^ 12 * B * S_K ^ 17 * A ^ 29 * cd * RU_val) := by
    rw [show B ^ 12 * B ^ 12 * (-q2 ^ 3 * (r50 * S_K * A) ^ 4 * cd * w0 *
            (w0 ^ 3 * rinv * S_K ^ 3 * A ^ 4 * B * (r119 * S_K ^ 3 * A * (rDRU * RU_val)))) =
          -q2 ^ 3 * (r50 * S_K * A) ^ 4 * rinv * r119 * rDRU * B ^ 12 * B * S_K ^ 6 * A ^ 5 * cd * (w0 * B ^ 3) ^ 4 * RU_val by ring,
        hw0_B3]; dsimp only [q2]; ring
  have hR : B ^ 12 * B ^ 12 * (21 * S_K * (r35 * (6 * S_K * B) ^ 4) * w0 *
      (RU_val * (81 * (r4 * B ^ 3) * w0 * q2 ^ 3 * (cd ^ 2 / q2)))) =
      (21 * r35 * 81 * r4 * 6 ^ 4 * r15 ^ 2 * (-rcd) * r25 ^ 2) * (B ^ 12 * B * S_K ^ 17 * A ^ 29 * cd * RU_val) := by
    rw [mul_assoc _ (q2 ^ 3), hq2_div]
    rw [show B ^ 12 * B ^ 12 * (21 * S_K * (r35 * (6 * S_K * B) ^ 4) * w0 *
            (RU_val * (81 * (r4 * B ^ 3) * w0 * (q2 ^ 2 * cd ^ 2)))) =
          21 * r35 * 81 * r4 * 6 ^ 4 * S_K ^ 5 * B ^ 13 * q2 ^ 2 * (w0 * B ^ 3) ^ 2 * cd * (cd * B ^ 12) * RU_val by ring,
        hw0_B3, hcd_B12]; dsimp only [q2]; ring
  rw [hL, hR, hk2]



lemma br2_0_q1_cancel_proof
    {w0 P_val P_eps P1_0 P0_0 : SymmetricSexticResidual.K5Field.K5}
    (hw0_eq : w0 = -(25 / 4 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 2 / (SymmetricSexticResidual.K5Field.T_K - 3) ^ 3)
    (hw0_ne : w0 ≠ 0)
    (hden_ne : 81 * SymmetricSexticResidual.CoverAlgebra.k5Params.Av0 * w0 *
      ((15625 / 59049 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 4) ^ 3 *
      (((-59604644775390625 / 4941387170271576 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K ^ 8 * (-(5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)) ^ 17 / (SymmetricSexticResidual.K5Field.T_K - 3) ^ 12) ^ 2 /
        ((15625 / 59049 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 4)) ≠ 0)
    (hq2_ne : (15625 / 59049 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 4 ≠ 0)
    (hcd_eq : ((-59604644775390625 / 103769130575703096 : SymmetricSexticResidual.K5Field.K5) *
        (225 * SymmetricSexticResidual.K5Field.S_K - 45 * SymmetricSexticResidual.K5Field.Q_K + 77 * SymmetricSexticResidual.K5Field.T_K - 189) * SymmetricSexticResidual.K5Field.S_K ^ 8 * (-(5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)) ^ 17 / (SymmetricSexticResidual.K5Field.T_K - 3) ^ 12) +
      (w0 * SymmetricSexticResidual.K5Field.S_K / (SymmetricSexticResidual.K5Field.T_K - 3)) *
        ((-2384185791015625 / 25942282643925774 : SymmetricSexticResidual.K5Field.K5) *
          (225 * SymmetricSexticResidual.K5Field.S_K - 45 * SymmetricSexticResidual.K5Field.Q_K + 77 * SymmetricSexticResidual.K5Field.T_K - 210) * SymmetricSexticResidual.K5Field.S_K ^ 6 * (-(5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)) ^ 15 / (SymmetricSexticResidual.K5Field.T_K - 3) ^ 8) =
      (-59604644775390625 / 4941387170271576 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K ^ 8 * (-(5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)) ^ 17 / (SymmetricSexticResidual.K5Field.T_K - 3) ^ 12)
    (hP_val : ((15625 / 59049 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 4) ^ 3 * P_val =
      P1_0 * (w0 * SymmetricSexticResidual.K5Field.S_K / (SymmetricSexticResidual.K5Field.T_K - 3)) + P0_0)
    (hP_eps : ((15625 / 59049 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 4) ^ 3 * P_eps = P1_0 * w0)
    (hPg0_Z2_prod :
      let q1_c := fun k : Fin 3 =>
        9 * w0 * (SymmetricSexticResidual.SheetCalculus.H0_of SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K * SymmetricSexticResidual.SheetCalculus.A1_of SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K 0 1 *
            (SymmetricSexticResidual.SheetCalculus.QY_num SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K SymmetricSexticResidual.K5Field.y_K 0 1 k - SymmetricSexticResidual.SheetCalculus.QY_num SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K SymmetricSexticResidual.K5Field.y_K 0 0 k) +
          (SymmetricSexticResidual.SheetCalculus.H0_of SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K * SymmetricSexticResidual.SheetCalculus.dA1_fn k SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K 0 1 -
            SymmetricSexticResidual.SheetCalculus.A1_of SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K 0 1 * SymmetricSexticResidual.SheetCalculus.dH0_fn k SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K) *
            SymmetricSexticResidual.SheetCalculus.EB_of SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K SymmetricSexticResidual.K5Field.y_K 0 1)
      QuadraticCovers.Dual.C (35721 * (6 * SymmetricSexticResidual.K5Field.S_K * (SymmetricSexticResidual.K5Field.T_K - 3)) ^ 4) * ⟨P_val, P_eps⟩ =
      QuadraticCovers.Dual.C (w0 ^ 2) *
        ⟨(8248380 / 51331077 : SymmetricSexticResidual.K5Field.K5) * (5 * SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) * SymmetricSexticResidual.K5Field.S_K ^ 3 * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 2,
         -(2 / 51331077 : SymmetricSexticResidual.K5Field.K5) * (SymmetricSexticResidual.K5Field.T_K - 3) * SymmetricSexticResidual.K5Field.S_K ^ 2 * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 2 *
           (11943020 * SymmetricSexticResidual.K5Field.S_K ^ 2 - 876486 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.Q_K + 8382500 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.T_K +
            5029500 * SymmetricSexticResidual.K5Field.Q_K * SymmetricSexticResidual.K5Field.T_K - 14837025 * SymmetricSexticResidual.K5Field.S_K - 33647355 * SymmetricSexticResidual.K5Field.Q_K)⟩ *
        ⟨35721 * (q1_c 0 * (6 * SymmetricSexticResidual.K5Field.S_K ^ 2) + q1_c 1 * (6 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.Q_K) + q1_c 2 * (6 * SymmetricSexticResidual.K5Field.S_K * (SymmetricSexticResidual.K5Field.T_K - 3))),
         35721 * (q1_c 0 * (6 * SymmetricSexticResidual.K5Field.S_K * (SymmetricSexticResidual.K5Field.T_K - 3)) + q1_c 1 * ((5 * SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) * (SymmetricSexticResidual.K5Field.T_K - 3)))⟩) :
    -(P1_0 * ((-59604644775390625 / 103769130575703096 : SymmetricSexticResidual.K5Field.K5) *
        (225 * SymmetricSexticResidual.K5Field.S_K - 45 * SymmetricSexticResidual.K5Field.Q_K + 77 * SymmetricSexticResidual.K5Field.T_K - 189) * SymmetricSexticResidual.K5Field.S_K ^ 8 * (-(5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)) ^ 17 / (SymmetricSexticResidual.K5Field.T_K - 3) ^ 12) -
      P0_0 * ((-2384185791015625 / 25942282643925774 : SymmetricSexticResidual.K5Field.K5) *
        (225 * SymmetricSexticResidual.K5Field.S_K - 45 * SymmetricSexticResidual.K5Field.Q_K + 77 * SymmetricSexticResidual.K5Field.T_K - 210) * SymmetricSexticResidual.K5Field.S_K ^ 6 * (-(5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)) ^ 15 / (SymmetricSexticResidual.K5Field.T_K - 3) ^ 8)) *
      w0 * ((50 / 27 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)) ^ 4 /
      (81 * SymmetricSexticResidual.CoverAlgebra.k5Params.Av0 * w0 *
        ((15625 / 59049 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 4) ^ 3 *
        (((-59604644775390625 / 4941387170271576 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K ^ 8 * (-(5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)) ^ 17 / (SymmetricSexticResidual.K5Field.T_K - 3) ^ 12) ^ 2 /
          ((15625 / 59049 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 4))) =
    SymmetricSexticResidual.LocalResidueU0.toK5_RU := by
  obtain ⟨hq1v, hq1e⟩ := br2_0_q1_biv_eval w0
  dsimp only at hPg0_Z2_prod
  rw [← hq1v, ← hq1e] at hPg0_Z2_prod
  exact br2_0_final_cancel hw0_eq hw0_ne hden_ne hq2_ne hcd_eq hP_val hP_eps hPg0_Z2_prod

end SymmetricSexticResidual.LocalResidueU0

theorem solution
    {w0 P_val P_eps P1_0 P0_0 : SymmetricSexticResidual.K5Field.K5}
    (hw0_eq : w0 = -(25 / 4 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 2 / (SymmetricSexticResidual.K5Field.T_K - 3) ^ 3)
    (hw0_ne : w0 ≠ 0)
    (hden_ne : 81 * SymmetricSexticResidual.CoverAlgebra.k5Params.Av0 * w0 *
      ((15625 / 59049 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 4) ^ 3 *
      (((-59604644775390625 / 4941387170271576 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K ^ 8 * (-(5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)) ^ 17 / (SymmetricSexticResidual.K5Field.T_K - 3) ^ 12) ^ 2 /
        ((15625 / 59049 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 4)) ≠ 0)
    (hq2_ne : (15625 / 59049 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 4 ≠ 0)
    (hcd_eq : ((-59604644775390625 / 103769130575703096 : SymmetricSexticResidual.K5Field.K5) *
        (225 * SymmetricSexticResidual.K5Field.S_K - 45 * SymmetricSexticResidual.K5Field.Q_K + 77 * SymmetricSexticResidual.K5Field.T_K - 189) * SymmetricSexticResidual.K5Field.S_K ^ 8 * (-(5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)) ^ 17 / (SymmetricSexticResidual.K5Field.T_K - 3) ^ 12) +
      (w0 * SymmetricSexticResidual.K5Field.S_K / (SymmetricSexticResidual.K5Field.T_K - 3)) *
        ((-2384185791015625 / 25942282643925774 : SymmetricSexticResidual.K5Field.K5) *
          (225 * SymmetricSexticResidual.K5Field.S_K - 45 * SymmetricSexticResidual.K5Field.Q_K + 77 * SymmetricSexticResidual.K5Field.T_K - 210) * SymmetricSexticResidual.K5Field.S_K ^ 6 * (-(5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)) ^ 15 / (SymmetricSexticResidual.K5Field.T_K - 3) ^ 8) =
      (-59604644775390625 / 4941387170271576 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K ^ 8 * (-(5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)) ^ 17 / (SymmetricSexticResidual.K5Field.T_K - 3) ^ 12)
    (hP_val : ((15625 / 59049 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 4) ^ 3 * P_val =
      P1_0 * (w0 * SymmetricSexticResidual.K5Field.S_K / (SymmetricSexticResidual.K5Field.T_K - 3)) + P0_0)
    (hP_eps : ((15625 / 59049 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 4) ^ 3 * P_eps = P1_0 * w0)
    (hPg0_Z2_prod :
      let q1_c := fun k : Fin 3 =>
        9 * w0 * (SymmetricSexticResidual.SheetCalculus.H0_of SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K * SymmetricSexticResidual.SheetCalculus.A1_of SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K 0 1 *
            (SymmetricSexticResidual.SheetCalculus.QY_num SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K SymmetricSexticResidual.K5Field.y_K 0 1 k - SymmetricSexticResidual.SheetCalculus.QY_num SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K SymmetricSexticResidual.K5Field.y_K 0 0 k) +
          (SymmetricSexticResidual.SheetCalculus.H0_of SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K * SymmetricSexticResidual.SheetCalculus.dA1_fn k SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K 0 1 -
            SymmetricSexticResidual.SheetCalculus.A1_of SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K 0 1 * SymmetricSexticResidual.SheetCalculus.dH0_fn k SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K) *
            SymmetricSexticResidual.SheetCalculus.EB_of SymmetricSexticResidual.K5Field.S_K SymmetricSexticResidual.K5Field.Q_K SymmetricSexticResidual.K5Field.T_K SymmetricSexticResidual.K5Field.x_K SymmetricSexticResidual.K5Field.y_K 0 1)
      QuadraticCovers.Dual.C (35721 * (6 * SymmetricSexticResidual.K5Field.S_K * (SymmetricSexticResidual.K5Field.T_K - 3)) ^ 4) * ⟨P_val, P_eps⟩ =
      QuadraticCovers.Dual.C (w0 ^ 2) *
        ⟨(8248380 / 51331077 : SymmetricSexticResidual.K5Field.K5) * (5 * SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) * SymmetricSexticResidual.K5Field.S_K ^ 3 * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 2,
         -(2 / 51331077 : SymmetricSexticResidual.K5Field.K5) * (SymmetricSexticResidual.K5Field.T_K - 3) * SymmetricSexticResidual.K5Field.S_K ^ 2 * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 2 *
           (11943020 * SymmetricSexticResidual.K5Field.S_K ^ 2 - 876486 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.Q_K + 8382500 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.T_K +
            5029500 * SymmetricSexticResidual.K5Field.Q_K * SymmetricSexticResidual.K5Field.T_K - 14837025 * SymmetricSexticResidual.K5Field.S_K - 33647355 * SymmetricSexticResidual.K5Field.Q_K)⟩ *
        ⟨35721 * (q1_c 0 * (6 * SymmetricSexticResidual.K5Field.S_K ^ 2) + q1_c 1 * (6 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.Q_K) + q1_c 2 * (6 * SymmetricSexticResidual.K5Field.S_K * (SymmetricSexticResidual.K5Field.T_K - 3))),
         35721 * (q1_c 0 * (6 * SymmetricSexticResidual.K5Field.S_K * (SymmetricSexticResidual.K5Field.T_K - 3)) + q1_c 1 * ((5 * SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) * (SymmetricSexticResidual.K5Field.T_K - 3)))⟩) :
    -(P1_0 * ((-59604644775390625 / 103769130575703096 : SymmetricSexticResidual.K5Field.K5) *
        (225 * SymmetricSexticResidual.K5Field.S_K - 45 * SymmetricSexticResidual.K5Field.Q_K + 77 * SymmetricSexticResidual.K5Field.T_K - 189) * SymmetricSexticResidual.K5Field.S_K ^ 8 * (-(5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)) ^ 17 / (SymmetricSexticResidual.K5Field.T_K - 3) ^ 12) -
      P0_0 * ((-2384185791015625 / 25942282643925774 : SymmetricSexticResidual.K5Field.K5) *
        (225 * SymmetricSexticResidual.K5Field.S_K - 45 * SymmetricSexticResidual.K5Field.Q_K + 77 * SymmetricSexticResidual.K5Field.T_K - 210) * SymmetricSexticResidual.K5Field.S_K ^ 6 * (-(5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)) ^ 15 / (SymmetricSexticResidual.K5Field.T_K - 3) ^ 8)) *
      w0 * ((50 / 27 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)) ^ 4 /
      (81 * SymmetricSexticResidual.CoverAlgebra.k5Params.Av0 * w0 *
        ((15625 / 59049 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 4) ^ 3 *
        (((-59604644775390625 / 4941387170271576 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K ^ 8 * (-(5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K)) ^ 17 / (SymmetricSexticResidual.K5Field.T_K - 3) ^ 12) ^ 2 /
          ((15625 / 59049 : SymmetricSexticResidual.K5Field.K5) * SymmetricSexticResidual.K5Field.S_K * (5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K) ^ 4))) =
    SymmetricSexticResidual.LocalResidueU0.toK5_RU :=
  SymmetricSexticResidual.LocalResidueU0.br2_0_q1_cancel_proof hw0_eq hw0_ne hden_ne hq2_ne hcd_eq hP_val hP_eps hPg0_Z2_prod
