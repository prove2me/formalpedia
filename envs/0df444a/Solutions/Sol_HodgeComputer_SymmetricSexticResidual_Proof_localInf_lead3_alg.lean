-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localInf_lead3_alg
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T15:56:47.528859+00:00
-- url     : https://prove2.me/submissions/6ccb2c61-f736-4821-bddf-6a09f0cf6184

import Definitions.Def_HodgeComputerSSR_LocalInfAlgDefs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

namespace SymmetricSexticResidual.LocalResidueInfAlg
open Polynomial QuadraticCovers

lemma d20_U3_eq {R : Type*} [Field R] [CharZero R] (a b xS xQ : R) :
    d20_U3 a b xS xQ =
      (4 / 5103 : R) * (441 * a ^ 2 * xQ ^ 2 - 154 * a ^ 2 * xQ * xS - 90 * a ^ 2 * xQ - 90 * a ^ 2 -
        1260 * a * b * xQ ^ 2 + 540 * a * b * xQ + 154 * a * b * xS ^ 2 + 540 * a * b +
        1260 * b ^ 2 * xQ * xS - 810 * b ^ 2 * xQ - 441 * b ^ 2 * xS ^ 2 - 810 * b ^ 2) := by
  simp only [d20_U3, minor_U3, dHS_2, dHS_1, dHQ_1]; ring

lemma d21_U3_eq {R : Type*} [Field R] [CharZero R] (a b xS xQ : R) :
    d21_U3 a b xS xQ =
      -(8 / 5103 : R) * (a - 3 * b) *
        (77 * a ^ 2 * xQ - 210 * a * b * xQ - 77 * a * b * xS + 45 * a * b + 210 * b ^ 2 * xS - 135 * b ^ 2) := by
  simp only [d21_U3, minor_U3, dHS_2, dHS_1, dHQ_1]; ring

lemma d10_U3_eq {R : Type*} [Field R] [CharZero R] (a b xS xQ : R) :
    d10_U3 a b xS xQ =
      -(8 / 5103 : R) * (3 * xQ - xS) *
        (210 * a * xQ ^ 2 - 77 * a * xQ * xS - 90 * a * xQ - 90 * a -
         210 * b * xQ * xS + 135 * b * xQ + 77 * b * xS ^ 2 + 45 * b * xS + 270 * b) := by
  simp only [d10_U3, minor_U3, dHS_2, dHS_1, dHQ_1]; ring

lemma d20_U2_eq {R : Type*} [Field R] [CharZero R] (a b xS xQ : R) :
    d20_U2 a b xS xQ =
      (2 / 1701 : R) * (1533 * a ^ 2 * xQ ^ 2 - 532 * a ^ 2 * xQ * xS + 2145 * a ^ 2 * xQ + 2145 * a ^ 2 -
        5880 * a * b * xQ ^ 2 - 8280 * a * b * xQ + 532 * a * b * xS ^ 2 - 8280 * a * b +
        5880 * b ^ 2 * xQ * xS + 7020 * b ^ 2 * xQ - 1533 * b ^ 2 * xS ^ 2 + 7020 * b ^ 2) := by
  simp only [d20_U2, minor_U2, dHS_2, dHS_1, dHS_0, dHQ_1, dHQ_0]; ring

lemma d21_U2_eq {R : Type*} [Field R] [CharZero R] (a b xS xQ : R) :
    d21_U2 a b xS xQ =
      -(2 / 1701 : R) * (532 * a ^ 3 * xQ - 3066 * a ^ 2 * b * xQ - 532 * a ^ 2 * b * xS - 2145 * a ^ 2 * b +
        5880 * a * b ^ 2 * xQ + 3066 * a * b ^ 2 * xS + 8280 * a * b ^ 2 - 5880 * b ^ 3 * xS - 7020 * b ^ 3) := by
  simp only [d21_U2, minor_U2, dHS_2, dHS_1, dHS_0, dHQ_1, dHQ_0]; ring

lemma d10_U2_eq {R : Type*} [Field R] [CharZero R] (a b xS xQ : R) :
    d10_U2 a b xS xQ =
      -(2 / 1701 : R) * (5880 * a * xQ ^ 3 - 3066 * a * xQ ^ 2 * xS + 8280 * a * xQ ^ 2 +
        532 * a * xQ * xS ^ 2 - 4290 * a * xQ * xS + 8280 * a * xQ - 4290 * a * xS -
        5880 * b * xQ ^ 2 * xS - 7020 * b * xQ ^ 2 + 3066 * b * xQ * xS ^ 2 - 14040 * b * xQ -
        532 * b * xS ^ 3 + 2145 * b * xS ^ 2 + 8280 * b * xS) := by
  simp only [d10_U2, minor_U2, dHS_2, dHS_1, dHS_0, dHQ_1, dHQ_0]; ring

lemma A0V_Uk_eq {R : Type*} [Field R] [CharZero R] (k : Fin 4) (a b xS xQ : R) :
    let (d10, d20, d21) : R × R × R := match k with
      | 0 => (d10_U0 a b xS xQ, d20_U0 a b xS xQ, d21_U0 a b xS xQ)
      | 1 => (d10_U1 a b xS xQ, d20_U1 a b xS xQ, d21_U1 a b xS xQ)
      | 2 => (d10_U2 a b xS xQ, d20_U2 a b xS xQ, d21_U2 a b xS xQ)
      | 3 => (d10_U3 a b xS xQ, d20_U3 a b xS xQ, d21_U3 a b xS xQ)
    A0V_Uk k a b xS xQ =
      (-(223 / 2916 : R) * a + (25 / 162) * b - (7 / 479)) * d10 +
      (-(223 / 1620 : R) * a + (5 / 18) * b - (25 / 162) * xQ + (223 / 2916) * xS - (35 / 958)) * d20 +
      (-(5 / 18 : R) * xQ + (223 / 1620) * xS - (441 / 23950)) * d21 := by
  fin_cases k <;> (simp only [A0V_Uk, numM_Uk]; ring)

lemma AX_Uk_eq {R : Type*} [Field R] [CharZero R] (k : Fin 4) (a b xS xQ : R) :
    let (d10, d20, d21) : R × R × R := match k with
      | 0 => (d10_U0 a b xS xQ, d20_U0 a b xS xQ, d21_U0 a b xS xQ)
      | 1 => (d10_U1 a b xS xQ, d20_U1 a b xS xQ, d21_U1 a b xS xQ)
      | 2 => (d10_U2 a b xS xQ, d20_U2 a b xS xQ, d21_U2 a b xS xQ)
      | 3 => (d10_U3 a b xS xQ, d20_U3 a b xS xQ, d21_U3 a b xS xQ)
    AX_Uk k a b xS xQ =
      (-(1 / 162 : R) * a - (119 / 5748)) * d10 +
      (-(1 / 90 : R) * a + (1 / 162) * xS - (140 / 1437)) * d20 +
      ((1 / 90 : R) * xS - (5187 / 47900)) * d21 := by
  fin_cases k <;> (simp only [AX_Uk, numM_Uk]; ring)

lemma diff3_lin_mul {R : Type*} [Field R] [CharZero R] (p1 p0 : R) (D : R → R) :
    let g := fun z : R => (p1 * z + p0) * D z
    (g 2 - 3 * g 1 + 3 * g 0 - g (-1)) / 6 =
      p1 * ((2 * D 2 - 3 * D 1 + D (-1)) / 6) +
      p0 * ((D 2 - 3 * D 1 + 3 * D 0 - D (-1)) / 6) := by
  dsimp only; ring

-- Exact cubic expansion of `A0V_Uk 3` at `(a, b) = (u, u / 3 + β)` for free `β`, then specializing `β`:
lemma A0V_U3_poly_beta {R : Type*} [Field R] [CharZero R] (S Q T u β : R) :
    A0V_Uk 3 u (u / 3 + β) (S - u * T) (Q - (u / 3 + β) * T) =
      ((73 / 7971615 : R) * (5 * T - 9) * (S - 3 * Q) ^ 2) * u ^ 3 +
      ((3 * Q - S) * (329432250 * Q ^ 2 - 225740725 * Q * S - 329432250 * Q * T * β + 7144200 * Q * T +
        592978050 * Q * β - 87606000 * Q + 38643325 * S ^ 2 + 97572300 * S * T * β - 2381400 * S * T -
        175630140 * S * β + 29202000 * S - 7144200 * T ^ 2 * β + 17860500 * T * β - 9001692 * β) / 44548041825) * u ^ 2 +
      ((214326000 * Q ^ 3 - 658864500 * Q ^ 2 * S * β - 221470200 * Q ^ 2 * S - 428652000 * Q ^ 2 * T * β +
        1256829750 * Q ^ 2 * β - 45927000 * Q ^ 2 + 451481450 * Q * S ^ 2 * β + 76204800 * Q * S ^ 2 +
        658864500 * Q * S * T * β ^ 2 + 285768000 * Q * S * T * β - 1185956100 * Q * S * β ^ 2 -
        680535000 * Q * S * β + 30618000 * Q * S + 214326000 * Q * T ^ 2 * β ^ 2 - 1256829750 * Q * T * β ^ 2 +
        1567877310 * Q * β ^ 2 + 472054500 * Q * β - 77286650 * S ^ 3 * β - 8731800 * S ^ 3 -
        213502275 * S ^ 2 * T * β ^ 2 - 47628000 * S ^ 2 * T * β + 384304095 * S ^ 2 * β ^ 2 +
        87197250 * S ^ 2 * β - 5103000 * S ^ 2 - 64297800 * S * T ^ 2 * β ^ 2 + 401082750 * S * T * β ^ 2 -
        513624078 * S * β ^ 2 - 157351500 * S * β + 45927000 * T ^ 2 * β ^ 2 - 350844750 * T * β ^ 2 +
        482717070 * β ^ 2) / 14849347275) * u +
      A0V_Uk 3 0 β S (Q - β * T) := by
  rw [A0V_Uk_eq 3 u (u / 3 + β) (S - u * T) (Q - (u / 3 + β) * T),
      A0V_Uk_eq 3 0 β S (Q - β * T)]
  have hd10 : d10_U3 u (u / 3 + β) (S - u * T) (Q - (u / 3 + β) * T) =
      (-(8 / 2187 : R) * T * (3 * Q - S) * (3 * Q - S - 3 * T * β)) * u ^ 2 +
      (-(8 / 15309 : R) * (3 * Q - S - 3 * T * β) * (630 * Q ^ 2 - 441 * Q * S - 630 * Q * T * β - 135 * Q +
        77 * S ^ 2 + 189 * S * T * β + 45 * S - 135 * T * β)) * u +
      d10_U3 0 β S (Q - β * T) := by
    rw [d10_U3_eq, d10_U3_eq]; ring
  have hd20 : d20_U3 u (u / 3 + β) (S - u * T) (Q - (u / 3 + β) * T) =
      ((4 / 2187 : R) * (3 * Q - S) * (3 * Q - S - 6 * T * β)) * u ^ 2 +
      (-(8 / 5103 : R) * β * (630 * Q ^ 2 - 420 * Q * S - 630 * Q * T * β + 70 * S ^ 2 + 189 * S * T * β - 135 * T * β)) * u +
      d20_U3 0 β S (Q - β * T) := by
    rw [d20_U3_eq, d20_U3_eq]; ring
  have hd21 : d21_U3 u (u / 3 + β) (S - u * T) (Q - (u / 3 + β) * T) =
      ((8 / 729 : R) * β * (3 * Q - S)) * u ^ 2 +
      (-(8 / 567 : R) * β ^ 2 * (70 * Q - 21 * S + 15)) * u +
      d21_U3 0 β S (Q - β * T) := by
    rw [d21_U3_eq, d21_U3_eq]; ring
  rw [hd10, hd20, hd21]
  have hd10_0 : d10_U3 0 β S (Q - β * T) =
      (8 / 5103 : R) * β * (3 * Q - S - 3 * T * β) * (210 * Q * S - 135 * Q - 77 * S ^ 2 - 210 * S * T * β - 45 * S + 135 * T * β - 270) := by
    rw [d10_U3_eq]; ring
  have hd20_0 : d20_U3 0 β S (Q - β * T) =
      (4 / 567 : R) * β ^ 2 * (140 * Q * S - 90 * Q - 49 * S ^ 2 - 140 * S * T * β + 90 * T * β - 90) := by
    rw [d20_U3_eq]; ring
  have hd21_0 : d21_U3 0 β S (Q - β * T) = (40 / 567 : R) * β ^ 3 * (14 * S - 9) := by
    rw [d21_U3_eq]; ring
  rw [hd10_0, hd20_0, hd21_0]
  ring

lemma A0V_U3_poly {R : Type*} [Field R] [CharZero R] (S Q T u : R)
    (hT : T ≠ 0) (hT59 : 5 * T - 9 ≠ 0) :
    let β : R := -(S - 3 * Q) * (5 * T - 3) / (3 * T * (5 * T - 9))
    A0V_Uk 3 u (u / 3 + β) (S - u * T) (Q - (u / 3 + β) * T) =
      ((73 / 7971615 : R) * (5 * T - 9) * (S - 3 * Q) ^ 2) * u ^ 3 +
      (A32_2_q_fn S Q T * (5 * T - 9) * (S - 3 * Q) / (14849347275 * (3 * T * (5 * T - 9)))) * u ^ 2 +
      (A32_1_q_fn S Q T * (5 * T - 9) * (S - 3 * Q) / (4949782425 * (3 * T * (5 * T - 9)) ^ 2)) * u +
      A0V_Uk 3 0 β S (Q - β * T) := by
  intro β
  rw [A0V_U3_poly_beta S Q T u β]
  have h3T : (3 : R) * T * (5 * T - 9) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by exact_mod_cast (by decide : (3 : ℕ) ≠ 0)) hT) hT59
  have h14849_ne : (14849347275 : R) ≠ 0 := by exact_mod_cast (by decide : (14849347275 : ℕ) ≠ 0)
  have h4949_ne : (4949782425 : R) ≠ 0 := by exact_mod_cast (by decide : (4949782425 : ℕ) ≠ 0)
  have hc2 :
      ((3 * Q - S) * (329432250 * Q ^ 2 - 225740725 * Q * S - 329432250 * Q * T * β + 7144200 * Q * T +
        592978050 * Q * β - 87606000 * Q + 38643325 * S ^ 2 + 97572300 * S * T * β - 2381400 * S * T -
        175630140 * S * β + 29202000 * S - 7144200 * T ^ 2 * β + 17860500 * T * β - 9001692 * β) / 44548041825) =
      A32_2_q_fn S Q T * (5 * T - 9) * (S - 3 * Q) / (14849347275 * (3 * T * (5 * T - 9))) := by
    have h445 : (44548041825 : R) = 3 * 14849347275 := by norm_num
    rw [h445, div_eq_div_iff (mul_ne_zero (by exact_mod_cast (by decide : (3 : ℕ) ≠ 0)) h14849_ne)
      (mul_ne_zero h14849_ne h3T)]
    have hβ : β * (3 * T * (5 * T - 9)) = -(S - 3 * Q) * (5 * T - 3) := div_mul_cancel₀ _ h3T
    have hmul :
        ((3 * Q - S) * (329432250 * Q ^ 2 - 225740725 * Q * S - 329432250 * Q * T * β + 7144200 * Q * T +
          592978050 * Q * β - 87606000 * Q + 38643325 * S ^ 2 + 97572300 * S * T * β - 2381400 * S * T -
          175630140 * S * β + 29202000 * S - 7144200 * T ^ 2 * β + 17860500 * T * β - 9001692 * β)) *
        (3 * T * (5 * T - 9)) =
        3 * (A32_2_q_fn S Q T * (5 * T - 9) * (S - 3 * Q)) := by
      have hpoly :
          (3 * Q - S) * ((329432250 * Q ^ 2 - 225740725 * Q * S + 7144200 * Q * T - 87606000 * Q +
            38643325 * S ^ 2 - 2381400 * S * T + 29202000 * S) * (3 * T * (5 * T - 9)) +
            (-329432250 * Q * T + 592978050 * Q + 97572300 * S * T - 175630140 * S -
              7144200 * T ^ 2 + 17860500 * T - 9001692) * (-(S - 3 * Q) * (5 * T - 3))) =
          3 * (A32_2_q_fn S Q T * (5 * T - 9) * (S - 3 * Q)) := by
        dsimp only [A32_2_q_fn]; ring
      linear_combination hpoly +
        (3 * Q - S) * (-329432250 * Q * T + 592978050 * Q + 97572300 * S * T - 175630140 * S -
          7144200 * T ^ 2 + 17860500 * T - 9001692) * hβ
    linear_combination (14849347275 : R) * hmul
  have hc1 :
      ((214326000 * Q ^ 3 - 658864500 * Q ^ 2 * S * β - 221470200 * Q ^ 2 * S - 428652000 * Q ^ 2 * T * β +
        1256829750 * Q ^ 2 * β - 45927000 * Q ^ 2 + 451481450 * Q * S ^ 2 * β + 76204800 * Q * S ^ 2 +
        658864500 * Q * S * T * β ^ 2 + 285768000 * Q * S * T * β - 1185956100 * Q * S * β ^ 2 -
        680535000 * Q * S * β + 30618000 * Q * S + 214326000 * Q * T ^ 2 * β ^ 2 - 1256829750 * Q * T * β ^ 2 +
        1567877310 * Q * β ^ 2 + 472054500 * Q * β - 77286650 * S ^ 3 * β - 8731800 * S ^ 3 -
        213502275 * S ^ 2 * T * β ^ 2 - 47628000 * S ^ 2 * T * β + 384304095 * S ^ 2 * β ^ 2 +
        87197250 * S ^ 2 * β - 5103000 * S ^ 2 - 64297800 * S * T ^ 2 * β ^ 2 + 401082750 * S * T * β ^ 2 -
        513624078 * S * β ^ 2 - 157351500 * S * β + 45927000 * T ^ 2 * β ^ 2 - 350844750 * T * β ^ 2 +
        482717070 * β ^ 2) / 14849347275) =
      A32_1_q_fn S Q T * (5 * T - 9) * (S - 3 * Q) / (4949782425 * (3 * T * (5 * T - 9)) ^ 2) := by
    have h148 : (14849347275 : R) = 3 * 4949782425 := by norm_num
    rw [h148, div_eq_div_iff (mul_ne_zero (by exact_mod_cast (by decide : (3 : ℕ) ≠ 0)) h4949_ne)
      (mul_ne_zero h4949_ne (pow_ne_zero 2 h3T))]
    have hβ : β * (3 * T * (5 * T - 9)) = -(S - 3 * Q) * (5 * T - 3) := div_mul_cancel₀ _ h3T
    have hβ2 : β ^ 2 * (3 * T * (5 * T - 9)) ^ 2 = (-(S - 3 * Q) * (5 * T - 3)) ^ 2 := by
      rw [← mul_pow, hβ]
    have hmul :
        (214326000 * Q ^ 3 - 658864500 * Q ^ 2 * S * β - 221470200 * Q ^ 2 * S - 428652000 * Q ^ 2 * T * β +
          1256829750 * Q ^ 2 * β - 45927000 * Q ^ 2 + 451481450 * Q * S ^ 2 * β + 76204800 * Q * S ^ 2 +
          658864500 * Q * S * T * β ^ 2 + 285768000 * Q * S * T * β - 1185956100 * Q * S * β ^ 2 -
          680535000 * Q * S * β + 30618000 * Q * S + 214326000 * Q * T ^ 2 * β ^ 2 - 1256829750 * Q * T * β ^ 2 +
          1567877310 * Q * β ^ 2 + 472054500 * Q * β - 77286650 * S ^ 3 * β - 8731800 * S ^ 3 -
          213502275 * S ^ 2 * T * β ^ 2 - 47628000 * S ^ 2 * T * β + 384304095 * S ^ 2 * β ^ 2 +
          87197250 * S ^ 2 * β - 5103000 * S ^ 2 - 64297800 * S * T ^ 2 * β ^ 2 + 401082750 * S * T * β ^ 2 -
          513624078 * S * β ^ 2 - 157351500 * S * β + 45927000 * T ^ 2 * β ^ 2 - 350844750 * T * β ^ 2 +
          482717070 * β ^ 2) * (3 * T * (5 * T - 9)) ^ 2 =
        3 * (A32_1_q_fn S Q T * (5 * T - 9) * (S - 3 * Q)) := by
      have hpoly :
          (214326000 * Q ^ 3 - 221470200 * Q ^ 2 * S - 45927000 * Q ^ 2 + 76204800 * Q * S ^ 2 +
            30618000 * Q * S - 8731800 * S ^ 3 - 5103000 * S ^ 2) * (3 * T * (5 * T - 9)) ^ 2 +
          (-658864500 * Q ^ 2 * S - 428652000 * Q ^ 2 * T + 1256829750 * Q ^ 2 + 451481450 * Q * S ^ 2 +
            285768000 * Q * S * T - 680535000 * Q * S + 472054500 * Q - 77286650 * S ^ 3 -
            47628000 * S ^ 2 * T + 87197250 * S ^ 2 - 157351500 * S) * (-(S - 3 * Q) * (5 * T - 3)) * (3 * T * (5 * T - 9)) +
          (658864500 * Q * S * T - 1185956100 * Q * S + 214326000 * Q * T ^ 2 - 1256829750 * Q * T +
            1567877310 * Q - 213502275 * S ^ 2 * T + 384304095 * S ^ 2 - 64297800 * S * T ^ 2 +
            401082750 * S * T - 513624078 * S + 45927000 * T ^ 2 - 350844750 * T + 482717070) *
            (-(S - 3 * Q) * (5 * T - 3)) ^ 2 =
          3 * (A32_1_q_fn S Q T * (5 * T - 9) * (S - 3 * Q)) := by
        dsimp only [A32_1_q_fn]; ring
      linear_combination hpoly +
        (-658864500 * Q ^ 2 * S - 428652000 * Q ^ 2 * T + 1256829750 * Q ^ 2 + 451481450 * Q * S ^ 2 +
          285768000 * Q * S * T - 680535000 * Q * S + 472054500 * Q - 77286650 * S ^ 3 -
          47628000 * S ^ 2 * T + 87197250 * S ^ 2 - 157351500 * S) * (3 * T * (5 * T - 9)) * hβ +
        (658864500 * Q * S * T - 1185956100 * Q * S + 214326000 * Q * T ^ 2 - 1256829750 * Q * T +
          1567877310 * Q - 213502275 * S ^ 2 * T + 384304095 * S ^ 2 - 64297800 * S * T ^ 2 +
          401082750 * S * T - 513624078 * S + 45927000 * T ^ 2 - 350844750 * T + 482717070) * hβ2
    linear_combination (4949782425 : R) * hmul
  rw [hc2, hc1]


lemma A0V_U3_lead3_eq {R : Type*} [Field R] [CharZero R] (S Q T aa ab b0 : R) :
    let f := fun z : R => A0V_Uk 3 (aa * z) (ab * z + b0) (S - aa * z * T) (Q - (ab * z + b0) * T)
    (f 2 - 3 * f 1 + 3 * f 0 - f (-1)) / 6 = A0V_U3_lead3_fn S Q T aa ab := by
  intro f
  let D10 : R → R := fun z => d10_U3 (aa * z) (ab * z + b0) (S - aa * z * T) (Q - (ab * z + b0) * T)
  let D20 : R → R := fun z => d20_U3 (aa * z) (ab * z + b0) (S - aa * z * T) (Q - (ab * z + b0) * T)
  let D21 : R → R := fun z => d21_U3 (aa * z) (ab * z + b0) (S - aa * z * T) (Q - (ab * z + b0) * T)
  let p10_1 : R := -(223 * aa - 450 * ab) / 2916
  let p10_0 : R := (11975 * b0 - 1134) / 77598
  let p20_1 : R := -(5 * T + 9) * (223 * aa - 450 * ab) / 14580
  let p20_0 : R := (-215550 * Q + 106817 * S + 215550 * T * b0 + 387990 * b0 - 51030) / 1396764
  let p21_1 : R := -T * (223 * aa - 450 * ab) / 1620
  let p21_0 : R := (-1077750 * Q + 534085 * S + 1077750 * T * b0 - 71442) / 3879900
  have hf_eq : ∀ z, f z = (p10_1 * z + p10_0) * D10 z + (p20_1 * z + p20_0) * D20 z + (p21_1 * z + p21_0) * D21 z := by
    intro z
    change A0V_Uk 3 (aa * z) (ab * z + b0) (S - aa * z * T) (Q - (ab * z + b0) * T) = _
    rw [A0V_Uk_eq 3]
    dsimp only [p10_1, p10_0, p20_1, p20_0, p21_1, p21_0, D10, D20, D21]
    ring
  have hsplit : (f 2 - 3 * f 1 + 3 * f 0 - f (-1)) / 6 =
      p10_1 * ((2 * D10 2 - 3 * D10 1 + D10 (-1)) / 6) + p10_0 * ((D10 2 - 3 * D10 1 + 3 * D10 0 - D10 (-1)) / 6) +
      p20_1 * ((2 * D20 2 - 3 * D20 1 + D20 (-1)) / 6) + p20_0 * ((D20 2 - 3 * D20 1 + 3 * D20 0 - D20 (-1)) / 6) +
      p21_1 * ((2 * D21 2 - 3 * D21 1 + D21 (-1)) / 6) + p21_0 * ((D21 2 - 3 * D21 1 + 3 * D21 0 - D21 (-1)) / 6) := by
    rw [hf_eq 2, hf_eq 1, hf_eq 0, hf_eq (-1)]
    have h1 := diff3_lin_mul p10_1 p10_0 D10
    have h2 := diff3_lin_mul p20_1 p20_0 D20
    have h3 := diff3_lin_mul p21_1 p21_0 D21
    dsimp only at h1 h2 h3
    linear_combination h1 + h2 + h3
  have hd10_d : (D10 2 - 3 * D10 1 + 3 * D10 0 - D10 (-1)) / 6 =
      -(8 / 5103 : R) * T ^ 2 * (aa - 3 * ab) *
        (77 * Q * aa ^ 2 - 210 * Q * aa * ab - 77 * S * aa * ab + 210 * S * ab ^ 2 + 45 * aa * ab - 135 * ab ^ 2) := by
    dsimp only [D10]; simp only [d10_U3_eq]; ring
  have hd10_w : (2 * D10 2 - 3 * D10 1 + D10 (-1)) / 6 =
      (8 / 5103 : R) * T * (-441 * Q ^ 2 * aa ^ 2 + 1260 * Q ^ 2 * aa * ab + 154 * Q * S * aa ^ 2 - 1260 * Q * S * ab ^ 2 -
        154 * Q * T * aa ^ 3 + 882 * Q * T * aa ^ 2 * ab + 441 * Q * T * aa ^ 2 * b0 - 1260 * Q * T * aa * ab ^ 2 -
        1260 * Q * T * aa * ab * b0 + 90 * Q * aa ^ 2 - 540 * Q * aa * ab + 810 * Q * ab ^ 2 - 154 * S ^ 2 * aa * ab +
        441 * S ^ 2 * ab ^ 2 + 154 * S * T * aa ^ 2 * ab + 77 * S * T * aa ^ 2 * b0 - 882 * S * T * aa * ab ^ 2 -
        882 * S * T * aa * ab * b0 + 1260 * S * T * ab ^ 3 + 1890 * S * T * ab ^ 2 * b0 - 90 * T * aa ^ 2 * ab -
        45 * T * aa ^ 2 * b0 + 540 * T * aa * ab ^ 2 + 540 * T * aa * ab * b0 - 810 * T * ab ^ 3 -
        1215 * T * ab ^ 2 * b0 + 90 * aa ^ 2 - 540 * aa * ab + 810 * ab ^ 2) := by
    dsimp only [D10]; simp only [d10_U3_eq]; ring
  have hd20_d : (D20 2 - 3 * D20 1 + 3 * D20 0 - D20 (-1)) / 6 =
      (8 / 5103 : R) * T * (aa - 3 * ab) *
        (77 * Q * aa ^ 2 - 210 * Q * aa * ab - 77 * S * aa * ab + 210 * S * ab ^ 2 + 45 * aa * ab - 135 * ab ^ 2) := by
    dsimp only [D20]; simp only [d20_U3_eq]; ring
  have hd20_w : (2 * D20 2 - 3 * D20 1 + D20 (-1)) / 6 =
      -(4 / 5103 : R) * (-441 * Q ^ 2 * aa ^ 2 + 1260 * Q ^ 2 * aa * ab + 154 * Q * S * aa ^ 2 - 1260 * Q * S * ab ^ 2 -
        308 * Q * T * aa ^ 3 + 1764 * Q * T * aa ^ 2 * ab + 882 * Q * T * aa ^ 2 * b0 - 2520 * Q * T * aa * ab ^ 2 -
        2520 * Q * T * aa * ab * b0 + 90 * Q * aa ^ 2 - 540 * Q * aa * ab + 810 * Q * ab ^ 2 - 154 * S ^ 2 * aa * ab +
        441 * S ^ 2 * ab ^ 2 + 308 * S * T * aa ^ 2 * ab + 154 * S * T * aa ^ 2 * b0 - 1764 * S * T * aa * ab ^ 2 -
        1764 * S * T * aa * ab * b0 + 2520 * S * T * ab ^ 3 + 3780 * S * T * ab ^ 2 * b0 - 180 * T * aa ^ 2 * ab -
        90 * T * aa ^ 2 * b0 + 1080 * T * aa * ab ^ 2 + 1080 * T * aa * ab * b0 - 1620 * T * ab ^ 3 -
        2430 * T * ab ^ 2 * b0 + 90 * aa ^ 2 - 540 * aa * ab + 810 * ab ^ 2) := by
    dsimp only [D20]; simp only [d20_U3_eq]; ring
  have hd21_d : (D21 2 - 3 * D21 1 + 3 * D21 0 - D21 (-1)) / 6 =
      -(8 / 5103 : R) * (aa - 3 * ab) *
        (77 * Q * aa ^ 2 - 210 * Q * aa * ab - 77 * S * aa * ab + 210 * S * ab ^ 2 + 45 * aa * ab - 135 * ab ^ 2) := by
    dsimp only [D21]; simp only [d21_U3_eq]; ring
  have hd21_w : (2 * D21 2 - 3 * D21 1 + D21 (-1)) / 6 =
      (8 / 5103 : R) * (-154 * Q * aa ^ 3 + 882 * Q * aa ^ 2 * ab + 441 * Q * aa ^ 2 * b0 - 1260 * Q * aa * ab ^ 2 -
        1260 * Q * aa * ab * b0 + 154 * S * aa ^ 2 * ab + 77 * S * aa ^ 2 * b0 - 882 * S * aa * ab ^ 2 -
        882 * S * aa * ab * b0 + 1260 * S * ab ^ 3 + 1890 * S * ab ^ 2 * b0 - 90 * aa ^ 2 * ab -
        45 * aa ^ 2 * b0 + 540 * aa * ab ^ 2 + 540 * aa * ab * b0 - 810 * ab ^ 3 - 1215 * ab ^ 2 * b0) := by
    dsimp only [D21]; simp only [d21_U3_eq]; ring
  rw [hsplit, hd10_d, hd10_w, hd20_d, hd20_w, hd21_d, hd21_w]
  dsimp only [p10_1, p10_0, p20_1, p20_0, p21_1, p21_0, A0V_U3_lead3_fn]
  ring

lemma A0V_U2_lead3_at_third {R : Type*} [Field R] [CharZero R] (S Q T aa b0 : R) :
    let f := fun z : R => A0V_Uk 2 (aa * z) ((aa / 3) * z + b0) (S - aa * z * T) (Q - ((aa / 3) * z + b0) * T)
    (f 2 - 3 * f 1 + 3 * f 0 - f (-1)) / 6 =
      aa ^ 3 * ((1 / 53457650190 : R) * (5 * T - 9) *
        (-50137409 * S ^ 2 + 300824454 * S * Q - 451236681 * Q ^ 2 - 10001880 * S * T +
         30005640 * Q * T - 45873099 * S + 137619297 * Q - 10103940 * T + 58998753)) := by
  intro f
  let D10 : R → R := fun z => d10_U2 (aa * z) ((aa / 3) * z + b0) (S - aa * z * T) (Q - ((aa / 3) * z + b0) * T)
  let D20 : R → R := fun z => d20_U2 (aa * z) ((aa / 3) * z + b0) (S - aa * z * T) (Q - ((aa / 3) * z + b0) * T)
  let D21 : R → R := fun z => d21_U2 (aa * z) ((aa / 3) * z + b0) (S - aa * z * T) (Q - ((aa / 3) * z + b0) * T)
  let p10_1 : R := -(73 / 2916 : R) * aa
  let p10_0 : R := (11975 * b0 - 1134) / 77598
  let p20_1 : R := -(73 / 14580 : R) * aa * (5 * T + 9)
  let p20_0 : R := (-215550 * Q + 106817 * S + 215550 * T * b0 + 387990 * b0 - 51030) / 1396764
  let p21_1 : R := -(73 / 1620 : R) * T * aa
  let p21_0 : R := (-1077750 * Q + 534085 * S + 1077750 * T * b0 - 71442) / 3879900
  have hf_eq : ∀ z, f z = (p10_1 * z + p10_0) * D10 z + (p20_1 * z + p20_0) * D20 z + (p21_1 * z + p21_0) * D21 z := by
    intro z
    change A0V_Uk 2 (aa * z) ((aa / 3) * z + b0) (S - aa * z * T) (Q - ((aa / 3) * z + b0) * T) = _
    rw [A0V_Uk_eq 2]
    dsimp only [p10_1, p10_0, p20_1, p20_0, p21_1, p21_0, D10, D20, D21]
    ring
  have hsplit : (f 2 - 3 * f 1 + 3 * f 0 - f (-1)) / 6 =
      p10_1 * ((2 * D10 2 - 3 * D10 1 + D10 (-1)) / 6) + p10_0 * ((D10 2 - 3 * D10 1 + 3 * D10 0 - D10 (-1)) / 6) +
      p20_1 * ((2 * D20 2 - 3 * D20 1 + D20 (-1)) / 6) + p20_0 * ((D20 2 - 3 * D20 1 + 3 * D20 0 - D20 (-1)) / 6) +
      p21_1 * ((2 * D21 2 - 3 * D21 1 + D21 (-1)) / 6) + p21_0 * ((D21 2 - 3 * D21 1 + 3 * D21 0 - D21 (-1)) / 6) := by
    rw [hf_eq 2, hf_eq 1, hf_eq 0, hf_eq (-1)]
    have h1 := diff3_lin_mul p10_1 p10_0 D10
    have h2 := diff3_lin_mul p20_1 p20_0 D20
    have h3 := diff3_lin_mul p21_1 p21_0 D21
    dsimp only at h1 h2 h3
    linear_combination h1 + h2 + h3
  have hd10_d : (D10 2 - 3 * D10 1 + 3 * D10 0 - D10 (-1)) / 6 =
      -(10 / 15309 : R) * T ^ 2 * aa ^ 3 * (294 * Q - 98 * S - 99) := by
    dsimp only [D10]; simp only [d10_U2_eq]; ring
  have hd10_w : (2 * D10 2 - 3 * D10 1 + D10 (-1)) / 6 =
      -(2 / 15309 : R) * T * aa ^ 2 * (-7686 * Q ^ 2 + 2184 * Q * S + 2940 * Q * T * aa + 7686 * Q * T * b0 +
        2970 * Q + 126 * S ^ 2 - 980 * S * T * aa - 4032 * S * T * b0 - 990 * T * aa + 9315 * T * b0 + 2970) := by
    dsimp only [D10]; simp only [d10_U2_eq]; ring
  have hd20_d : (D20 2 - 3 * D20 1 + 3 * D20 0 - D20 (-1)) / 6 =
      (10 / 15309 : R) * T * aa ^ 3 * (294 * Q - 98 * S - 99) := by
    dsimp only [D20]; simp only [d20_U2_eq]; ring
  have hd20_w : (2 * D20 2 - 3 * D20 1 + D20 (-1)) / 6 =
      (2 / 15309 : R) * aa ^ 2 * (-3843 * Q ^ 2 + 1092 * Q * S + 2940 * Q * T * aa + 7686 * Q * T * b0 +
        1485 * Q + 63 * S ^ 2 - 980 * S * T * aa - 4032 * S * T * b0 - 990 * T * aa + 9315 * T * b0 + 1485) := by
    dsimp only [D20]; simp only [d20_U2_eq]; ring
  have hd21_d : (D21 2 - 3 * D21 1 + 3 * D21 0 - D21 (-1)) / 6 =
      -(10 / 15309 : R) * aa ^ 3 * (294 * Q - 98 * S - 99) := by
    dsimp only [D21]; simp only [d21_U2_eq]; ring
  have hd21_w : (2 * D21 2 - 3 * D21 1 + D21 (-1)) / 6 =
      -(2 / 15309 : R) * aa ^ 2 * (2940 * Q * aa + 7686 * Q * b0 - 980 * S * aa - 4032 * S * b0 - 990 * aa + 9315 * b0) := by
    dsimp only [D21]; simp only [d21_U2_eq]; ring
  rw [hsplit, hd10_d, hd10_w, hd20_d, hd20_w, hd21_d, hd21_w]
  dsimp only [p10_1, p10_0, p20_1, p20_0, p21_1, p21_0]
  ring

lemma AX_U3_lead3_at_third {R : Type*} [Field R] [CharZero R] (S Q T aa b0 : R) :
    let f := fun z : R => AX_Uk 3 (aa * z) ((aa / 3) * z + b0) (S - aa * z * T) (Q - ((aa / 3) * z + b0) * T)
    (f 2 - 3 * f 1 + 3 * f 0 - f (-1)) / 6 =
      aa ^ 3 * ((2 / 885735 : R) * (5 * T - 9) * (S - 3 * Q) ^ 2) := by
  intro f
  let D10 : R → R := fun z => d10_U3 (aa * z) ((aa / 3) * z + b0) (S - aa * z * T) (Q - ((aa / 3) * z + b0) * T)
  let D20 : R → R := fun z => d20_U3 (aa * z) ((aa / 3) * z + b0) (S - aa * z * T) (Q - ((aa / 3) * z + b0) * T)
  let D21 : R → R := fun z => d21_U3 (aa * z) ((aa / 3) * z + b0) (S - aa * z * T) (Q - ((aa / 3) * z + b0) * T)
  let p10_1 : R := -(1 / 162 : R) * aa
  let p10_0 : R := -(119 / 5748 : R)
  let p20_1 : R := -(1 / 810 : R) * aa * (5 * T + 9)
  let p20_0 : R := (479 * S - 7560) / 77598
  let p21_1 : R := -(1 / 90 : R) * T * aa
  let p21_0 : R := (4790 * S - 46683) / 431100
  have hf_eq : ∀ z, f z = (p10_1 * z + p10_0) * D10 z + (p20_1 * z + p20_0) * D20 z + (p21_1 * z + p21_0) * D21 z := by
    intro z
    change AX_Uk 3 (aa * z) ((aa / 3) * z + b0) (S - aa * z * T) (Q - ((aa / 3) * z + b0) * T) = _
    rw [AX_Uk_eq 3]
    dsimp only [p10_1, p10_0, p20_1, p20_0, p21_1, p21_0, D10, D20, D21]
    ring
  have hsplit : (f 2 - 3 * f 1 + 3 * f 0 - f (-1)) / 6 =
      p10_1 * ((2 * D10 2 - 3 * D10 1 + D10 (-1)) / 6) + p10_0 * ((D10 2 - 3 * D10 1 + 3 * D10 0 - D10 (-1)) / 6) +
      p20_1 * ((2 * D20 2 - 3 * D20 1 + D20 (-1)) / 6) + p20_0 * ((D20 2 - 3 * D20 1 + 3 * D20 0 - D20 (-1)) / 6) +
      p21_1 * ((2 * D21 2 - 3 * D21 1 + D21 (-1)) / 6) + p21_0 * ((D21 2 - 3 * D21 1 + 3 * D21 0 - D21 (-1)) / 6) := by
    rw [hf_eq 2, hf_eq 1, hf_eq 0, hf_eq (-1)]
    have h1 := diff3_lin_mul p10_1 p10_0 D10
    have h2 := diff3_lin_mul p20_1 p20_0 D20
    have h3 := diff3_lin_mul p21_1 p21_0 D21
    dsimp only at h1 h2 h3
    linear_combination h1 + h2 + h3
  have hd10_d : (D10 2 - 3 * D10 1 + 3 * D10 0 - D10 (-1)) / 6 = 0 := by
    dsimp only [D10]; simp only [d10_U3_eq]; ring
  have hd10_w : (2 * D10 2 - 3 * D10 1 + D10 (-1)) / 6 =
      (8 / 2187 : R) * T * aa ^ 2 * (3 * Q - S) * (-3 * Q + S + 3 * T * b0) := by
    dsimp only [D10]; simp only [d10_U3_eq]; ring
  have hd20_d : (D20 2 - 3 * D20 1 + 3 * D20 0 - D20 (-1)) / 6 = 0 := by
    dsimp only [D20]; simp only [d20_U3_eq]; ring
  have hd20_w : (2 * D20 2 - 3 * D20 1 + D20 (-1)) / 6 =
      -(4 / 2187 : R) * aa ^ 2 * (3 * Q - S) * (-3 * Q + S + 6 * T * b0) := by
    dsimp only [D20]; simp only [d20_U3_eq]; ring
  have hd21_d : (D21 2 - 3 * D21 1 + 3 * D21 0 - D21 (-1)) / 6 = 0 := by
    dsimp only [D21]; simp only [d21_U3_eq]; ring
  have hd21_w : (2 * D21 2 - 3 * D21 1 + D21 (-1)) / 6 =
      (8 / 729 : R) * aa ^ 2 * b0 * (3 * Q - S) := by
    dsimp only [D21]; simp only [d21_U3_eq]; ring
  rw [hsplit, hd10_d, hd10_w, hd20_d, hd20_w, hd21_d, hd21_w]
  dsimp only [p10_1, p10_0, p20_1, p20_0, p21_1, p21_0]
  ring

lemma M01_dual_combine {R : Type*} [Field R] [CharZero R] (S Q T : R) :
    let Bv1 : R := (143 / 243 : R) * S ^ 3 - (92 / 27) * S ^ 2 * Q + (52 / 9) * S * Q ^ 2 - (22 / 9) * Q ^ 3 +
      (143 / 243) * T ^ 3 - (92 / 27) * T ^ 2 + (52 / 9) * T - (22 / 9) + (5 / 7) * Q ^ 2 + (10 / 7) * Q
    let w1w0_sc : R := (243 / 4 : R) * Bv1
    let rb_sc : R := -(3 / 28 : R) * (S - 3 * Q) * (119 * S ^ 2 - 560 * S * Q + 630 * Q ^ 2 + 90 * Q + 90)
    let c0 : R := (73 / 7971615 : R) * (5 * T - 9) * (S - 3 * Q) ^ 2
    let dc0 : R := -(2 / 2121335325 : R) * (5 * T - 9) * (-464630 * S + 1568725 * Q + 34020 * T - 23814) * (-S + 3 * Q)
    let c2 : R := (1 / 53457650190 : R) * (5 * T - 9) *
      (-50137409 * S ^ 2 + 300824454 * S * Q - 451236681 * Q ^ 2 - 10001880 * S * T +
       30005640 * Q * T - 45873099 * S + 137619297 * Q - 10103940 * T + 58998753);
    -2 * w1w0_sc * c0 + (rb_sc / 3) * dc0 + (S - 3 * Q) ^ 3 * c2 =
      M01_q_fn S Q T * (5 * T - 9) * (S - 3 * Q) / 267288250950 := by
  dsimp only [M01_q_fn]; ring

lemma A0V_U3_lead3_dual {R : Type*} [Field R] [CharZero R] (S Q T r1 : R) :
    let c0 : R := (73 / 7971615 : R) * (5 * T - 9) * (S - 3 * Q) ^ 2
    let dc0 : R := -(2 / 2121335325 : R) * (5 * T - 9) * (-464630 * S + 1568725 * Q + 34020 * T - 23814) * (-S + 3 * Q)
    (-(1 / 4949782425 : R) * (5 * T - 9) *
      (-7728665 * Q ^ 2 - 1746360 * Q * T + 15457330 * S * Q * (1 / 3 : R) +
       21962150 * Q ^ 2 * (1 / 3) + 1746360 * S * T * (1 / 3) + 10001880 * Q * T * (1 / 3) -
       7728665 * S ^ 2 * (1 / 3) ^ 2 - 43924300 * S * Q * (1 / 3) ^ 2 - 10001880 * S * T * (1 / 3) ^ 2 -
       14288400 * Q * T * (1 / 3) ^ 2 + 21962150 * S ^ 2 * (1 / 3) ^ 3 + 14288400 * S * T * (1 / 3) ^ 3 +
       6563302 * Q - 6563302 * S * (1 / 3) - 39046416 * Q * (1 / 3) -
       1020600 * T * (1 / 3) + 39046416 * S * (1 / 3) ^ 2 + 58069530 * Q * (1 / 3) ^ 2 +
       6123600 * T * (1 / 3) ^ 2 - 58069530 * S * (1 / 3) ^ 3 - 9185400 * T * (1 / 3) ^ 3 +
       5340850 - 42108180 * (1 / 3) + 108446130 * (1 / 3) ^ 2 - 90567720 * (1 / 3) ^ 3) = c0) ∧
    (-(1 / 4949782425 : R) * (5 * T - 9) *
      ((15457330 * S * Q + 21962150 * Q ^ 2 + 1746360 * S * T + 10001880 * Q * T -
        6563302 * S - 39046416 * Q - 1020600 * T - 42108180) +
       2 * (-7728665 * S ^ 2 - 43924300 * S * Q - 10001880 * S * T - 14288400 * Q * T +
        39046416 * S + 58069530 * Q + 6123600 * T + 108446130) * (1 / 3 : R) +
       3 * (21962150 * S ^ 2 + 14288400 * S * T - 58069530 * S - 9185400 * T - 90567720) * (1 / 3 : R) ^ 2) * r1 =
      dc0 * r1) := by
  dsimp only; constructor <;> ring


private theorem localInf_lead3_alg_proof : LocalInfLead3AlgSpec :=
  ⟨fun S Q T u hT hT59 => A0V_U3_poly S Q T u hT hT59,
   fun S Q T aa ab b0 => A0V_U3_lead3_eq S Q T aa ab b0,
   fun S Q T aa b0 => A0V_U2_lead3_at_third S Q T aa b0,
   fun S Q T aa b0 => AX_U3_lead3_at_third S Q T aa b0,
   fun S Q T => M01_dual_combine S Q T,
   fun S Q T r1 => A0V_U3_lead3_dual S Q T r1⟩

end SymmetricSexticResidual.LocalResidueInfAlg

theorem solution : SymmetricSexticResidual.LocalResidueInfAlg.LocalInfLead3AlgSpec :=
  SymmetricSexticResidual.LocalResidueInfAlg.localInf_lead3_alg_proof
