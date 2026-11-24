-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localInf_sheet_splits
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T16:58:45.239997+00:00
-- url     : https://prove2.me/submissions/88889bd3-db24-492c-b801-e653c21d2e81

import Definitions.Def_HodgeComputerSSR_SheetCalculus
import Definitions.Def_HodgeComputerSSR_LocalInfAlgDefs
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

namespace SymmetricSexticResidual.LocalResidueInfAlg
open SymmetricSexticResidual.SheetCalculus QuadraticCovers

lemma minor_split_UV {R : Type*} [Field R] [CharZero R] (s1 q1 v1 s2 q2 v2 U V : R) :
    dH_dS s1 q1 U V * dH_dQ s2 q2 v2 U V - dH_dS s2 q2 U V * dH_dQ s1 q1 v1 U V =
      V ^ 2 * (U ^ 3 * minor_U3 s1 q1 v1 s2 q2 v2 + U ^ 2 * minor_U2 s1 q1 v1 s2 q2 v2 +
               U * minor_U1 s1 q1 v1 s2 q2 v2 + minor_U0 s1 q1 s2 q2) := by
  simp only [dH_dS, dH_dQ, minor_U3, minor_U2, minor_U1, minor_U0,
    dHS_2, dHS_1, dHS_0, dHQ_1, dHQ_0]; ring


lemma numM_split_UV {R : Type*} [Field R] [CharZero R] (mi : Fin 10) (a b xS xQ U V : R) :
    numM mi a b xS xQ U V =
      V ^ 2 * (U ^ 3 * numM_Uk 3 mi a b xS xQ + U ^ 2 * numM_Uk 2 mi a b xS xQ +
               U * numM_Uk 1 mi a b xS xQ + numM_Uk 0 mi a b xS xQ) := by
  have hd20 : q1_a2 a b U V * q2_b0 xS xQ U V - q1_a0 xS xQ U V * q2_b2 a b U V =
      V ^ 2 * (U ^ 3 * d20_U3 a b xS xQ + U ^ 2 * d20_U2 a b xS xQ +
               U * d20_U1 a b xS xQ + d20_U0 a b xS xQ) :=
    minor_split_UV a b 0 xS xQ 1 U V
  have hd21 : q1_a2 a b U V * q2_b1 a b xS xQ U V - q1_a1 a b xS xQ U V * q2_b2 a b U V =
      V ^ 2 * (U ^ 3 * d21_U3 a b xS xQ + U ^ 2 * d21_U2 a b xS xQ +
               U * d21_U1 a b xS xQ + d21_U0 a b xS xQ) := by
    have hm1 := minor_split_UV a b 0 (a + xS) (b + xQ) 0 U V
    have hm2 := minor_split_UV a b 0 xS xQ 0 U V
    have hre : q1_a2 a b U V * q2_b1 a b xS xQ U V - q1_a1 a b xS xQ U V * q2_b2 a b U V =
        (dH_dS a b U V * dH_dQ (a + xS) (b + xQ) 0 U V - dH_dS (a + xS) (b + xQ) U V * dH_dQ a b 0 U V) -
        (dH_dS a b U V * dH_dQ xS xQ 0 U V - dH_dS xS xQ U V * dH_dQ a b 0 U V) +
        (10 / 7 : R) * b * U * V * dH_dS a b U V := by
      simp only [q1_a2, q1_a1, q2_b2, q2_b1]; ring
    rw [hre, hm1, hm2]
    simp only [d21_U3, d21_U2, d21_U1, d21_U0, dH_dS, dHS_2, dHS_1, dHS_0]; ring
  have hd10 : q1_a1 a b xS xQ U V * q2_b0 xS xQ U V - q1_a0 xS xQ U V * q2_b1 a b xS xQ U V =
      V ^ 2 * (U ^ 3 * d10_U3 a b xS xQ + U ^ 2 * d10_U2 a b xS xQ +
               U * d10_U1 a b xS xQ + d10_U0 a b xS xQ) := by
    have hm1 := minor_split_UV (a + xS) (b + xQ) 0 xS xQ 1 U V
    have hm2 := minor_split_UV a b 0 xS xQ 1 U V
    have hm3 := minor_split_UV xS xQ 0 xS xQ 1 U V
    have hre : q1_a1 a b xS xQ U V * q2_b0 xS xQ U V - q1_a0 xS xQ U V * q2_b1 a b xS xQ U V =
        (dH_dS (a + xS) (b + xQ) U V * dH_dQ xS xQ 1 U V - dH_dS xS xQ U V * dH_dQ (a + xS) (b + xQ) 0 U V) -
        (dH_dS a b U V * dH_dQ xS xQ 1 U V - dH_dS xS xQ U V * dH_dQ a b 0 U V) -
        (dH_dS xS xQ U V * dH_dQ xS xQ 1 U V - dH_dS xS xQ U V * dH_dQ xS xQ 0 U V) -
        (10 / 7 : R) * b * U * V * dH_dS xS xQ U V := by
      simp only [q1_a1, q1_a0, q2_b1, q2_b0]; ring
    rw [hre, hm1, hm2, hm3]
    simp only [d10_U3, d10_U2, d10_U1, d10_U0, dH_dS, dHS_2, dHS_1, dHS_0]; ring
  fin_cases mi <;> (simp only [numM, numM_Uk]; rw [hd20, hd21, hd10]; ring)

lemma AY_t3_U3_eq_zero {R : Type*} [Field R] [CharZero R] (a b xS xQ : R) :
    -(123236 / 24249375 : R) * (numM_Uk 3 0 a b xS xQ + (2790 / 77) * numM_Uk 3 6 a b xS xQ +
      28 * numM_Uk 3 8 a b xS xQ - (5904 / 77) * numM_Uk 3 9 a b xS xQ) +
    (492944 / 33949125) * (numM_Uk 3 1 a b xS xQ + (927 / 77) * numM_Uk 3 6 a b xS xQ +
      (49 / 5) * numM_Uk 3 8 a b xS xQ - (21159 / 770) * numM_Uk 3 9 a b xS xQ) = 0 := by
  simp only [numM_Uk, d10_U3, d20_U3, d21_U3, minor_U3, dHS_2, dHS_1, dHQ_1]; ring


lemma A_0V_split_UV {R : Type*} [Field R] [CharZero R] (a b xS xQ U V : R) :
    A_0V a b xS xQ U V =
      V ^ 2 * (U ^ 3 * A0V_Uk 3 a b xS xQ + U ^ 2 * A0V_Uk 2 a b xS xQ +
               U * A0V_Uk 1 a b xS xQ + A0V_Uk 0 a b xS xQ) := by
  simp only [A_0V, A0V_Uk, numM_split_UV]; ring

lemma A_X_split_UV {R : Type*} [Field R] [CharZero R] (a b xS xQ U V : R) :
    A_X a b xS xQ U V =
      U * V ^ 2 * (U ^ 3 * AX_Uk 3 a b xS xQ + U ^ 2 * AX_Uk 2 a b xS xQ +
                   U * AX_Uk 1 a b xS xQ + AX_Uk 0 a b xS xQ) := by
  simp only [A_X, AX_Uk, numM_split_UV]; ring

-- Compact factored forms for `d20/d21/d10` at `U3` and `U2`, and linear decomposition of `A0V_Uk`/`AX_Uk`:

lemma br_10_eq {R : Type*} [Field R] [CharZero R] (k : Fin 5) (S Q T x y : R) :
    243 * (br_fn k S Q T x y 1 0 - br_fn k S Q T x y 0 0) =
      match k with
      | 0 => -5 * T * (5 * T - 9) * (9 * x - 25 * S + 15 * Q)
      | 1 => -150 * T * (5 * T - 9) * S
      | 2 => 5 * (5 * T - 3) * (27 * x - 25 * S + 45 * Q) * S
      | 3 => -90 * T * (5 * T - 9) * S
      | 4 => 0 := by
  fin_cases k <;> (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, br_fn, LX_of, LY_of,
    dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of]; ring)

lemma br_00_eq {R : Type*} [Field R] [CharZero R] (k : Fin 5) (S Q T x y : R) :
    243 * br_fn k S Q T x y 0 0 =
      match k with
      | 0 => 25 * T * (5 * T - 9) * (-5 * S + 3 * Q)
      | 1 => 150 * T * (5 * T - 9) * S
      | 2 => -25 * (5 * T - 3) * (-5 * S + 9 * Q) * S
      | 3 => 0
      | 4 => 0 := by
  fin_cases k <;> (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, br_fn, LX_of, LY_of,
    dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of]; ring)

lemma br_11_eq {R : Type*} [Field R] [CharZero R] (k : Fin 5) (S Q T x y : R) :
    243 * (br_fn k S Q T x y 1 1 - br_fn k S Q T x y 1 0 - br_fn k S Q T x y 0 1 + br_fn k S Q T x y 0 0) =
      match k with
      | 0 => -(27 * y - 25 * T + 45) * T * (9 * x - 25 * S + 15 * Q)
      | 1 => -30 * (27 * y - 25 * T + 45) * T * S
      | 2 => (9 * y - 25 * T + 15) * (27 * x - 25 * S + 45 * Q) * S
      | 3 => -18 * (27 * y - 25 * T + 45) * T * S
      | 4 => 18 * T * (27 * x - 25 * S + 45 * Q) * S := by
  fin_cases k <;> (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, br_fn, LX_of, LY_of,
    dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of]; ring)

lemma om_10_eq {R : Type*} [Field R] [CharZero R] (i j : Fin 5) (S Q T x y : R) :
    81 * (om_fn i j S Q T x y 1 0 - om_fn i j S Q T x y 0 0) =
      let f : Fin 5 → Fin 5 → R := fun p q => match p, q with
        | 0, 2 => 5 * (5 * T - 3) * (9 * x - 25 * S + 15 * Q)
        | 1, 2 => 150 * (5 * T - 3) * S
        | 2, 3 => -90 * (5 * T - 3) * S
        | _, _ => 0
      f i j - f j i := by
  fin_cases i <;> fin_cases j <;> (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, om_fn]; ring)

lemma om_00_eq {R : Type*} [Field R] [CharZero R] (i j : Fin 5) (S Q T x y : R) :
    81 * om_fn i j S Q T x y 0 0 =
      let f : Fin 5 → Fin 5 → R := fun p q => match p, q with
        | 0, 2 => -25 * (5 * T - 3) * (-5 * S + 3 * Q)
        | 1, 2 => -150 * (5 * T - 3) * S
        | _, _ => 0
      f i j - f j i := by
  fin_cases i <;> fin_cases j <;> (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, om_fn]; ring)

lemma om_11_eq {R : Type*} [Field R] [CharZero R] (i j : Fin 5) (S Q T x y : R) :
    81 * (om_fn i j S Q T x y 1 1 - om_fn i j S Q T x y 1 0 - om_fn i j S Q T x y 0 1 + om_fn i j S Q T x y 0 0) =
      let f : Fin 5 → Fin 5 → R := fun p q => match p, q with
        | 0, 2 => (9 * y - 25 * T + 15) * (9 * x - 25 * S + 15 * Q)
        | 0, 4 => 18 * T * (9 * x - 25 * S + 15 * Q)
        | 1, 2 => 30 * (9 * y - 25 * T + 15) * S
        | 1, 4 => 540 * T * S
        | 2, 3 => -18 * (9 * y - 25 * T + 15) * S
        | 3, 4 => 324 * T * S
        | _, _ => 0
      f i j - f j i := by
  fin_cases i <;> fin_cases j <;> (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, om_fn]; ring)

lemma QY_10_u1_zero {R : Type*} [Field R] [CharZero R] (S Q T x y : R) :
    3 * (QY_num S Q T x y 1 0 0 - QY_num S Q T x y 0 0 0) +
    (QY_num S Q T x y 1 0 1 - QY_num S Q T x y 0 0 1) = 0 := by
  have hb0 : br_fn 0 S Q T x y 1 0 = br_fn 0 S Q T x y 0 0 + (-5 * T * (5 * T - 9) * (9 * x - 25 * S + 15 * Q)) / 243 := by
    have h := br_10_eq 0 S Q T x y; dsimp only at h; linear_combination (1 / 243 : R) * h
  have hb1 : br_fn 1 S Q T x y 1 0 = br_fn 1 S Q T x y 0 0 + (-150 * T * (5 * T - 9) * S) / 243 := by
    have h := br_10_eq 1 S Q T x y; dsimp only at h; linear_combination (1 / 243 : R) * h
  have hb3 : br_fn 3 S Q T x y 1 0 = br_fn 3 S Q T x y 0 0 + (-90 * T * (5 * T - 9) * S) / 243 := by
    have h := br_10_eq 3 S Q T x y; dsimp only at h; linear_combination (1 / 243 : R) * h
  have hb4 : br_fn 4 S Q T x y 1 0 = br_fn 4 S Q T x y 0 0 := by
    have h := br_10_eq 4 S Q T x y; dsimp only at h; linear_combination (1 / 243 : R) * h
  have ho03 : om_fn 0 3 S Q T x y 1 0 = om_fn 0 3 S Q T x y 0 0 := by
    have h := om_10_eq 0 3 S Q T x y; dsimp only at h; linear_combination (1 / 81 : R) * h
  have ho40 : om_fn 4 0 S Q T x y 1 0 = om_fn 4 0 S Q T x y 0 0 := by
    have h := om_10_eq 4 0 S Q T x y; dsimp only at h; linear_combination (1 / 81 : R) * h
  have ho34 : om_fn 3 4 S Q T x y 1 0 = om_fn 3 4 S Q T x y 0 0 := by
    have h := om_10_eq 3 4 S Q T x y; dsimp only at h; linear_combination (1 / 81 : R) * h
  have ho13 : om_fn 1 3 S Q T x y 1 0 = om_fn 1 3 S Q T x y 0 0 := by
    have h := om_10_eq 1 3 S Q T x y; dsimp only at h; linear_combination (1 / 81 : R) * h
  have ho41 : om_fn 4 1 S Q T x y 1 0 = om_fn 4 1 S Q T x y 0 0 := by
    have h := om_10_eq 4 1 S Q T x y; dsimp only at h; linear_combination (1 / 81 : R) * h
  have hd4 : dDX2_fn 4 S Q x = 0 := rfl
  have hcore :
      3 * (dDX2_fn 0 S Q x * (-90 * T * (5 * T - 9) * S) -
           dDX2_fn 3 S Q x * (-5 * T * (5 * T - 9) * (9 * x - 25 * S + 15 * Q))) +
      (dDX2_fn 1 S Q x * (-90 * T * (5 * T - 9) * S) -
       dDX2_fn 3 S Q x * (-150 * T * (5 * T - 9) * S)) = 0 := by
    simp only [dDX2_fn, u3_of]; ring
  simp only [QY_num, Omega_F, dDX2_F, F_contract]
  rw [hb0, hb1, hb3, hb4, ho03, ho40, ho34, ho13, ho41, hd4]
  linear_combination -(DY2_of T y * dF5_fn 4 S Q T x y * S * T / 243) * hcore

-- Exact log-derivative verification of `W1_inf` weights `A4[3], A4[4], A3[4], A2[4]`!

end SymmetricSexticResidual.LocalResidueInfAlg

theorem solution :
    (∀ {R : Type} [Field R] [CharZero R] (s1 q1 v1 s2 q2 v2 U V : R),
      SymmetricSexticResidual.SheetCalculus.dH_dS s1 q1 U V * SymmetricSexticResidual.SheetCalculus.dH_dQ s2 q2 v2 U V -
      SymmetricSexticResidual.SheetCalculus.dH_dS s2 q2 U V * SymmetricSexticResidual.SheetCalculus.dH_dQ s1 q1 v1 U V =
        V ^ 2 * (U ^ 3 * SymmetricSexticResidual.LocalResidueInfAlg.minor_U3 s1 q1 v1 s2 q2 v2 +
                 U ^ 2 * SymmetricSexticResidual.LocalResidueInfAlg.minor_U2 s1 q1 v1 s2 q2 v2 +
                 U * SymmetricSexticResidual.LocalResidueInfAlg.minor_U1 s1 q1 v1 s2 q2 v2 +
                 SymmetricSexticResidual.LocalResidueInfAlg.minor_U0 s1 q1 s2 q2)) ∧
    (∀ {R : Type} [Field R] [CharZero R] (mi : Fin 10) (a b xS xQ U V : R),
      SymmetricSexticResidual.SheetCalculus.numM mi a b xS xQ U V =
        V ^ 2 * (U ^ 3 * SymmetricSexticResidual.LocalResidueInfAlg.numM_Uk 3 mi a b xS xQ +
                 U ^ 2 * SymmetricSexticResidual.LocalResidueInfAlg.numM_Uk 2 mi a b xS xQ +
                 U * SymmetricSexticResidual.LocalResidueInfAlg.numM_Uk 1 mi a b xS xQ +
                 SymmetricSexticResidual.LocalResidueInfAlg.numM_Uk 0 mi a b xS xQ)) ∧
    (∀ {R : Type} [Field R] [CharZero R] (a b xS xQ : R),
      -(123236 / 24249375 : R) * (SymmetricSexticResidual.LocalResidueInfAlg.numM_Uk 3 0 a b xS xQ +
        (2790 / 77) * SymmetricSexticResidual.LocalResidueInfAlg.numM_Uk 3 6 a b xS xQ +
        28 * SymmetricSexticResidual.LocalResidueInfAlg.numM_Uk 3 8 a b xS xQ -
        (5904 / 77) * SymmetricSexticResidual.LocalResidueInfAlg.numM_Uk 3 9 a b xS xQ) +
      (492944 / 33949125) * (SymmetricSexticResidual.LocalResidueInfAlg.numM_Uk 3 1 a b xS xQ +
        (927 / 77) * SymmetricSexticResidual.LocalResidueInfAlg.numM_Uk 3 6 a b xS xQ +
        (49 / 5) * SymmetricSexticResidual.LocalResidueInfAlg.numM_Uk 3 8 a b xS xQ -
        (21159 / 770) * SymmetricSexticResidual.LocalResidueInfAlg.numM_Uk 3 9 a b xS xQ) = 0) ∧
    (∀ {R : Type} [Field R] [CharZero R] (a b xS xQ U V : R),
      SymmetricSexticResidual.SheetCalculus.A_0V a b xS xQ U V =
        V ^ 2 * (U ^ 3 * SymmetricSexticResidual.LocalResidueInfAlg.A0V_Uk 3 a b xS xQ +
                 U ^ 2 * SymmetricSexticResidual.LocalResidueInfAlg.A0V_Uk 2 a b xS xQ +
                 U * SymmetricSexticResidual.LocalResidueInfAlg.A0V_Uk 1 a b xS xQ +
                 SymmetricSexticResidual.LocalResidueInfAlg.A0V_Uk 0 a b xS xQ)) ∧
    (∀ {R : Type} [Field R] [CharZero R] (a b xS xQ U V : R),
      SymmetricSexticResidual.SheetCalculus.A_X a b xS xQ U V =
        U * V ^ 2 * (U ^ 3 * SymmetricSexticResidual.LocalResidueInfAlg.AX_Uk 3 a b xS xQ +
                     U ^ 2 * SymmetricSexticResidual.LocalResidueInfAlg.AX_Uk 2 a b xS xQ +
                     U * SymmetricSexticResidual.LocalResidueInfAlg.AX_Uk 1 a b xS xQ +
                     SymmetricSexticResidual.LocalResidueInfAlg.AX_Uk 0 a b xS xQ)) ∧
    (∀ {R : Type} [Field R] [CharZero R] (k : Fin 5) (S Q T x y : R),
      243 * (SymmetricSexticResidual.SheetCalculus.br_fn k S Q T x y 1 0 -
        SymmetricSexticResidual.SheetCalculus.br_fn k S Q T x y 0 0) =
        match k with
        | 0 => -5 * T * (5 * T - 9) * (9 * x - 25 * S + 15 * Q)
        | 1 => -150 * T * (5 * T - 9) * S
        | 2 => 5 * (5 * T - 3) * (27 * x - 25 * S + 45 * Q) * S
        | 3 => -90 * T * (5 * T - 9) * S
        | 4 => 0) ∧
    (∀ {R : Type} [Field R] [CharZero R] (k : Fin 5) (S Q T x y : R),
      243 * SymmetricSexticResidual.SheetCalculus.br_fn k S Q T x y 0 0 =
        match k with
        | 0 => 25 * T * (5 * T - 9) * (-5 * S + 3 * Q)
        | 1 => 150 * T * (5 * T - 9) * S
        | 2 => -25 * (5 * T - 3) * (-5 * S + 9 * Q) * S
        | 3 => 0
        | 4 => 0) ∧
    (∀ {R : Type} [Field R] [CharZero R] (k : Fin 5) (S Q T x y : R),
      243 * (SymmetricSexticResidual.SheetCalculus.br_fn k S Q T x y 1 1 -
        SymmetricSexticResidual.SheetCalculus.br_fn k S Q T x y 1 0 -
        SymmetricSexticResidual.SheetCalculus.br_fn k S Q T x y 0 1 +
        SymmetricSexticResidual.SheetCalculus.br_fn k S Q T x y 0 0) =
        match k with
        | 0 => -(27 * y - 25 * T + 45) * T * (9 * x - 25 * S + 15 * Q)
        | 1 => -30 * (27 * y - 25 * T + 45) * T * S
        | 2 => (9 * y - 25 * T + 15) * (27 * x - 25 * S + 45 * Q) * S
        | 3 => -18 * (27 * y - 25 * T + 45) * T * S
        | 4 => 18 * T * (27 * x - 25 * S + 45 * Q) * S) ∧
    (∀ {R : Type} [Field R] [CharZero R] (i j : Fin 5) (S Q T x y : R),
      81 * (SymmetricSexticResidual.SheetCalculus.om_fn i j S Q T x y 1 0 -
        SymmetricSexticResidual.SheetCalculus.om_fn i j S Q T x y 0 0) =
        let f : Fin 5 → Fin 5 → R := fun p q => match p, q with
          | 0, 2 => 5 * (5 * T - 3) * (9 * x - 25 * S + 15 * Q)
          | 1, 2 => 150 * (5 * T - 3) * S
          | 2, 3 => -90 * (5 * T - 3) * S
          | _, _ => 0
        f i j - f j i) ∧
    (∀ {R : Type} [Field R] [CharZero R] (i j : Fin 5) (S Q T x y : R),
      81 * SymmetricSexticResidual.SheetCalculus.om_fn i j S Q T x y 0 0 =
        let f : Fin 5 → Fin 5 → R := fun p q => match p, q with
          | 0, 2 => -25 * (5 * T - 3) * (-5 * S + 3 * Q)
          | 1, 2 => -150 * (5 * T - 3) * S
          | _, _ => 0
        f i j - f j i) ∧
    (∀ {R : Type} [Field R] [CharZero R] (i j : Fin 5) (S Q T x y : R),
      81 * (SymmetricSexticResidual.SheetCalculus.om_fn i j S Q T x y 1 1 -
        SymmetricSexticResidual.SheetCalculus.om_fn i j S Q T x y 1 0 -
        SymmetricSexticResidual.SheetCalculus.om_fn i j S Q T x y 0 1 +
        SymmetricSexticResidual.SheetCalculus.om_fn i j S Q T x y 0 0) =
        let f : Fin 5 → Fin 5 → R := fun p q => match p, q with
          | 0, 2 => (9 * y - 25 * T + 15) * (9 * x - 25 * S + 15 * Q)
          | 0, 4 => 18 * T * (9 * x - 25 * S + 15 * Q)
          | 1, 2 => 30 * (9 * y - 25 * T + 15) * S
          | 1, 4 => 540 * T * S
          | 2, 3 => -18 * (9 * y - 25 * T + 15) * S
          | 3, 4 => 324 * T * S
          | _, _ => 0
        f i j - f j i) ∧
    (∀ {R : Type} [Field R] [CharZero R] (S Q T x y : R),
      3 * (SymmetricSexticResidual.SheetCalculus.QY_num S Q T x y 1 0 0 -
        SymmetricSexticResidual.SheetCalculus.QY_num S Q T x y 0 0 0) +
      (SymmetricSexticResidual.SheetCalculus.QY_num S Q T x y 1 0 1 -
        SymmetricSexticResidual.SheetCalculus.QY_num S Q T x y 0 0 1) = 0) :=
  ⟨@SymmetricSexticResidual.LocalResidueInfAlg.minor_split_UV,
   @SymmetricSexticResidual.LocalResidueInfAlg.numM_split_UV,
   @SymmetricSexticResidual.LocalResidueInfAlg.AY_t3_U3_eq_zero,
   @SymmetricSexticResidual.LocalResidueInfAlg.A_0V_split_UV,
   @SymmetricSexticResidual.LocalResidueInfAlg.A_X_split_UV,
   @SymmetricSexticResidual.LocalResidueInfAlg.br_10_eq,
   @SymmetricSexticResidual.LocalResidueInfAlg.br_00_eq,
   @SymmetricSexticResidual.LocalResidueInfAlg.br_11_eq,
   @SymmetricSexticResidual.LocalResidueInfAlg.om_10_eq,
   @SymmetricSexticResidual.LocalResidueInfAlg.om_00_eq,
   @SymmetricSexticResidual.LocalResidueInfAlg.om_11_eq,
   @SymmetricSexticResidual.LocalResidueInfAlg.QY_10_u1_zero⟩
