-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_geom_bridge
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:43:23.578629+00:00
-- url     : https://prove2.me/submissions/03dcf081-cead-4500-a40b-2e7c9028448e

import Definitions.Def_HodgeComputerSSR_Q5ACDefs
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_ac_bridge

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueQ5
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  QuadraticCovers CrossedRationalResidue Polynomial PolynomialEncoding.KroneckerCheck
open PolynomialEncoding.PolyOps hiding dotW dotW_rel dotW_len
open scoped BigOperators

section PureRingGeom
variable {R : Type*} [Field R] [CharZero R]
lemma B1_of_eq_Av0_Cv0 (T U V : R) :
    B1_of T U V = 9 * U * ((-(4 / 243 : R) * (T - 3) ^ 3) * V - (-(25 / 243 : R) * T * (5 * T - 9) ^ 2)) := by
  simp only [B1_of]; ring

lemma E0_V_split (S Q T U V : R) :
    H_cub S Q T 1 U V =
      V * (U * H0_of S Q T + u_of U * A1_of S Q U 1) +
      (V - 1) * U * ((-(4 / 243 : R) * (T - 3) ^ 3) * V - (-(25 / 243 : R) * T * (5 * T - 9) ^ 2)) := by
  have h1 := H_cub_eq_H0_A1_B1 S Q T U V
  have hA : A1_of S Q U V = V * A1_of S Q U 1 := by simp only [A1_of]; ring
  rw [h1, hA, B1_of_eq_Av0_Cv0, v_of]
  ring

lemma cA1_dot_V1_ring (S Q T U : R) :
    let ca := q1_a0 S Q U 1; let cb := q2_b0 S Q U 1
    let qC0 : R := -5250 * S ^ 4 + 30450 * S ^ 3 * Q - 64050 * S ^ 2 * Q ^ 2 + 63000 * S * Q ^ 3 - 28350 * Q ^ 4 +
      6250 * S ^ 2 * Q - 15000 * S * Q ^ 2 + 6750 * Q ^ 3 + 6250 * S ^ 2 - 15000 * S * Q + 6750 * Q ^ 2
    let qC1 : R := 336 * S ^ 4 - 2856 * S ^ 3 * Q + 8484 * S ^ 2 * Q ^ 2 - 10080 * S * Q ^ 3 + 3780 * Q ^ 4 -
      40 * S ^ 2 * Q + 240 * S * Q ^ 2 - 360 * Q ^ 3 - 40 * S ^ 2 + 240 * S * Q - 360 * Q ^ 2
    let qC := (qC0 + qC1 * U) / 63
    (H0_of S Q T * dA1_fn 0 S Q U 1 - A1_of S Q U 1 * dH0_fn 0 S Q T) * cb -
    (H0_of S Q T * dA1_fn 1 S Q U 1 - A1_of S Q U 1 * dH0_fn 1 S Q T) * ca =
      qC * (U * H0_of S Q T + u_of U * A1_of S Q U 1) := by
  intro ca cb qC0 qC1 qC
  -- Factor linearly in `H0 := H0_of S Q T`!
  set H0 := H0_of S Q T
  have h1 : dA1_fn 0 S Q U 1 * cb - dA1_fn 1 S Q U 1 * ca = qC * U := by
    simp only [dA1_fn, cb, ca, q2_b0, q1_a0, dH_dQ, dH_dS, qC, qC0, qC1]; ring
  have h2 : -(dH0_fn 0 S Q T * cb - dH0_fn 1 S Q T * ca) = qC * u_of U := by
    simp only [dH0_fn, cb, ca, q2_b0, q1_a0, dH_dQ, dH_dS, qC, qC0, qC1, u_of]; ring
  linear_combination H0 * h1 + A1_of S Q U 1 * h2

lemma QY_dot_V1_ring (S Q T x y U : R) :
    let ca := q1_a0 S Q U 1; let cb := q2_b0 S Q U 1
    let qC0 : R := -5250 * S ^ 4 + 30450 * S ^ 3 * Q - 64050 * S ^ 2 * Q ^ 2 + 63000 * S * Q ^ 3 - 28350 * Q ^ 4 +
      6250 * S ^ 2 * Q - 15000 * S * Q ^ 2 + 6750 * Q ^ 3 + 6250 * S ^ 2 - 15000 * S * Q + 6750 * Q ^ 2
    let qC1 : R := 336 * S ^ 4 - 2856 * S ^ 3 * Q + 8484 * S ^ 2 * Q ^ 2 - 10080 * S * Q ^ 3 + 3780 * Q ^ 4 -
      40 * S ^ 2 * Q + 240 * S * Q ^ 2 - 360 * Q ^ 3 - 40 * S ^ 2 + 240 * S * Q - 360 * Q ^ 2
    let qEx0 : R := 6090 * S ^ 3 - 25620 * S ^ 2 * Q + 34650 * S * Q ^ 2 - 20790 * Q ^ 3 -
      6750 * S * Q + 4050 * Q ^ 2 - 6750 * S + 4050 * Q
    let qEx1 : R := -420 * S ^ 3 + 2940 * S ^ 2 * Q - 6300 * S * Q ^ 2 + 3780 * Q ^ 3
    let qE := 4 * S ^ 2 * T ^ 2 * ((qC0 + qC1 * U) + x * (qEx0 + qEx1 * U)) / 63
    QY_num S Q T x y U 1 0 * cb - QY_num S Q T x y U 1 1 * ca =
      DY2_of T y * qE * (u_of U * A1_of S Q U 1 - 3 * U * (S * x ^ 2 + T * y ^ 2)) := by
  intro ca cb qC0 qC1 qEx0 qEx1 qE
  have hLY1 : LY_of T y 1 = y := by simp only [LY_of, v3_of, v_of]; ring
  have hdLY1 : ∀ k : Fin 5, dLY_fn k (1 : R) = match k with | 4 => 1 | _ => 0 := by
    intro k; fin_cases k <;> simp [dLY_fn, v_of]
  -- Split `(DX2 * Omega_F - dDX2_F)` dotted with `(cb, -ca)` by `y ^ 2` and `y ^ 0`!
  have hy2 : -S * T * (6 * T) *
      ((dDX2_fn 0 S Q x * (-2 * S * T * dLX_fn 3 U) - dDX2_fn 3 S Q x * (-T * LX_of S Q x U - 2 * S * T * dLX_fn 0 U)) * cb -
       (dDX2_fn 1 S Q x * (-2 * S * T * dLX_fn 3 U) - dDX2_fn 3 S Q x * (-2 * S * T * dLX_fn 1 U)) * ca) =
      qE * (-3 * U * T) := by
    simp only [dDX2_fn, dLX_fn, LX_of, u3_of, u_of, cb, ca, q2_b0, q1_a0, dH_dQ, dH_dS, qE, qC0, qC1, qEx0, qEx1]
    ring
  have hy0 :
      DX2_of S Q x * (S * T * ((6 * S * x) * (-(2 / 9 : R) * T * (-25 * S * U + 15 * Q * U + 9 * x * U + 25 * S - 15 * Q)) +
        (3 * x ^ 2 + dH0_fn 0 S Q T) * (4 * S * T * U)) * cb -
        S * T * ((6 * S * x) * (-(2 / 9 : R) * T * (30 * (U - 1) * S)) + dH0_fn 1 S Q T * (4 * S * T * U)) * ca) -
      S * T * (((6 * S * x) * (-dDX2_fn 0 S Q x * (2 * S * T * LX_of S Q x U)) +
          (3 * x ^ 2 + dH0_fn 0 S Q T) * (dDX2_fn 3 S Q x * (2 * S * T * LX_of S Q x U))) * cb -
        ((6 * S * x) * (-dDX2_fn 1 S Q x * (2 * S * T * LX_of S Q x U)) +
          dH0_fn 1 S Q T * (dDX2_fn 3 S Q x * (2 * S * T * LX_of S Q x U))) * ca) =
      qE * (u_of U * A1_of S Q U 1 - 3 * U * S * x ^ 2) := by
    simp only [DX2_of, dDX2_fn, dH0_fn, LX_of, u3_of, u_of, A1_of, cb, ca, q2_b0, q1_a0, dH_dQ, dH_dS,
      qE, qC0, qC1, qEx0, qEx1]
    ring
  have hinner :
      (DX2_of S Q x * Omega_F S Q T x y U 1 0 - dDX2_F S Q T x y U 1 0) * cb -
      (DX2_of S Q x * Omega_F S Q T x y U 1 1 - dDX2_F S Q T x y U 1 1) * ca =
      qE * (u_of U * A1_of S Q U 1 - 3 * U * (S * x ^ 2 + T * y ^ 2)) := by
    have hd4 : dDX2_fn 4 S Q x = 0 := rfl
    have hdX4 : dLX_fn 4 U = 0 := rfl
    simp only [Omega_F, dDX2_F, F_contract, om_fn, br_fn, dF5_fn, hLY1, hdLY1, hd4, hdX4,
      mul_zero, zero_mul, zero_add, sub_zero]
    linear_combination y ^ 2 * hy2 + hy0
  simp only [QY_num]
  linear_combination DY2_of T y * hinner

lemma QX_dot_U1_ring (S Q T x y V : R) :
    let ca := q1_a0 S Q 1 1; let cb := q2_b0 S Q 1 1
    QX_num S Q T x y 1 V 0 * cb - QX_num S Q T x y 1 V 1 * ca = 0 := by
  intro ca cb
  have hca : ca = dH0_fn 0 S Q T := by simp only [ca, q1_a0, dH_dS, dH0_fn]; ring
  have hcb : cb = dH0_fn 1 S Q T := by simp only [cb, q2_b0, dH_dQ, dH0_fn]; ring
  have hLX1 : LX_of S Q x 1 = x := by simp only [LX_of, u3_of, u_of]; ring
  have hdLX1 : ∀ k : Fin 5, dLX_fn k (1 : R) = match k with | 3 => 1 | _ => 0 := by
    intro k; fin_cases k <;> simp [dLX_fn, u_of]; ring
  rw [hca, hcb]
  simp only [QX_num, Omega_F, dDY2_F, F_contract, om_fn, br_fn, dF5_fn, dDY2_fn, dLY_fn, hLX1, hdLX1
    ]
  ring

lemma QY_QX_U0V0_ring (S Q T x y : R) :
    let ca := q1_a0 S Q 0 1; let cb := q2_b0 S Q 0 1
    (QY_num S Q T x y 0 0 0 * cb - QY_num S Q T x y 0 0 1 * ca = 0) ∧
    (QX_num S Q T x y 0 0 0 * cb - QX_num S Q T x y 0 0 1 * ca = 0) ∧
    (EB_of S Q T x y 0 0 = 0) := by
  intro ca cb
  have hbr0 : br_fn 0 S Q T x y 0 0 * cb - br_fn 1 S Q T x y 0 0 * ca = 0 := by
    simp only [br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of, ca, cb, q1_a0, q2_b0, dH_dS, dH_dQ]
    ring
  have hbr3 : br_fn 3 S Q T x y 0 0 = 0 := by simp [br_fn, dLX_fn, dLY_fn]
  have hbr4 : br_fn 4 S Q T x y 0 0 = 0 := by simp [br_fn, dLX_fn, dLY_fn]
  have hom0 : Omega_F S Q T x y 0 0 0 = 0 := by simp [Omega_F, F_contract, om_fn]
  have hom1 : Omega_F S Q T x y 0 0 1 = 0 := by simp [Omega_F, F_contract, om_fn]
  refine ⟨?_, ?_, ?_⟩
  · have hd4 : dDX2_fn 4 S Q x = 0 := rfl
    simp only [QY_num, hom0, hom1, dDX2_F, F_contract, hbr3, hbr4, hd4]
    linear_combination DY2_of T y * S * T * dF5_fn 4 S Q T x y * dDX2_fn 3 S Q x * hbr0
  · have hd3 : dDY2_fn 3 T y = 0 := rfl
    simp only [QX_num, hom0, hom1, dDY2_F, F_contract, hbr3, hbr4, hd3]
    linear_combination DX2_of S Q x * S * T * dF5_fn 3 S Q T x y * dDY2_fn 4 T y * hbr0
  · simp [EB_of, hbr3, hbr4]

end PureRingGeom

private lemma F5_of_AC : F5_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) = 0 := by
  have h := congrArg ιC_K5 (F5_of_L (L := K5))
  simpa only [F5_of, H0_of, SL, QL, TL, xL, yL, ιL, Algebra.algebraMap_self, RingHom.id_apply,
    map_zero, map_add, map_sub, map_mul, map_pow, map_neg, map_div₀, map_ofNat] using h

private lemma pU_ιC_K5_loc (P : K5[X]) : pU ιC_K5 P U_C = polyC P := by
  simp only [pU, polyC, U_C, ιC_K5, ← Polynomial.eval₂_eq_eval_map]
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [eval₂_add, map_add, hp, hq]
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, map_mul, map_pow,
      RatFunc.algebraMap_C, RatFunc.algebraMap_X, RingHom.comp_apply]; rfl

private lemma E0_AC_zero (a b : A_C) :
    E_fn 0 (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) a b U_C V_C = 0 := by
  have h0 := E0_of_cover ιC_K5 U_C W_C U_C_ne_zero
  have hW_eq : W_C ^ 2 + pU ιC_K5 k5Params.bW U_C * W_C + pU ιC_K5 k5Params.cW U_C = 0 := by
    rw [pU_ιC_K5_loc, pU_ιC_K5_loc]; exact W_C_relation
  rw [hW_eq, mul_zero] at h0
  exact (mul_eq_zero.mp h0).resolve_left U_C_ne_zero

lemma evalGeomSQ_K5_props :
    let S := ιC_K5 S_K; let Q := ιC_K5 Q_K; let T := ιC_K5 T_K; let x := ιC_K5 x_K; let y := ιC_K5 y_K
    let qC0_K : K5 := -5250 * S_K ^ 4 + 30450 * S_K ^ 3 * Q_K - 64050 * S_K ^ 2 * Q_K ^ 2 + 63000 * S_K * Q_K ^ 3 -
      28350 * Q_K ^ 4 + 6250 * S_K ^ 2 * Q_K - 15000 * S_K * Q_K ^ 2 + 6750 * Q_K ^ 3 +
      6250 * S_K ^ 2 - 15000 * S_K * Q_K + 6750 * Q_K ^ 2
    let qC1_K : K5 := 336 * S_K ^ 4 - 2856 * S_K ^ 3 * Q_K + 8484 * S_K ^ 2 * Q_K ^ 2 - 10080 * S_K * Q_K ^ 3 +
      3780 * Q_K ^ 4 - 40 * S_K ^ 2 * Q_K + 240 * S_K * Q_K ^ 2 - 360 * Q_K ^ 3 -
      40 * S_K ^ 2 + 240 * S_K * Q_K - 360 * Q_K ^ 2
    let qEx0_K : K5 := 6090 * S_K ^ 3 - 25620 * S_K ^ 2 * Q_K + 34650 * S_K * Q_K ^ 2 - 20790 * Q_K ^ 3 -
      6750 * S_K * Q_K + 4050 * Q_K ^ 2 - 6750 * S_K + 4050 * Q_K
    let qEx1_K : K5 := -420 * S_K ^ 3 + 2940 * S_K ^ 2 * Q_K - 6300 * S_K * Q_K ^ 2 + 3780 * Q_K ^ 3
    (gsqK.H0_7_SQ = 7 * (-2 * S_K ^ 3 + 6 * S_K ^ 2 * Q_K - 3 * S_K * Q_K ^ 2 - 2 * Q_K ^ 3) + 5 * Q_K ^ 2 + 10 * Q_K) ∧
    (gsqK.S2 = S_K * S_K) ∧
    (ιC_K5 (evalBivLK5 gsqK.DX2) = DX2_of S Q x) ∧
    (ιC_K5 (evalBivLK5 gsqK.dDX2_dS) = dDX2_fn 0 S Q x ∧
     ιC_K5 (evalBivLK5 gsqK.dDX2_dQ) = dDX2_fn 1 S Q x ∧
     ιC_K5 (evalBivLK5 gsqK.dDX2_dx) = dDX2_fn 3 S Q x) ∧
    (ιC_K5 (evalBivLK5 gsqK.dF5_0) = 7 * dF5_fn 0 S Q T x y ∧
     ιC_K5 (evalBivLK5 gsqK.dF5_1) = 7 * dF5_fn 1 S Q T x y ∧
     ιC_K5 (evalBivLK5 gsqK.dF5_3) = 7 * dF5_fn 3 S Q T x y ∧
     evalBivLK5 gsqK.dF5_0 = 7 * (3 * x_K ^ 2 + q1_a0 S_K Q_K 1 1) ∧
     evalBivLK5 gsqK.dF5_1 = 7 * q2_b0 S_K Q_K 1 1 ∧
     evalBivLK5 gsqK.dF5_3 = 42 * S_K * x_K) ∧
    (polyC (evalUBivLK5 gsqK.LX_27) = 27 * LX_of S Q x U_C ∧
     (evalUBivLK5 gsqK.LX_27).eval 0 = 25 * S_K - 45 * Q_K ∧
     (evalUBivLK5 gsqK.LX_27).eval 1 = 27 * x_K) ∧
    (polyC (evalUBivLK5 gsqK.dLX_0) = 27 * dLX_fn 0 U_C ∧
     (evalUBivLK5 gsqK.dLX_0).eval 0 = 25 ∧ (evalUBivLK5 gsqK.dLX_0).eval 1 = 0) ∧
    (polyC (evalUBivLK5 gsqK.dLX_1) = 27 * dLX_fn 1 U_C ∧
     (evalUBivLK5 gsqK.dLX_1).eval 0 = -45 ∧ (evalUBivLK5 gsqK.dLX_1).eval 1 = 0) ∧
    (polyC (evalUBivLK5 gsqK.dLX_3) = 27 * dLX_fn 3 U_C ∧
     (evalUBivLK5 gsqK.dLX_3).eval 0 = 0 ∧ (evalUBivLK5 gsqK.dLX_3).eval 1 = 27) ∧
    (polyC (evalUBivLK5 gsqK.PX_0) = (27 / 9 : A_C) * (-25 * S * U_C + 15 * Q * U_C + 9 * x * U_C + 25 * S - 15 * Q) ∧
     (evalUBivLK5 gsqK.PX_0).eval 1 = 27 * x_K ∧
     polyC (evalUBivLK5 gsqK.PX_1) = (27 / 9 : A_C) * (30 * (U_C - 1) * S) ∧
     (evalUBivLK5 gsqK.PX_1).eval 1 = 0 ∧
     polyC (evalUBivLK5 gsqK.PX_3) = (27 / 9 : A_C) * (18 * U_C * S) ∧
     (evalUBivLK5 gsqK.PX_3).eval 1 = 54 * S_K) ∧
    (polyC (evalUPolyK5 gsqK.A1_1_27) = 27 * A1_of S Q U_C 1) ∧
    (polyC (evalUPolyK5 gsqK.qC_63) = ιC_K5 qC0_K + ιC_K5 qC1_K * U_C ∧
     gsqK.qC_63.getD 0 0 = qC0_K ∧ gsqK.qC_63.getD 1 0 = qC1_K ∧
     gsqK.qEx_63.getD 0 0 = qEx0_K ∧ gsqK.qEx_63.getD 1 0 = qEx1_K) := by
  intro S Q T x y qC0_K qC1_K qEx0_K qEx1_K
  let P : GeomSQ K5 → Prop := fun g =>
    (g.H0_7_SQ = 7 * (-2 * S_K ^ 3 + 6 * S_K ^ 2 * Q_K - 3 * S_K * Q_K ^ 2 - 2 * Q_K ^ 3) + 5 * Q_K ^ 2 + 10 * Q_K) ∧
    (g.S2 = S_K * S_K) ∧
    (ιC_K5 (evalBivLK5 g.DX2) = DX2_of S Q x) ∧
    (ιC_K5 (evalBivLK5 g.dDX2_dS) = dDX2_fn 0 S Q x ∧
     ιC_K5 (evalBivLK5 g.dDX2_dQ) = dDX2_fn 1 S Q x ∧
     ιC_K5 (evalBivLK5 g.dDX2_dx) = dDX2_fn 3 S Q x) ∧
    (ιC_K5 (evalBivLK5 g.dF5_0) = 7 * dF5_fn 0 S Q T x y ∧
     ιC_K5 (evalBivLK5 g.dF5_1) = 7 * dF5_fn 1 S Q T x y ∧
     ιC_K5 (evalBivLK5 g.dF5_3) = 7 * dF5_fn 3 S Q T x y ∧
     evalBivLK5 g.dF5_0 = 7 * (3 * x_K ^ 2 + q1_a0 S_K Q_K 1 1) ∧
     evalBivLK5 g.dF5_1 = 7 * q2_b0 S_K Q_K 1 1 ∧
     evalBivLK5 g.dF5_3 = 42 * S_K * x_K) ∧
    (polyC (evalUBivLK5 g.LX_27) = 27 * LX_of S Q x U_C ∧
     (evalUBivLK5 g.LX_27).eval 0 = 25 * S_K - 45 * Q_K ∧
     (evalUBivLK5 g.LX_27).eval 1 = 27 * x_K) ∧
    (polyC (evalUBivLK5 g.dLX_0) = 27 * dLX_fn 0 U_C ∧
     (evalUBivLK5 g.dLX_0).eval 0 = 25 ∧ (evalUBivLK5 g.dLX_0).eval 1 = 0) ∧
    (polyC (evalUBivLK5 g.dLX_1) = 27 * dLX_fn 1 U_C ∧
     (evalUBivLK5 g.dLX_1).eval 0 = -45 ∧ (evalUBivLK5 g.dLX_1).eval 1 = 0) ∧
    (polyC (evalUBivLK5 g.dLX_3) = 27 * dLX_fn 3 U_C ∧
     (evalUBivLK5 g.dLX_3).eval 0 = 0 ∧ (evalUBivLK5 g.dLX_3).eval 1 = 27) ∧
    (polyC (evalUBivLK5 g.PX_0) = (27 / 9 : A_C) * (-25 * S * U_C + 15 * Q * U_C + 9 * x * U_C + 25 * S - 15 * Q) ∧
     (evalUBivLK5 g.PX_0).eval 1 = 27 * x_K ∧
     polyC (evalUBivLK5 g.PX_1) = (27 / 9 : A_C) * (30 * (U_C - 1) * S) ∧
     (evalUBivLK5 g.PX_1).eval 1 = 0 ∧
     polyC (evalUBivLK5 g.PX_3) = (27 / 9 : A_C) * (18 * U_C * S) ∧
     (evalUBivLK5 g.PX_3).eval 1 = 54 * S_K) ∧
    (polyC (evalUPolyK5 g.A1_1_27) = 27 * A1_of S Q U_C 1) ∧
    (polyC (evalUPolyK5 g.qC_63) = ιC_K5 qC0_K + ιC_K5 qC1_K * U_C ∧
     g.qC_63.getD 0 0 = qC0_K ∧ g.qC_63.getD 1 0 = qC1_K ∧
     g.qEx_63.getD 0 0 = qEx0_K ∧ g.qEx_63.getD 1 0 = qEx1_K)
  suffices h : P (evalGeomSQ k5Ops S_K Q_K) from h
  unfold evalGeomSQ
  refine letB_intro fun S2 hS2 => letB_intro fun SQ hSQ => letB_intro fun Q2 hQ2 =>
    letB_intro fun S3 hS3 => letB_intro fun S4 hS4 => letB_intro fun Q3 hQ3 => letB_intro fun Q4 hQ4 =>
    letB_intro fun Sm3Q hSm3Q => letB_intro fun A5 hA5 => letB_intro fun pS hpS => letB_intro fun H0_7_SQ hH0SQ =>
    letB_intro fun u3 hu3 => letB_intro fun u3_2 hu3_2 =>
    letB_intro fun LX0 hLX0 => letB_intro fun LX1 hLX1 => letB_intro fun LX_27 hLX27 =>
    letB_intro fun dLX_0 hdLX0 => letB_intro fun dLX_1 hdLX1 => letB_intro fun dLX_3 hdLX3 =>
    letB_intro fun S2x hS2x => ?_
  dsimp only [P]
  have hS2' : S2 = S_K * S_K := hS2
  have hSQ' : SQ = S_K * Q_K := hSQ
  have hQ2' : Q2 = Q_K * Q_K := hQ2
  have hS3' : S3 = S_K ^ 3 := by rw [hS3, hS2']; dsimp only [k5Ops, ringOps]; ring
  have hS4' : S4 = S_K ^ 4 := by rw [hS4, hS2']; dsimp only [k5Ops, ringOps]; ring
  have hQ3' : Q3 = Q_K ^ 3 := by rw [hQ3, hQ2']; dsimp only [k5Ops, ringOps]; ring
  have hQ4' : Q4 = Q_K ^ 4 := by rw [hQ4, hQ2']; dsimp only [k5Ops, ringOps]; ring
  have hSm3Q' : Sm3Q = S_K - 3 * Q_K := by rw [hSm3Q]; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hA5' : A5 = 5 * S_K - 9 * Q_K := by rw [hA5]; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hS2x' : S2x = 2 * S_K := by rw [hS2x]; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hu3_eq : evalBivLK5 u3 = x_K - S_K + 2 * Q_K := by
    rw [hu3]; simp only [evalBivLK5, evalBivL, evalYList, k5Ops, ringOps, Int.cast_ofNat]; ring
  have hu3_2_eq : evalBivLK5 u3_2 = (x_K - S_K + 2 * Q_K) ^ 2 := by
    rw [hu3_2, evalBivLK5_bivMul, hu3_eq]; ring
  have hLX0_eq : evalBivLK5 LX0 = 25 * S_K - 45 * Q_K := by
    rw [hLX0]; simp only [bivConst, evalBivLK5, evalBivL, evalYList, k5Ops, ringOps, Int.cast_ofNat]; ring
  have hLX1_eq : evalBivLK5 LX1 = 45 * Q_K - 25 * S_K + 27 * x_K := by
    rw [hLX1]; simp only [evalBivLK5, evalBivL, evalYList, k5Ops, ringOps, Int.cast_ofNat]; ring
  have hLX_ac : polyC (evalUBivLK5 LX_27) = 27 * LX_of S Q x U_C := by
    rw [hLX27]; simp only [evalUBivLK5, evalUBivL, hLX0_eq, hLX1_eq, polyC_add, polyC_sub, polyC_mul, polyC_C, polyC_X, polyC_ofNat,
      LX_of, u3_of, u_of, S, Q, x, map_add, map_sub, map_mul, map_ofNat, mul_zero, add_zero]; ring
  have hLX_e0 : (evalUBivLK5 LX_27).eval 0 = 25 * S_K - 45 * Q_K := by
    rw [hLX27]; simp [evalUBivLK5, evalUBivL, hLX0_eq]
  have hLX_e1 : (evalUBivLK5 LX_27).eval 1 = 27 * x_K := by
    rw [hLX27]; simp [evalUBivLK5, evalUBivL, hLX0_eq, hLX1_eq]; ring
  have hd0_ac : polyC (evalUBivLK5 dLX_0) = 27 * dLX_fn 0 U_C := by
    rw [hdLX0]; simp only [evalUBivLK5, evalUBivL, bivConst, evalBivL, evalYList, k5Ops, ringOps,
      polyC_add, polyC_neg, polyC_mul, polyC_X, polyC_ofNat, 
      dLX_fn, u_of, Int.cast_neg, Int.cast_ofNat,
      map_neg, map_ofNat, mul_zero, add_zero]; ring
  have hd0_e0 : (evalUBivLK5 dLX_0).eval 0 = 25 := by
    rw [hdLX0]; simp [evalUBivLK5, evalUBivL, bivConst, evalBivL, evalYList, k5Ops, ringOps]
  have hd0_e1 : (evalUBivLK5 dLX_0).eval 1 = 0 := by
    rw [hdLX0]; simp [evalUBivLK5, evalUBivL, bivConst, evalBivL, evalYList, k5Ops, ringOps]
  have hd1_ac : polyC (evalUBivLK5 dLX_1) = 27 * dLX_fn 1 U_C := by
    rw [hdLX1]; simp only [evalUBivLK5, evalUBivL, bivConst, evalBivL, evalYList, k5Ops, ringOps,
      polyC_add, polyC_neg, polyC_mul, polyC_X, polyC_ofNat, 
      dLX_fn, u_of, Int.cast_neg, Int.cast_ofNat,
      map_neg, map_ofNat, mul_zero, add_zero]; ring
  have hd1_e0 : (evalUBivLK5 dLX_1).eval 0 = -45 := by
    rw [hdLX1]; simp [evalUBivLK5, evalUBivL, bivConst, evalBivL, evalYList, k5Ops, ringOps]
  have hd1_e1 : (evalUBivLK5 dLX_1).eval 1 = 0 := by
    rw [hdLX1]; simp [evalUBivLK5, evalUBivL, bivConst, evalBivL, evalYList, k5Ops, ringOps]
  have hd3_ac : polyC (evalUBivLK5 dLX_3) = 27 * dLX_fn 3 U_C := by
    rw [hdLX3]; simp only [evalUBivLK5, evalUBivL, bivConst, evalBivL, evalYList, k5Ops, ringOps,
      polyC_add, polyC_mul, polyC_X, polyC_ofNat, polyC_zero,
      dLX_fn, Int.cast_ofNat,
      map_ofNat, map_zero, mul_zero, add_zero]; ring
  have hd3_e0 : (evalUBivLK5 dLX_3).eval 0 = 0 := by
    rw [hdLX3]; simp [evalUBivLK5, evalUBivL, evalBivL]
  have hd3_e1 : (evalUBivLK5 dLX_3).eval 1 = 27 := by
    rw [hdLX3]; simp [evalUBivLK5, evalUBivL, bivConst, evalBivL, evalYList, k5Ops, ringOps]
  have hqC0_eq :
      ((((((((((-5250 : K5) * S4 + 30450 * (S3 * Q_K)) + -64050 * (S2 * Q2)) + 63000 * (S_K * Q3)) +
        -28350 * Q4) + 6250 * (S2 * Q_K)) + -15000 * (S_K * Q2)) + 6750 * Q3) + 6250 * S2) +
        -15000 * SQ) + 6750 * Q2 = qC0_K := by
    rw [hS4', hS3', hS2', hSQ', hQ2', hQ3', hQ4']; dsimp only [qC0_K]; ring
  have hqC1_eq :
      ((((((((((336 : K5) * S4 + -2856 * (S3 * Q_K)) + 8484 * (S2 * Q2)) + -10080 * (S_K * Q3)) +
        3780 * Q4) + -40 * (S2 * Q_K)) + 240 * (S_K * Q2)) + -360 * Q3) + -40 * S2) +
        240 * SQ) + -360 * Q2 = qC1_K := by
    rw [hS4', hS3', hS2', hSQ', hQ2', hQ3', hQ4']; dsimp only [qC1_K]; ring
  have hqEx0_eq :
      (((((((6090 : K5) * S3 + -25620 * (S2 * Q_K)) + 34650 * (S_K * Q2)) + -20790 * Q3) +
        -6750 * SQ) + 4050 * Q2) + -6750 * S_K) + 4050 * Q_K = qEx0_K := by
    rw [hS3', hS2', hSQ', hQ2', hQ3']; dsimp only [qEx0_K]; ring
  have hqEx1_eq : (((-420 : K5) * S3 + 2940 * (S2 * Q_K)) + -6300 * (S_K * Q2)) + 3780 * Q3 = qEx1_K := by
    rw [hS3', hS2', hQ2', hQ3']; dsimp only [qEx1_K]; ring
  refine ⟨?_, hS2', ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨hLX_ac, hLX_e0, hLX_e1⟩,
    ⟨hd0_ac, hd0_e0, hd0_e1⟩, ⟨hd1_ac, hd1_e0, hd1_e1⟩, ⟨hd3_ac, hd3_e0, hd3_e1⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hH0SQ, hpS, hS3', hS2', hQ2', hQ3']; dsimp only [k5Ops, ringOps]; push_cast; ring
  · simp only [evalBivLK5_bivAdd, evalBivLK5_bivSc, bivConst, evalBivLK5, evalBivL, evalYList, hu3_eq, hu3_2_eq,
      hS2', hSQ', hQ2', hQ3', DX2_of, u3_of, S, Q, x, map_add, map_sub, map_mul, map_pow,
      map_ofNat, map_zero]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, map_neg, map_mul, map_sub, map_pow, map_ofNat, mul_zero, add_zero]; ring
  · simp only [evalBivLK5_bivAdd, evalBivLK5_bivSc, bivConst, evalBivLK5, evalBivL, evalYList, hu3_eq, hu3_2_eq,
      hS2', hSQ', hQ2', dDX2_fn, u3_of, S, Q, x, map_add, map_sub, map_mul, map_pow,
      map_ofNat, map_zero]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, add_zero]; ring
  · simp only [evalBivLK5_bivAdd, evalBivLK5_bivSc, bivConst, evalBivLK5, evalBivL, evalYList, hu3_eq,
      hS2', hSQ', hQ2', dDX2_fn, u3_of, S, Q, x, map_add, map_sub, map_mul, 
      map_ofNat, map_zero]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, map_neg, map_mul, map_add, map_sub, map_ofNat, mul_zero, add_zero]; ring
  · simp only [evalBivLK5_bivAdd, evalBivLK5_bivSc, bivConst, evalBivLK5, evalBivL, evalYList, hu3_eq,
      hS2', hSQ', dDX2_fn, u3_of, S, Q, x, map_add, map_sub, map_mul, 
      map_ofNat, map_zero]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, map_neg, map_mul, map_add, map_ofNat, mul_zero, add_zero]; ring
  · simp only [evalBivLK5, evalBivL, evalYList, hS2', hSQ', hQ2', k5Ops, ringOps, dF5_fn, dH0_fn, S, Q, x, 
      map_add, map_sub, map_mul, map_neg, map_ofNat, map_zero, Int.cast_neg, Int.cast_ofNat]; ring
  · simp only [evalBivLK5, evalBivL, evalYList, hS2', hSQ', hQ2', k5Ops, ringOps, dF5_fn, dH0_fn, S, Q, 
      map_add, map_sub, map_mul, map_ofNat, map_zero, Int.cast_ofNat]; ring
  · simp only [evalBivLK5, evalBivL, evalYList, k5Ops, ringOps, dF5_fn, S, x, 
      map_add, map_mul, map_ofNat, map_zero, Int.cast_ofNat]; ring
  · simp only [evalBivLK5, evalBivL, evalYList, hS2', hSQ', hQ2', k5Ops, ringOps, q1_a0, dH_dS, Int.cast_neg, Int.cast_ofNat]; ring
  · simp only [evalBivLK5, evalBivL, evalYList, hS2', hSQ', hQ2', k5Ops, ringOps, q2_b0, dH_dQ, Int.cast_ofNat]; ring
  · simp only [evalBivLK5, evalBivL, evalYList, k5Ops, ringOps, Int.cast_ofNat]; ring
  · simp only [evalUBivLK5_ubAdd, evalUBivLK5_ubSc, polyC_add, polyC_mul, polyC_C, polyC_ofNat, hS2x', hd0_ac, hLX_ac,
      dLX_fn, LX_of, u3_of, u_of, S, Q, x, map_mul, map_ofNat]; ring
  · simp only [evalUBivLK5_ubAdd, evalUBivLK5_ubSc, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      hd0_e1, hLX_e1, mul_zero, zero_add]
  · simp only [evalUBivLK5_ubSc, polyC_mul, polyC_C, polyC_ofNat, hS2x', hd1_ac, dLX_fn, u_of, S, map_mul, map_ofNat]; ring
  · simp only [evalUBivLK5_ubSc, Polynomial.eval_mul, Polynomial.eval_C, hd1_e1, mul_zero]
  · simp only [evalUBivLK5_ubSc, polyC_mul, polyC_C, polyC_ofNat, hS2x', hd3_ac, dLX_fn, S, map_mul, map_ofNat]; ring
  · simp only [evalUBivLK5_ubSc, Polynomial.eval_mul, Polynomial.eval_C, hS2x', hd3_e1]; ring
  · simp only [evalUPolyK5, evalUPoly, hA5', hSm3Q', k5Ops, ringOps, polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_C, polyC_X, polyC_ofNat, A1_of, S, Q,
      map_sub, map_mul, map_neg, map_ofNat, mul_zero, add_zero,
      Int.cast_neg, Int.cast_ofNat]; ring
  · simp only [evalUPolyK5, evalUPoly, k5Ops, ringOps, Int.cast_neg, Int.cast_ofNat, hqC0_eq, hqC1_eq,
      polyC_add, polyC_mul, polyC_C, polyC_X, mul_zero, add_zero]; ring
  · simp only [List.getD_cons_zero, k5Ops, ringOps, Int.cast_neg, Int.cast_ofNat, hqC0_eq]
  · simp only [List.getD_cons_succ, List.getD_cons_zero, k5Ops, ringOps, Int.cast_neg, Int.cast_ofNat, hqC1_eq]
  · simp only [List.getD_cons_zero, k5Ops, ringOps, Int.cast_neg, Int.cast_ofNat, hqEx0_eq]
  · simp only [List.getD_cons_succ, List.getD_cons_zero, k5Ops, ringOps, Int.cast_neg, Int.cast_ofNat, hqEx1_eq]

-- Fast O(N) `letB_intro` bridge for `gtK` (`evalGeomT k5Ops S_K acK.ca_p acK.cb_p gsqK T_K`)!
lemma evalGeomT_K5_props :
    let S := ιC_K5 S_K; let Q := ιC_K5 Q_K; let T := ιC_K5 T_K
    let x := ιC_K5 x_K; let y := ιC_K5 y_K
    let ca := polyC k5Params.ca_h; let cb := polyC k5Params.cb_h
    let QX_dot := QX_num S Q T x y U_C V_C 0 * cb - QX_num S Q T x y U_C V_C 1 * ca
    let QY_dot := QY_num S Q T x y U_C V_C 0 * cb - QY_num S Q T x y U_C V_C 1 * ca
    let cA1_dot := (H0_of S Q T * dA1_fn 0 S Q U_C V_C - A1_of S Q U_C V_C * dH0_fn 0 S Q T) * cb -
      (H0_of S Q T * dA1_fn 1 S Q U_C V_C - A1_of S Q U_C V_C * dH0_fn 1 S Q T) * ca
    let q1_dot := H0_of S Q T * A1_of S Q U_C V_C * (QY_dot / v_of V_C) +
      H0_of S Q T * B1_of T U_C V_C * (QX_dot / u_of U_C) +
      (cA1_dot / v_of V_C) * EB_of S Q T x y U_C V_C
    (gtK.H0_7 = 7 * H0_of S_K Q_K T_K) ∧
    (gtK.H0_7_2 = gtK.H0_7 ^ 2) ∧
    (gtK.Av0_243 = 243 * k5Params.Av0) ∧
    (gtK.Cv0_243 = 243 * k5Params.Cv0) ∧
    (gtK.Cv0_243 = -25 * gtK.Cv0_int) ∧
    (polyC Bv_1701_p = 1701 * (ιC_K5 k5Params.Av0 * polyC k5Params.bW)) ∧
    (polyC (evalUBivLK5 gtK.qX_0_sc) + V_C * polyC (evalUBivLK5 gtK.qX_1_sc) = 321489 * (QX_dot / u_of U_C)) ∧
    (polyC (evalUBivLK5 gtK.qY_0_321489) - 9 * (321489 / 63 : A_C) * polyC (evalUBivLK5 gtK.DY2_qE_63) * U_C * ιC_K5 k5Params.Av0 * V_C =
      321489 * (QY_dot / v_of V_C)) ∧
    ((M_mid_int : A_C) * q1_dot =
      ιC_K5 k5Params.Cv0 * U_C * polyC (evalUBivLK5 gtK.q1_0_div_sc) +
      (1 / 243 : A_C) * polyC (evalUBivLK5 gtK.q1_1_sc) * V_C +
      ιC_K5 k5Params.Av0 * U_C * polyC (evalUBivLK5 gtK.q1_2_div_sc) * V_C ^ 2) ∧
    ((evalUBivLK5 gtK.qX_0_sc).eval 0 = 0 ∧
     (evalUBivLK5 gtK.qY_0_321489).eval 0 = 0 ∧
     (evalUBivLK5 gtK.q1_0_div_sc).eval 0 = 0 ∧
     (evalUBivLK5 gtK.q1_1_sc).eval 0 = 0) := by
  intro S Q T x y ca cb QX_dot QY_dot cA1_dot q1_dot
  let P : GeomT K5 → Prop := fun gt =>
    (gt.H0_7 = 7 * H0_of S_K Q_K T_K) ∧
    (gt.H0_7_2 = gt.H0_7 ^ 2) ∧
    (gt.Av0_243 = 243 * k5Params.Av0) ∧
    (gt.Cv0_243 = 243 * k5Params.Cv0) ∧
    (gt.Cv0_243 = -25 * gt.Cv0_int) ∧
    (polyC (evalUPolyK5 acK.Bv_SQ + Polynomial.C gt.Bv1_T_1701 * Polynomial.X) =
      1701 * (ιC_K5 k5Params.Av0 * polyC k5Params.bW)) ∧
    (polyC (evalUBivLK5 gt.qX_0_sc) + V_C * polyC (evalUBivLK5 gt.qX_1_sc) = 321489 * (QX_dot / u_of U_C)) ∧
    (polyC (evalUBivLK5 gt.qY_0_321489) - 9 * (321489 / 63 : A_C) * polyC (evalUBivLK5 gt.DY2_qE_63) * U_C * ιC_K5 k5Params.Av0 * V_C =
      321489 * (QY_dot / v_of V_C)) ∧
    ((M_mid_int : A_C) * q1_dot =
      ιC_K5 k5Params.Cv0 * U_C * polyC (evalUBivLK5 gt.q1_0_div_sc) +
      (1 / 243 : A_C) * polyC (evalUBivLK5 gt.q1_1_sc) * V_C +
      ιC_K5 k5Params.Av0 * U_C * polyC (evalUBivLK5 gt.q1_2_div_sc) * V_C ^ 2) ∧
    ((evalUBivLK5 gt.qX_0_sc).eval 0 = 0 ∧
     (evalUBivLK5 gt.qY_0_321489).eval 0 = 0 ∧
     (evalUBivLK5 gt.q1_0_div_sc).eval 0 = 0 ∧
     (evalUBivLK5 gt.q1_1_sc).eval 0 = 0)
  suffices h : P (evalGeomT k5Ops S_K acK.ca_p acK.cb_p gsqK T_K) from h
  unfold evalGeomT
  refine letB_intro fun T2 hT2 => letB_intro fun T3 hT3 => letB_intro fun pT hpT =>
    letB_intro fun H0_7 hH0_7 => letB_intro fun H0_7_2 hH0_7_2 =>
    letB_intro fun Tm3 hTm3 => letB_intro fun Av0_243 hAv0_243 =>
    letB_intro fun T59 hT59 => letB_intro fun Cv0_int hCv0_int => letB_intro fun Cv0_243 hCv0_243 =>
    letB_intro fun Bv1_T_1701 hBv1_T => letB_intro fun v3 hv3 => letB_intro fun v3_2 hv3_2 =>
    letB_intro fun DY2 hDY2_d => letB_intro fun dDY2_dy hdDY2_d =>
    letB_intro fun ST hST => letB_intro fun ST2 hST2 => letB_intro fun W2 hW2 =>
    letB_intro fun dF5_4 hdF5_4 => letB_intro fun LY0 hLY0 => letB_intro fun LY1 hLY1 =>
    letB_intro fun PY_4_1 hPY41 =>
    letB_intro fun br0_0 hbr0_0 => letB_intro fun br1_0 hbr1_0 =>
    letB_intro fun br0_1 hbr0_1 => letB_intro fun br1_1 hbr1_1 =>
    letB_intro fun br0_3 hbr0_3 => letB_intro fun br1_3 hbr1_3 => letB_intro fun br1_4 hbr1_4 =>
    letB_intro fun omF1_0 homF1_0 => letB_intro fun omF1_1 homF1_1 =>
    letB_intro fun dYF0_0 hdYF0_0 => letB_intro fun dYF0_1 hdYF0_1 =>
    letB_intro fun dYF1_0 hdYF1_0 => letB_intro fun dYF1_1 hdYF1_1 =>
    letB_intro fun dXF0_0 hdXF0_0 => letB_intro fun dXF0_1 hdXF0_1 =>
    letB_intro fun QX0_0 hQX0_0 => letB_intro fun QX0_1 hQX0_1 =>
    letB_intro fun QX1_0 hQX1_0 => letB_intro fun QX1_1 hQX1_1 =>
    letB_intro fun QY0_0 hQY0_0 => letB_intro fun QY0_1 hQY0_1 =>
    letB_intro fun EB0_5103 hEB0 => letB_intro fun EB1_5103 hEB1 =>
    letB_intro fun div0 hdiv0 => letB_intro fun div1 hdiv1 =>
    letB_intro fun QY_dot_0_sc hQYd0 => letB_intro fun c4S2T2 hc4S2T2 =>
    letB_intro fun qE_63 hqE_63 => letB_intro fun DY2_qE_63 hDYqE =>
    letB_intro fun qY_0_321489 hqY0 => ?_
  dsimp only [P]
  have hacP_ca := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_ac_bridge.ca_p
  have hacP_cb := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_ac_bridge.cb_p
  have hacP_ca0 := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_ac_bridge.ca_e0
  have hacP_cb0 := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_ac_bridge.cb_e0
  have hacP_Bv := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_ac_bridge.Bv_SQ
  have hgsqP := evalGeomSQ_K5_props
  have hca_p : polyC (evalUPolyK5 acK.ca_p) = 567 * ca := by rw [hacP_ca, polyC_mul, polyC_C]; simp [ca, map_ofNat]
  have hcb_p : polyC (evalUPolyK5 acK.cb_p) = 567 * cb := by rw [hacP_cb, polyC_mul, polyC_C]; simp [cb, map_ofNat]
  have hca_e0 := hacP_ca0
  have hcb_e0 := hacP_cb0
  have hca_e1 : (evalUPolyK5 acK.ca_p).eval 1 = 567 * q1_a0 S_K Q_K 1 1 := by
    rw [hacP_ca, Polynomial.eval_mul, Polynomial.eval_C]
    simp only [CoverParams.ca_h, CoverParams.quadU, CoverParams.inv9, CoverParams.inv27,
      CoverParams.inv81, k5Params_inv3, k5Params_S, k5Params_Q,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
      q1_a0, dH_dS]; ring
  have hcb_e1 : (evalUPolyK5 acK.cb_p).eval 1 = 567 * q2_b0 S_K Q_K 1 1 := by
    rw [hacP_cb, Polynomial.eval_mul, Polynomial.eval_C]
    simp only [CoverParams.cb_h, CoverParams.quadU, CoverParams.inv9, CoverParams.inv27,
      k5Params_inv3, k5Params_inv7, k5Params_S, k5Params_Q,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
      q2_b0, dH_dQ]; ring
  -- Scalar identities
  have hT2' : T2 = T_K * T_K := hT2
  have hT3' : T3 = T_K ^ 3 := by rw [hT3, hT2']; dsimp only [k5Ops, ringOps]; ring
  have hH0 : H0_7 = 7 * H0_of S_K Q_K T_K := by
    rw [hH0_7, hpT, hgsqP.1, hT3', hT2']; dsimp only [k5Ops, ringOps, H0_of]; push_cast; ring
  have hH0_2 : H0_7_2 = H0_7 ^ 2 := by rw [hH0_7_2]; dsimp only [k5Ops, ringOps]; ring
  have hAv0 : Av0_243 = 243 * k5Params.Av0 := by
    rw [hAv0_243, hTm3]; simp only [k5Ops, ringOps, CoverParams.Av0, CoverParams.inv243, k5Params_inv3, k5Params_T,
      Int.cast_neg, Int.cast_ofNat]; ring
  have hCv0 : Cv0_243 = 243 * k5Params.Cv0 := by
    rw [hCv0_243, hCv0_int, hT59]; simp only [k5Ops, ringOps, CoverParams.Cv0, CoverParams.inv243, k5Params_inv3, k5Params_T,
      Int.cast_neg, Int.cast_ofNat]; ring
  have hCv0i : Cv0_243 = -25 * Cv0_int := by rw [hCv0_243]; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hBv1701 : polyC (evalUPolyK5 acK.Bv_SQ + Polynomial.C Bv1_T_1701 * Polynomial.X) =
      1701 * (ιC_K5 k5Params.Av0 * polyC k5Params.bW) := by
    have hbW : ιC_K5 k5Params.Av0 * polyC k5Params.bW = polyC k5Params.Bv := by
      rw [CoverParams.bW, polyC_mul, polyC_C, ← mul_assoc, ← map_mul,
        k5Params_Av0_mul_inv, map_one, one_mul]
    rw [hbW, polyC_add, polyC_mul, polyC_C, polyC_X, hacP_Bv, hBv1_T, hT3', hT2']
    simp only [k5Ops, ringOps, CoverParams.Bv, CoverParams.Bv0, CoverParams.Bv1, CoverParams.Bv2, CoverParams.quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv243, k5Params_inv3, k5Params_inv7,
      k5Params_S, k5Params_Q, k5Params_T, polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_pow, polyC_C, polyC_X, polyC_ofNat, 
      map_add, map_sub, map_mul, map_inv₀, map_neg, map_pow, map_ofNat, Int.cast_ofNat]; ring
  -- BivL & basic `A_C` evaluations
  have hv3_eq : evalBivLK5 v3 = y_K - T_K + 2 := by rw [hv3]; simp only [evalBivLK5, evalBivL, evalYList, k5Ops, ringOps, Int.cast_ofNat]; ring
  have hv3_2_eq : evalBivLK5 v3_2 = (y_K - T_K + 2) ^ 2 := by rw [hv3_2, evalBivLK5_bivMul, hv3_eq]; ring
  have hDY2 : ιC_K5 (evalBivLK5 DY2) = DY2_of T y := by
    rw [hDY2_d]; simp only [evalBivLK5_bivAdd, evalBivLK5_bivSc, bivConst, evalBivLK5, evalBivL, evalYList,
      hv3_eq, hv3_2_eq, hT2', DY2_of, v3_of, T, y, map_add, map_sub, map_mul, map_pow,
      map_ofNat, map_zero]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, map_neg, map_mul, map_sub, map_ofNat, mul_zero, add_zero]; ring
  have hdDY2 : ιC_K5 (evalBivLK5 dDY2_dy) = dDY2_fn 4 T y := by
    rw [hdDY2_d]; simp only [evalBivLK5_bivAdd, evalBivLK5_bivSc, bivConst, evalBivLK5, evalBivL, evalYList,
      hv3_eq, hT2', dDY2_fn, v3_of, T, y, map_add, map_sub, map_mul, map_ofNat, map_zero
      ]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, map_neg, map_mul, map_add, map_ofNat, mul_zero, add_zero]; ring
  have hST' : ST = S_K * T_K := hST
  have hST2' : ST2 = 2 * (S_K * T_K) := by rw [hST2, hST']; dsimp only [k5Ops, ringOps]; push_cast; ring
  have hW2_eq : ιC_K5 (evalBivLK5 W2) = S * T * DX2_of S Q x * DY2_of T y := by
    rw [hW2, evalBivLK5_bivSc, evalBivLK5_bivMul, hST', map_mul, map_mul, map_mul, hgsqP.2.2.1, hDY2]; ring
  have hdF5_4_eq : ιC_K5 (evalBivLK5 dF5_4) = 7 * dF5_fn 4 S Q T x y := by
    rw [hdF5_4]; simp only [evalBivLK5, evalBivL, evalYList, k5Ops, ringOps, dF5_fn, T, y, map_add, map_mul, map_ofNat, map_zero, Int.cast_ofNat]; ring
  have hLY0_K : evalBivLK5 LY0 = 25 * T_K - 45 := by
    rw [hLY0]; simp only [bivConst, evalBivLK5, evalBivL, evalYList, k5Ops, ringOps, Int.cast_ofNat]; ring
  have hLY1_K : evalBivLK5 LY1 = 45 - 25 * T_K + 27 * y_K := by
    rw [hLY1]; simp only [evalBivLK5, evalBivL, evalYList, k5Ops, ringOps, Int.cast_ofNat]; ring
  have hLY0_AC : ιC_K5 (evalBivLK5 LY0) = 27 * LY_of T y 0 := by
    rw [hLY0_K]; simp only [LY_of, v3_of, v_of, T, map_sub, map_mul, map_ofNat]; ring
  have hLY_eq : ιC_K5 (evalBivLK5 LY0) + V_C * ιC_K5 (evalBivLK5 LY1) = 27 * LY_of T y V_C := by
    rw [hLY0_K, hLY1_K]; simp only [LY_of, v3_of, v_of, T, y, map_add, map_sub, map_mul, map_ofNat]; ring
  have hPY_K : evalBivLK5 PY_4_1 = 54 * T_K := by
    rw [hPY41]; simp only [bivConst, evalBivLK5, evalBivL, evalYList, k5Ops, ringOps, Int.cast_ofNat]; ring
  -- Evaluate `br0_0..br1_4`, `omF1_*`, `dYF*`, `QX*` at `U = 0`, `U = 1`, and in `A_C`!
  have hbr0_3_e0 : (evalUBivLK5 br0_3).eval 0 = 0 := by
    rw [hbr0_3, evalUBivLK5_ubSc, evalUBivLK5_ubBmul]; simp [hgsqP.2.2.2.2.2.2.2.2.1.2.1]
  have hbr0_0_e0 : (evalUBivLK5 br0_0).eval 0 = -(2 * (S_K * T_K)) * ((25 * T_K - 45) * 25) - T_K * ((25 * T_K - 45) * (25 * S_K - 45 * Q_K)) := by
    rw [hbr0_0]; simp only [evalUBivLK5_ubSub, evalUBivLK5_ubSc, evalUBivLK5_ubBmul,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hST2', hLY0_K,
      hgsqP.2.2.2.2.2.2.1.2.1, hgsqP.2.2.2.2.2.1.2.1]; dsimp only [k5Ops, ringOps]
  have hbr0_1_e0 : (evalUBivLK5 br0_1).eval 0 = -(2 * (S_K * T_K)) * ((25 * T_K - 45) * (-45)) := by
    rw [hbr0_1]; simp only [evalUBivLK5_ubSc, evalUBivLK5_ubBmul,
      Polynomial.eval_mul, Polynomial.eval_C, hST2', hLY0_K, hgsqP.2.2.2.2.2.2.2.1.2.1]; dsimp only [k5Ops, ringOps]
  have hbr0_cancel : (evalUBivLK5 br0_0).eval 0 * (evalUPolyK5 acK.cb_p).eval 0 -
      (evalUBivLK5 br0_1).eval 0 * (evalUPolyK5 acK.ca_p).eval 0 = 0 := by
    rw [hbr0_0_e0, hbr0_1_e0, hcb_e0, hca_e0]; ring
  have hbr_e1 :
      (evalUBivLK5 br0_0).eval 1 = -T_K * (evalBivLK5 LY0 * (27 * x_K)) ∧
      (evalUBivLK5 br0_1).eval 1 = 0 ∧
      (evalUBivLK5 br0_3).eval 1 = -(2 * (S_K * T_K)) * (evalBivLK5 LY0 * 27) ∧
      (evalUBivLK5 br1_0).eval 1 = -T_K * (evalBivLK5 LY1 * (27 * x_K)) ∧
      (evalUBivLK5 br1_1).eval 1 = 0 ∧
      (evalUBivLK5 br1_3).eval 1 = -(2 * (S_K * T_K)) * (evalBivLK5 LY1 * 27) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hbr0_0]; simp [evalUBivLK5_ubSub, evalUBivLK5_ubSc, evalUBivLK5_ubBmul, hgsqP.2.2.2.2.2.2.1.2.2, hgsqP.2.2.2.2.2.1.2.2]
    · rw [hbr0_1]; simp [evalUBivLK5_ubSc, evalUBivLK5_ubBmul, hgsqP.2.2.2.2.2.2.2.1.2.2]
    · rw [hbr0_3]; simp [evalUBivLK5_ubSc, evalUBivLK5_ubBmul, hST2', hgsqP.2.2.2.2.2.2.2.2.1.2.2]; dsimp only [k5Ops, ringOps]; ring
    · rw [hbr1_0]; simp [evalUBivLK5_ubSub, evalUBivLK5_ubSc, evalUBivLK5_ubBmul, hgsqP.2.2.2.2.2.2.1.2.2, hgsqP.2.2.2.2.2.1.2.2]
    · rw [hbr1_1]; simp [evalUBivLK5_ubSc, evalUBivLK5_ubBmul, hgsqP.2.2.2.2.2.2.2.1.2.2]
    · rw [hbr1_3]; simp [evalUBivLK5_ubSc, evalUBivLK5_ubBmul, hST2', hgsqP.2.2.2.2.2.2.2.2.1.2.2]; dsimp only [k5Ops, ringOps]; ring
  have hdQX0_e1 : (evalUBivLK5 (ubSub k5Ops (ubMulU k5Ops acK.cb_p QX0_0) (ubMulU k5Ops acK.ca_p QX0_1))).eval 1 = 0 := by
    rw [hQX0_0, hQX0_1, hdYF0_0, hdYF0_1]
    simp only [evalUBivLK5_ubSub, evalUBivLK5_ubSc, evalUBivLK5_ubBmul, evalUBivLK5_ubMulU,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      hcb_e1, hca_e1, hbr_e1.1, hbr_e1.2.1, hbr_e1.2.2.1,
      hgsqP.2.2.2.2.1.2.2.2.1, hgsqP.2.2.2.2.1.2.2.2.2.1, hgsqP.2.2.2.2.1.2.2.2.2.2]; ring
  have hdQX1_e1 : (evalUBivLK5 (ubSub k5Ops (ubMulU k5Ops acK.cb_p QX1_0) (ubMulU k5Ops acK.ca_p QX1_1))).eval 1 = 0 := by
    rw [hQX1_0, hQX1_1, hdYF1_0, hdYF1_1, homF1_0, homF1_1]
    simp only [evalUBivLK5_ubAdd, evalUBivLK5_ubSub, evalUBivLK5_ubNeg, evalUBivLK5_ubSc, evalUBivLK5_ubBmul, evalUBivLK5_ubMulU,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_C,
      hcb_e1, hca_e1, hbr_e1.2.2.2.1, hbr_e1.2.2.2.2.1, hbr_e1.2.2.2.2.2, hPY_K,
      hgsqP.2.2.2.2.1.2.2.2.1, hgsqP.2.2.2.2.1.2.2.2.2.1, hgsqP.2.2.2.2.1.2.2.2.2.2,
      hgsqP.2.2.2.2.2.2.2.2.2.1.2.1, hgsqP.2.2.2.2.2.2.2.2.2.1.2.2.2.1, hgsqP.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2]; ring
  have hrem0 : evalBivLK5 div0.1 = 0 := by
    rw [hdiv0]
    have h := congrArg (fun p : K5[X] => p.eval 1)
      (evalUBivLK5_ubSynDiv1Rem (ubSub k5Ops (ubMulU k5Ops acK.cb_p QX0_0) (ubMulU k5Ops acK.ca_p QX0_1)))
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_one, sub_self, zero_mul, add_zero, hdQX0_e1] at h
    exact h.symm
  have hrem1 : evalBivLK5 div1.1 = 0 := by
    rw [hdiv1]
    have h := congrArg (fun p : K5[X] => p.eval 1)
      (evalUBivLK5_ubSynDiv1Rem (ubSub k5Ops (ubMulU k5Ops acK.cb_p QX1_0) (ubMulU k5Ops acK.ca_p QX1_1)))
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_one, sub_self, zero_mul, add_zero, hdQX1_e1] at h
    exact h.symm
  -- `A_C` evaluation of `QX`, `QY`, `EB`, `q1`!
  have hdQX_AC :
      polyC (evalUBivLK5 (ubSub k5Ops (ubMulU k5Ops acK.cb_p QX0_0) (ubMulU k5Ops acK.ca_p QX0_1))) +
      V_C * polyC (evalUBivLK5 (ubSub k5Ops (ubMulU k5Ops acK.cb_p QX1_0) (ubMulU k5Ops acK.ca_p QX1_1))) =
      2893401 * QX_dot := by
    rw [hQX0_0, hQX0_1, hQX1_0, hQX1_1, hdYF0_0, hdYF0_1, hdYF1_0, hdYF1_1, homF1_0, homF1_1,
      hbr0_0, hbr0_1, hbr0_3, hbr1_0, hbr1_1, hbr1_3]
    simp only [evalUBivLK5_ubAdd, evalUBivLK5_ubSub, evalUBivLK5_ubNeg, evalUBivLK5_ubSc, evalUBivLK5_ubBmul, evalUBivLK5_ubMulU, polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_C, polyC_ofNat, hST', hST2', hPY_K,
      map_mul, map_ofNat, hca_p, hcb_p, hgsqP.2.2.1, hDY2, hdDY2,
      hgsqP.2.2.2.2.1.1, hgsqP.2.2.2.2.1.2.1, hgsqP.2.2.2.2.1.2.2.1,
      hgsqP.2.2.2.2.2.1.1, hgsqP.2.2.2.2.2.2.1.1, hgsqP.2.2.2.2.2.2.2.1.1, hgsqP.2.2.2.2.2.2.2.2.1.1,
      hgsqP.2.2.2.2.2.2.2.2.2.1.1, hgsqP.2.2.2.2.2.2.2.2.2.1.2.2.1, hgsqP.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1]; dsimp only [k5Ops, ringOps]; simp only [map_neg, map_mul, map_ofNat]
    have hd0 : dDY2_fn 0 T y = 0 := rfl
    have hd1 : dDY2_fn 1 T y = 0 := rfl
    have hd3 : dDY2_fn 3 T y = 0 := rfl
    simp only [QX_dot, QX_num, Omega_F, dDY2_F, F_contract, om_fn, br_fn, hd0, hd1, hd3, dLY_fn
      ]
    dsimp only [S, Q, T, x, y] at hLY_eq ⊢
    linear_combination -107163 * DX2_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 x_K) * ιC_K5 S_K * ιC_K5 T_K ^ 2 * dDY2_fn 4 (ιC_K5 T_K) (ιC_K5 y_K) *
      (dF5_fn 3 (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) * ((2 * ιC_K5 S_K * dLX_fn 0 U_C + LX_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 x_K) U_C) * cb - 2 * ιC_K5 S_K * dLX_fn 1 U_C * ca) -
       2 * ιC_K5 S_K * dLX_fn 3 U_C * (dF5_fn 0 (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) * cb - dF5_fn 1 (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) * ca)) * hLY_eq
  have hqX_AC : polyC (evalUBivLK5 div0.2) + V_C * polyC (evalUBivLK5 div1.2) = 321489 * (QX_dot / u_of U_C) := by
    have h0 := congrArg polyC (evalUBivLK5_ubSynDiv1Rem (ubSub k5Ops (ubMulU k5Ops acK.cb_p QX0_0) (ubMulU k5Ops acK.ca_p QX0_1)))
    have h1 := congrArg polyC (evalUBivLK5_ubSynDiv1Rem (ubSub k5Ops (ubMulU k5Ops acK.cb_p QX1_0) (ubMulU k5Ops acK.ca_p QX1_1)))
    rw [← hdiv0, hrem0, map_zero, zero_add, polyC_mul, polyC_sub, polyC_X, polyC_one] at h0
    rw [← hdiv1, hrem1, map_zero, zero_add, polyC_mul, polyC_sub, polyC_X, polyC_one] at h1
    have hu_ne : U_C - 1 ≠ 0 := fun h => u_of_U_C_ne_zero (by simp [u_of, h])
    apply mul_left_cancel₀ hu_ne
    calc (U_C - 1) * (polyC (evalUBivLK5 div0.2) + V_C * polyC (evalUBivLK5 div1.2)) =
          polyC (evalUBivLK5 (ubSub k5Ops (ubMulU k5Ops acK.cb_p QX0_0) (ubMulU k5Ops acK.ca_p QX0_1))) +
          V_C * polyC (evalUBivLK5 (ubSub k5Ops (ubMulU k5Ops acK.cb_p QX1_0) (ubMulU k5Ops acK.ca_p QX1_1))) := by
            rw [h0, h1]; ring
      _ = 2893401 * QX_dot := hdQX_AC
      _ = (U_C - 1) * (321489 * (QX_dot / u_of U_C)) := by
          have hu := u_of_U_C_ne_zero; rw [u_of] at hu ⊢; field_simp [hu]; ring
  have hQYd0_AC : polyC (evalUBivLK5 QY_dot_0_sc) =
      2893401 * (QY_num S Q T x y U_C 0 0 * cb - QY_num S Q T x y U_C 0 1 * ca) := by
    rw [hQYd0, hQY0_0, hQY0_1, hdXF0_0, hdXF0_1, hbr0_0, hbr0_1, hbr0_3]
    simp only [evalUBivLK5_ubSub, evalUBivLK5_ubNeg, evalUBivLK5_ubSc, evalUBivLK5_ubBmul, evalUBivLK5_ubMulU, polyC_sub, polyC_neg, polyC_mul, polyC_C, hST', hST2',
      map_mul, hca_p, hcb_p, hDY2, hdF5_4_eq, hLY0_AC,
      hgsqP.2.2.2.1.1, hgsqP.2.2.2.1.2.1, hgsqP.2.2.2.1.2.2,
      hgsqP.2.2.2.2.2.1.1, hgsqP.2.2.2.2.2.2.1.1, hgsqP.2.2.2.2.2.2.2.1.1, hgsqP.2.2.2.2.2.2.2.2.1.1]; dsimp only [k5Ops, ringOps]; simp only [map_neg, map_mul, map_ofNat]
    have hd4 : dDX2_fn 4 S Q x = 0 := rfl
    have hdX4 : dLX_fn 4 U_C = 0 := rfl
    simp only [QY_num, Omega_F, dDX2_F, F_contract, om_fn, br_fn, hd4, hdX4, dLY_fn
      ]
    dsimp only [S, Q, T, x, y]; ring
  have hDYqE_eq : polyC (evalUBivLK5 DY2_qE_63) =
      63 * DY2_of T y * (4 * S ^ 2 * T ^ 2 *
        (((-5250 * S ^ 4 + 30450 * S ^ 3 * Q - 64050 * S ^ 2 * Q ^ 2 + 63000 * S * Q ^ 3 - 28350 * Q ^ 4 +
            6250 * S ^ 2 * Q - 15000 * S * Q ^ 2 + 6750 * Q ^ 3 + 6250 * S ^ 2 - 15000 * S * Q + 6750 * Q ^ 2) +
          (336 * S ^ 4 - 2856 * S ^ 3 * Q + 8484 * S ^ 2 * Q ^ 2 - 10080 * S * Q ^ 3 + 3780 * Q ^ 4 -
            40 * S ^ 2 * Q + 240 * S * Q ^ 2 - 360 * Q ^ 3 - 40 * S ^ 2 + 240 * S * Q - 360 * Q ^ 2) * U_C) +
         x * ((6090 * S ^ 3 - 25620 * S ^ 2 * Q + 34650 * S * Q ^ 2 - 20790 * Q ^ 3 -
            6750 * S * Q + 4050 * Q ^ 2 - 6750 * S + 4050 * Q) +
          (-420 * S ^ 3 + 2940 * S ^ 2 * Q - 6300 * S * Q ^ 2 + 3780 * Q ^ 3) * U_C)) / 63) := by
    rw [hDYqE, evalUBivLK5_ubBmul, polyC_mul, polyC_C, hDY2, hqE_63, hc4S2T2, hgsqP.2.1, hT2']
    simp only [evalUBivLK5, evalUBivL, evalBivL, evalYList, k5Ops, ringOps, Int.cast_ofNat,
      hgsqP.2.2.2.2.2.2.2.2.2.2.2.2.1, hgsqP.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hgsqP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hgsqP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
      polyC_add, polyC_sub, polyC_neg, polyC_mul, polyC_pow, polyC_C, polyC_X, polyC_ofNat, S, Q, T, x, y,
      map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, mul_zero, add_zero]; ring
  have hAv_A : ιC_K5 k5Params.Av0 = -(4 / 243 : A_C) * (T - 3) ^ 3 := by
    simp only [CoverParams.Av0, CoverParams.inv243, k5Params_inv3, k5Params_T, T,
      map_mul, map_sub, map_neg, map_inv₀, map_pow, map_ofNat]; ring
  have hCv_A : ιC_K5 k5Params.Cv0 = -(25 / 243 : A_C) * T * (5 * T - 9) ^ 2 := by
    simp only [CoverParams.Cv0, CoverParams.inv243, k5Params_inv3, k5Params_T, T,
      map_mul, map_sub, map_neg, map_inv₀, map_pow, map_ofNat]; ring
  have hqY_AC : polyC (evalUBivLK5 qY_0_321489) -
      9 * (321489 / 63 : A_C) * polyC (evalUBivLK5 DY2_qE_63) * U_C * ιC_K5 k5Params.Av0 * V_C =
      321489 * (QY_dot / v_of V_C) := by
    have hQY0_eq : polyC (evalUBivLK5 qY_0_321489) =
        -2893401 * (QY_num S Q T x y U_C 0 0 * cb - QY_num S Q T x y U_C 0 1 * ca) +
        189 * ιC_K5 Cv0_243 * U_C * polyC (evalUBivLK5 DY2_qE_63) := by
      rw [hqY0, evalUBivLK5_ubAdd, evalUBivLK5_ubNeg, evalUBivLK5_ubSc, evalUBivLK5_ubShift,
        polyC_add, polyC_neg, polyC_mul, polyC_mul, polyC_C, polyC_X, hQYd0_AC]
      simp only [k5Ops, ringOps, map_mul, map_ofNat, Int.cast_ofNat]; ring
    have hQY_lin : QY_dot = V_C * (QY_num S Q T x y U_C 1 0 * cb - QY_num S Q T x y U_C 1 1 * ca) -
        (V_C - 1) * (QY_num S Q T x y U_C 0 0 * cb - QY_num S Q T x y U_C 0 1 * ca) := by
      have h1 : ∀ i : Fin 3, QY_num S Q T x y U_C V_C i =
          V_C * QY_num S Q T x y U_C 1 i - (V_C - 1) * QY_num S Q T x y U_C 0 i := fun i => by
        fin_cases i <;> (simp only [QY_num, Omega_F, dDX2_F, F_contract, om_fn, br_fn, LY_of, dLY_fn, v3_of, v_of]; ring)
      simp only [QY_dot, h1 0, h1 1]; ring
    have hV1 := QY_dot_V1_ring S Q T x y U_C
    rw [← polyC_ca_cb_eq_q10_q20.1, ← polyC_ca_cb_eq_q10_q20.2] at hV1
    have hV_factor : V_C * (u_of U_C * A1_of S Q U_C 1 - 3 * U_C * (S * x ^ 2 + T * y ^ 2)) =
        -(V_C - 1) * U_C * (ιC_K5 k5Params.Av0 * V_C - ιC_K5 k5Params.Cv0) := by
      have hsp := E0_V_split S Q T U_C V_C
      have hHcub0 : H_cub S Q T 1 U_C V_C = 0 := by simpa [E_fn, S, Q, T] using E0_AC_zero 0 0
      rw [hHcub0, ← hAv_A, ← hCv_A] at hsp
      have hF5_0 : F5_of S Q T x y = 0 := F5_of_AC
      unfold F5_of at hF5_0
      linear_combination -hsp - U_C * V_C * hF5_0
    rw [hQY0_eq, hCv0, map_mul, map_ofNat, ← mul_div_assoc (321489 : A_C), eq_div_iff v_of_V_C_ne_zero, hQY_lin, hV1]
    have hcomb : V_C * (DY2_of T y *
        (4 * S ^ 2 * T ^ 2 *
          (((-5250 * S ^ 4 + 30450 * S ^ 3 * Q - 64050 * S ^ 2 * Q ^ 2 + 63000 * S * Q ^ 3 - 28350 * Q ^ 4 +
              6250 * S ^ 2 * Q - 15000 * S * Q ^ 2 + 6750 * Q ^ 3 + 6250 * S ^ 2 - 15000 * S * Q + 6750 * Q ^ 2) +
            (336 * S ^ 4 - 2856 * S ^ 3 * Q + 8484 * S ^ 2 * Q ^ 2 - 10080 * S * Q ^ 3 + 3780 * Q ^ 4 -
              40 * S ^ 2 * Q + 240 * S * Q ^ 2 - 360 * Q ^ 3 - 40 * S ^ 2 + 240 * S * Q - 360 * Q ^ 2) * U_C) +
           x * ((6090 * S ^ 3 - 25620 * S ^ 2 * Q + 34650 * S * Q ^ 2 - 20790 * Q ^ 3 -
              6750 * S * Q + 4050 * Q ^ 2 - 6750 * S + 4050 * Q) +
            (-420 * S ^ 3 + 2940 * S ^ 2 * Q - 6300 * S * Q ^ 2 + 3780 * Q ^ 3) * U_C)) / 63) *
        (u_of U_C * A1_of S Q U_C 1 - 3 * U_C * (S * x ^ 2 + T * y ^ 2))) =
        (polyC (evalUBivLK5 DY2_qE_63) / 63) * (-(V_C - 1) * U_C * (ιC_K5 k5Params.Av0 * V_C - ιC_K5 k5Params.Cv0)) := by
      rw [hDYqE_eq, ← hV_factor]; ring
    rw [hcomb, v_of]; ring
  have hEB_AC : polyC (evalUBivLK5 EB0_5103) + V_C * polyC (evalUBivLK5 EB1_5103) = 5103 * EB_of S Q T x y U_C V_C := by
    rw [hEB0, hEB1, hbr0_3, hbr1_3, hbr1_4]
    simp only [evalUBivLK5_ubSub, evalUBivLK5_ubSc, evalUBivLK5_ubBmul,
      polyC_sub, polyC_mul, polyC_C, hST2', 
      hW2_eq, hdF5_4_eq, hgsqP.2.2.2.2.1.2.2.1, hgsqP.2.2.2.2.2.2.2.2.1.1, hgsqP.2.2.2.2.2.1.1]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_ofNat, map_neg, map_mul, map_ofNat]
    have hdX4 : dLX_fn 4 U_C = 0 := rfl
    simp only [EB_of, W2_of, br_fn, hdX4, dLY_fn]
    dsimp only [S, Q, T, x, y] at hLY_eq ⊢
    linear_combination -378 * (ιC_K5 S_K * ιC_K5 T_K * DX2_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 x_K) * DY2_of (ιC_K5 T_K) (ιC_K5 y_K)) *
      dF5_fn 4 (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) *
      (2 * ιC_K5 S_K * ιC_K5 T_K * dLX_fn 3 U_C) * hLY_eq
  have hq1_AC : (M_mid_int : A_C) * q1_dot =
      ιC_K5 k5Params.Cv0 * U_C * polyC (evalUBivLK5 (ubAdd k5Ops (ubSc k5Ops (k5Ops.mul (k5Ops.ofInt (-9)) H0_7) div0.2)
        (ubSc k5Ops (k5Ops.ofInt 63) (ubMulU k5Ops gsqK.qC_63 EB0_5103)))) +
      (1 / 243 : A_C) * polyC (evalUBivLK5 (ubAdd k5Ops (ubSc k5Ops (k5Ops.mul (k5Ops.ofInt 9) H0_7) (ubMulU k5Ops gsqK.A1_1_27 qY_0_321489))
        (ubShift (ubAdd k5Ops (ubSc k5Ops (k5Ops.mul (k5Ops.ofInt 9) H0_7) (ubSub k5Ops (ubSc k5Ops Av0_243 div0.2) (ubSc k5Ops Cv0_243 div1.2)))
          (ubSc k5Ops (k5Ops.ofInt 63) (ubMulU k5Ops gsqK.qC_63 (ubSub k5Ops (ubSc k5Ops Cv0_243 EB1_5103) (ubSc k5Ops Av0_243 EB0_5103)))))))) * V_C +
      ιC_K5 k5Params.Av0 * U_C * polyC (evalUBivLK5 (ubSub k5Ops (ubAdd k5Ops (ubSc k5Ops (k5Ops.mul (k5Ops.ofInt (-1701)) H0_7)
        (ubMulU k5Ops gsqK.A1_1_27 DY2_qE_63)) (ubSc k5Ops (k5Ops.mul (k5Ops.ofInt 9) H0_7) div1.2))
        (ubSc k5Ops (k5Ops.ofInt 63) (ubMulU k5Ops gsqK.qC_63 EB1_5103)))) * V_C ^ 2 := by
    have hcA1_AC : cA1_dot / v_of V_C =
        (9 / 63 : A_C) * polyC (evalUPolyK5 gsqK.qC_63) * U_C * (ιC_K5 k5Params.Cv0 - ιC_K5 k5Params.Av0 * V_C) := by
      have hV1 := cA1_dot_V1_ring S Q T U_C
      rw [← polyC_ca_cb_eq_q10_q20.1, ← polyC_ca_cb_eq_q10_q20.2] at hV1
      have hqC_eq : polyC (evalUPolyK5 gsqK.qC_63) =
          (-5250 * S ^ 4 + 30450 * S ^ 3 * Q - 64050 * S ^ 2 * Q ^ 2 + 63000 * S * Q ^ 3 - 28350 * Q ^ 4 +
            6250 * S ^ 2 * Q - 15000 * S * Q ^ 2 + 6750 * Q ^ 3 + 6250 * S ^ 2 - 15000 * S * Q + 6750 * Q ^ 2) +
          (336 * S ^ 4 - 2856 * S ^ 3 * Q + 8484 * S ^ 2 * Q ^ 2 - 10080 * S * Q ^ 3 + 3780 * Q ^ 4 -
            40 * S ^ 2 * Q + 240 * S * Q ^ 2 - 360 * Q ^ 3 - 40 * S ^ 2 + 240 * S * Q - 360 * Q ^ 2) * U_C := by
        rw [hgsqP.2.2.2.2.2.2.2.2.2.2.2.1]; simp only [S, Q, map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat]
      have hcA1_V : cA1_dot = V_C * ((H0_of S Q T * dA1_fn 0 S Q U_C 1 - A1_of S Q U_C 1 * dH0_fn 0 S Q T) * cb -
          (H0_of S Q T * dA1_fn 1 S Q U_C 1 - A1_of S Q U_C 1 * dH0_fn 1 S Q T) * ca) := by
        simp only [cA1_dot, A1_of, dA1_fn]; ring
      have hsp := E0_V_split S Q T U_C V_C
      have hHcub0 : H_cub S Q T 1 U_C V_C = 0 := by simpa [E_fn, S, Q, T] using E0_AC_zero 0 0
      rw [hHcub0, ← hAv_A, ← hCv_A] at hsp
      rw [div_eq_iff v_of_V_C_ne_zero, hcA1_V, hV1, ← hqC_eq, v_of]
      linear_combination -(polyC (evalUPolyK5 gsqK.qC_63) / 63) * hsp
    have hB1_AC : B1_of T U_C V_C = 9 * U_C * (ιC_K5 k5Params.Av0 * V_C - ιC_K5 k5Params.Cv0) := by
      rw [B1_of_eq_Av0_Cv0, ← hAv_A, ← hCv_A]
    have hA1_V : A1_of S Q U_C V_C = V_C * A1_of S Q U_C 1 := by simp only [A1_of]; ring
    have hH0_AC : ιC_K5 H0_7 = 7 * H0_of S Q T := by
      rw [hH0]; simp only [H0_of, S, Q, T, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]
    have hAv0_AC : ιC_K5 Av0_243 = 243 * ιC_K5 k5Params.Av0 := by rw [hAv0]; simp [map_ofNat]
    have hCv0_AC : ιC_K5 Cv0_243 = 243 * ιC_K5 k5Params.Cv0 := by rw [hCv0]; simp [map_ofNat]
    simp only [evalUBivLK5_ubAdd, evalUBivLK5_ubSub, evalUBivLK5_ubSc, evalUBivLK5_ubShift, evalUBivLK5_ubMulU, polyC_add, polyC_sub, polyC_mul, polyC_C, polyC_X, 
      hgsqP.2.2.2.2.2.2.2.2.2.2.1]; dsimp only [k5Ops, ringOps]; simp only [Int.cast_neg, Int.cast_ofNat, map_neg, map_mul, map_ofNat, hH0_AC, hAv0_AC, hCv0_AC]
    dsimp only [q1_dot]
    rw [hA1_V, hB1_AC, hcA1_AC, show M_mid_int = 2250423 from rfl]
    push_cast
    linear_combination (7 * H0_of S Q T * A1_of S Q U_C 1 * V_C) * (-hqY_AC) +
      (7 * H0_of S Q T * (9 * U_C * (ιC_K5 k5Params.Av0 * V_C - ιC_K5 k5Params.Cv0))) * (-hqX_AC) +
      (63 * polyC (evalUPolyK5 gsqK.qC_63) * U_C * (ιC_K5 k5Params.Cv0 - ιC_K5 k5Params.Av0 * V_C)) * (-hEB_AC)
  -- `U = 0` vanishing for `R13_int_p_eval_zero`!
  have hqX0_e0 : (evalUBivLK5 div0.2).eval 0 = 0 := by
    have h0 := congrArg (fun p : K5[X] => p.eval 0)
      (evalUBivLK5_ubSynDiv1Rem (ubSub k5Ops (ubMulU k5Ops acK.cb_p QX0_0) (ubMulU k5Ops acK.ca_p QX0_1)))
    rw [← hdiv0, hrem0, map_zero, zero_add] at h0
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one, zero_sub, neg_mul, one_mul] at h0
    have hd0 : (evalUBivLK5 (ubSub k5Ops (ubMulU k5Ops acK.cb_p QX0_0) (ubMulU k5Ops acK.ca_p QX0_1))).eval 0 = 0 := by
      rw [hQX0_0, hQX0_1, hdYF0_0, hdYF0_1]
      simp only [evalUBivLK5_ubSub, evalUBivLK5_ubSc, evalUBivLK5_ubBmul, evalUBivLK5_ubMulU,
        Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hbr0_3_e0, mul_zero, sub_zero]
      linear_combination evalBivLK5 gsqK.DX2 * ST * evalBivLK5 gsqK.dF5_3 * evalBivLK5 dDY2_dy * hbr0_cancel
    rw [hd0] at h0; exact neg_eq_zero.mp h0.symm
  have hqY0_e0 : (evalUBivLK5 qY_0_321489).eval 0 = 0 := by
    rw [hqY0, hQYd0, hQY0_0, hQY0_1, hdXF0_0, hdXF0_1]
    simp only [evalUBivLK5_ubAdd, evalUBivLK5_ubSub, evalUBivLK5_ubNeg, evalUBivLK5_ubSc,
      evalUBivLK5_ubBmul, evalUBivLK5_ubMulU, evalUBivLK5_ubShift,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, hbr0_3_e0, mul_zero, zero_mul, zero_sub, add_zero]
    linear_combination -evalBivLK5 DY2 * ST * evalBivLK5 dF5_4 * evalBivLK5 gsqK.dDX2_dx * hbr0_cancel
  have hEB0_e0 : (evalUBivLK5 EB0_5103).eval 0 = 0 := by
    rw [hEB0]; simp [evalUBivLK5_ubSc, evalUBivLK5_ubBmul, hbr0_3_e0]
  refine ⟨hH0, hH0_2, hAv0, hCv0, hCv0i, hBv1701, hqX_AC, hqY_AC, hq1_AC, ⟨hqX0_e0, hqY0_e0, ?_, ?_⟩⟩
  · simp [evalUBivLK5_ubAdd, evalUBivLK5_ubSc, evalUBivLK5_ubMulU, hqX0_e0, hEB0_e0]
  · simp [evalUBivLK5_ubAdd, evalUBivLK5_ubSc, evalUBivLK5_ubShift, evalUBivLK5_ubMulU, hqY0_e0]


end SymmetricSexticResidual.LocalResidueQ5

theorem solution : SymmetricSexticResidual.LocalResidueQ5.Q5GeomBridgeSpec :=
  ⟨SymmetricSexticResidual.LocalResidueQ5.evalGeomT_K5_props⟩
