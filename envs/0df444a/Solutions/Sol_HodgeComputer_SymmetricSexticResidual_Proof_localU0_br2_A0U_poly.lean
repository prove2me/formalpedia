-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localU0_br2_A0U_poly
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T13:19:43.16949+00:00
-- url     : https://prove2.me/submissions/544c5492-407f-48ef-b9cc-82a25714fb3b

import Definitions.Def_HodgeComputerFormal_LaurentJets

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueU0
open QuadraticCovers

private def br2_0_m_sc {F : Type*} [Field F] (S Q T : F) (mi : Fin 10) : Dual F :=
  let B := T - 3
  let d_ab := 6 * S * B
  let a_s : Dual F := ⟨6 * S ^ 2, 6 * S * B⟩
  let b_s : Dual F := ⟨6 * S * Q, (5 * S - 3 * Q) * B⟩
  let ξS_s : Dual F := ⟨-18 * S ^ 2, -6 * S * B * T⟩
  let ξQ_s : Dual F := ⟨-18 * S * Q, -(5 * S - 3 * Q) * B * T⟩
  let dHS_v := fun s q : Dual F => Dual.C (-(25 / 243 : F)) * (5 * s - 9 * q) * (15 * s - 9 * q)
  let dHS_e := fun s q : Dual F =>
    Dual.C (143 / 81 : F) * s ^ 2 - Dual.C (184 / 27 : F) * s * q + Dual.C (52 / 9 : F) * q ^ 2
  let dHQ_v := fun s q : Dual F => Dual.C (50 / 27 : F) * s * (5 * s - 9 * q)
  let dHQ_e := fun (s q : Dual F) (v0 : F) =>
    Dual.C (-(92 / 27 : F)) * s ^ 2 + Dual.C (104 / 9 : F) * s * q - Dual.C (22 / 3 : F) * q ^ 2 +
      Dual.C ((10 / 7 : F) * v0) * q + Dual.C ((10 / 7 : F) * v0 ^ 2)
  let a2_v := dHS_v a_s b_s; let a2_e := dHS_e a_s b_s
  let a0_v := dHS_v ξS_s ξQ_s; let a0_e := dHS_e ξS_s ξQ_s
  let a1_v := dHS_v (a_s + ξS_s) (b_s + ξQ_s) - a2_v - a0_v
  let a1_e := dHS_e (a_s + ξS_s) (b_s + ξQ_s) - a2_e - a0_e
  let b2_v := dHQ_v a_s b_s; let b2_e := dHQ_e a_s b_s 0
  let b0_v := dHQ_v ξS_s ξQ_s; let b0_e := dHQ_e ξS_s ξQ_s d_ab
  let b1_v := dHQ_v (a_s + ξS_s) (b_s + ξQ_s) - b2_v - b0_v
  let b1_e := dHQ_e (a_s + ξS_s) (b_s + ξQ_s) 0 - b2_e - dHQ_e ξS_s ξQ_s 0 + Dual.C ((10 / 7 : F) * d_ab) * b_s
  let d20_e := a2_v * b0_e + a2_e * b0_v - a0_v * b2_e - a0_e * b2_v
  let d21_e := a2_v * b1_e + a2_e * b1_v - a1_v * b2_e - a1_e * b2_v
  let d10_e := a1_v * b0_e + a1_e * b0_v - a0_v * b1_e - a0_e * b1_v
  let (m2, m1, m0) : Dual F × Dual F × Dual F := match mi with
    | 0 => (a_s ^ 2, 2 * a_s * ξS_s, ξS_s ^ 2)
    | 1 => (a_s * b_s, a_s * ξQ_s + b_s * ξS_s, ξS_s * ξQ_s)
    | 2 => (b_s ^ 2, 2 * b_s * ξQ_s, ξQ_s ^ 2)
    | 3 => (Dual.C d_ab * a_s, Dual.C d_ab * ξS_s, 0)
    | 4 => (0, Dual.C d_ab * a_s, Dual.C d_ab * ξS_s)
    | 5 => (Dual.C d_ab * b_s, Dual.C d_ab * ξQ_s, 0)
    | 6 => (0, Dual.C d_ab * b_s, Dual.C d_ab * ξQ_s)
    | 7 => (Dual.C (d_ab ^ 2), 0, 0)
    | 8 => (0, Dual.C (d_ab ^ 2), 0)
    | 9 => (0, 0, Dual.C (d_ab ^ 2))
  Dual.C (1 / 16 : F) * (m2 * d10_e - m1 * d20_e + m0 * d21_e)

private lemma br2_0_A0U_scaled_poly {F : Type*} [Field F] [CharZero F] (S Q T : F) :
    let A := 5 * S - 9 * Q
    let B := T - 3
    let d_ab := 6 * S * B
    let Q_quad := 11943020 * S ^ 2 - 876486 * S * Q + 8382500 * S * T +
      5029500 * Q * T - 14837025 * S - 33647355 * Q
    Dual.C (-(19708 / 1257375 : F)) * (5 * br2_0_m_sc S Q T 0 - 9 * br2_0_m_sc S Q T 1) +
      Dual.C (1472 / 1257375 : F) * (5 * br2_0_m_sc S Q T 1 - 9 * br2_0_m_sc S Q T 2) -
      Dual.C (16 / 729 : F) * (5 * br2_0_m_sc S Q T 3 - 9 * br2_0_m_sc S Q T 5) +
      Dual.C (188 / 2025 : F) * (5 * br2_0_m_sc S Q T 4 - 9 * br2_0_m_sc S Q T 6) =
    Dual.C (d_ab ^ 3) * ⟨(8248380 / 51331077 : F) * (5 * S - 3 * Q) * S ^ 3 * A ^ 2,
      -(2 / 51331077 : F) * B * S ^ 2 * A ^ 2 * Q_quad⟩ := by
  intro A B d_ab Q_quad
  let a_s : Dual F := ⟨6 * S ^ 2, 6 * S * B⟩
  let b_s : Dual F := ⟨6 * S * Q, (5 * S - 3 * Q) * B⟩
  let ξS_s : Dual F := ⟨-18 * S ^ 2, -6 * S * B * T⟩
  let ξQ_s : Dual F := ⟨-18 * S * Q, -(5 * S - 3 * Q) * B * T⟩
  let dHS_v := fun s q : Dual F => Dual.C (-(25 / 243 : F)) * (5 * s - 9 * q) * (15 * s - 9 * q)
  let dHS_e := fun s q : Dual F =>
    Dual.C (143 / 81 : F) * s ^ 2 - Dual.C (184 / 27 : F) * s * q + Dual.C (52 / 9 : F) * q ^ 2
  let dHQ_v := fun s q : Dual F => Dual.C (50 / 27 : F) * s * (5 * s - 9 * q)
  let dHQ_e := fun (s q : Dual F) (v0 : F) =>
    Dual.C (-(92 / 27 : F)) * s ^ 2 + Dual.C (104 / 9 : F) * s * q - Dual.C (22 / 3 : F) * q ^ 2 +
      Dual.C ((10 / 7 : F) * v0) * q + Dual.C ((10 / 7 : F) * v0 ^ 2)
  let a2_v := dHS_v a_s b_s; let a2_e := dHS_e a_s b_s
  let a0_v := dHS_v ξS_s ξQ_s; let a0_e := dHS_e ξS_s ξQ_s
  let a1_v := dHS_v (a_s + ξS_s) (b_s + ξQ_s) - a2_v - a0_v
  let a1_e := dHS_e (a_s + ξS_s) (b_s + ξQ_s) - a2_e - a0_e
  let b2_v := dHQ_v a_s b_s; let b2_e := dHQ_e a_s b_s 0
  let b0_v := dHQ_v ξS_s ξQ_s; let b0_e := dHQ_e ξS_s ξQ_s d_ab
  let b1_v := dHQ_v (a_s + ξS_s) (b_s + ξQ_s) - b2_v - b0_v
  let b1_e := dHQ_e (a_s + ξS_s) (b_s + ξQ_s) 0 - b2_e - dHQ_e ξS_s ξQ_s 0 + Dual.C ((10 / 7 : F) * d_ab) * b_s
  set d20 : Dual F := a2_v * b0_e + a2_e * b0_v - a0_v * b2_e - a0_e * b2_v
  set d21 : Dual F := a2_v * b1_e + a2_e * b1_v - a1_v * b2_e - a1_e * b2_v
  set d10 : Dual F := a1_v * b0_e + a1_e * b0_v - a0_v * b1_e - a0_e * b1_v
  have hd20 : d20 =
      ⟨-(4000 / 7 : F) * B * (-3 * Q + B) * (-5 * S + 3 * Q) * (-A) * S ^ 4,
       -(400 / 21 : F) * (-A) * B ^ 2 * S ^ 3 *
         (259 * S ^ 3 - 1722 * S ^ 2 * Q + 1932 * S * Q ^ 2 + 125 * S ^ 2 * T -
           150 * S * Q * T + 45 * Q ^ 2 * T + 270 * Q ^ 2 - 90 * Q * T + 270 * Q)⟩ := by
    ext <;> (simp only [d20, a2_v, a2_e, a0_v, a0_e, b2_v, b2_e, b0_v, b0_e,
      dHS_v, dHS_e, dHQ_v, dHQ_e, a_s, b_s, ξS_s, ξQ_s, d_ab, A, B,
      Dual.C_val, Dual.C_eps, Dual.add_val, Dual.sub_val, Dual.mul_val, Dual.pow_eq,
      Dual.add_eps, Dual.sub_eps, Dual.mul_eps, Dual.ofNat_val, Dual.ofNat_eps,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, add_zero, mul_zero, zero_mul]; ring)
  have hd21 : d21 =
      ⟨-(4000 / 7 : F) * B * Q * (-5 * S + 3 * Q) * (-A) * S ^ 4,
       (400 / 63 : F) * (-A) * B ^ 2 * S ^ 3 *
         (259 * S ^ 3 - 1722 * S ^ 2 * Q + 1932 * S * Q ^ 2 + 375 * S ^ 2 - 450 * S * Q + 405 * Q ^ 2)⟩ := by
    ext <;> (simp only [d21, a2_v, a2_e, a1_v, a1_e, a0_v, a0_e, b2_v, b2_e, b1_v, b1_e, b0_v, 
      dHS_v, dHS_e, dHQ_v, dHQ_e, a_s, b_s, ξS_s, ξQ_s, d_ab, A, B,
      Dual.C_val, Dual.C_eps, Dual.add_val, Dual.sub_val, Dual.mul_val, Dual.pow_eq,
      Dual.add_eps, Dual.sub_eps, Dual.mul_eps, Dual.ofNat_val, Dual.ofNat_eps,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, add_zero, mul_zero, zero_mul]; ring)
  have hd10 : d10 =
      ⟨(12000 / 7 : F) * B * (-3 * Q + 2 * B) * (-5 * S + 3 * Q) * (-A) * S ^ 4,
       -(400 / 7 : F) * (-A) * B ^ 2 * S ^ 3 *
         (-259 * S ^ 3 + 1722 * S ^ 2 * Q - 1932 * S * Q ^ 2 - 250 * S ^ 2 * T +
           300 * S * Q * T - 90 * Q ^ 2 * T + 30 * Q * T ^ 2 + 375 * S ^ 2 - 450 * S * Q - 135 * Q ^ 2 - 270 * Q)⟩ := by
    ext <;> (simp only [d10, a2_v, a2_e, a1_v, a1_e, a0_v, a0_e, b2_v, b2_e, b1_v, b1_e, b0_v, b0_e,
      dHS_v, dHS_e, dHQ_v, dHQ_e, a_s, b_s, ξS_s, ξQ_s, d_ab, A, B,
      Dual.C_val, Dual.C_eps, Dual.add_val, Dual.sub_val, Dual.mul_val, Dual.pow_eq,
      Dual.add_eps, Dual.sub_eps, Dual.mul_eps, Dual.ofNat_val, Dual.ofNat_eps,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, add_zero, mul_zero, zero_mul]; ring)
  have hbr_m (mi : Fin 10) : br2_0_m_sc S Q T mi =
      let (m2, m1, m0) : Dual F × Dual F × Dual F := match mi with
        | 0 => (a_s ^ 2, 2 * a_s * ξS_s, ξS_s ^ 2)
        | 1 => (a_s * b_s, a_s * ξQ_s + b_s * ξS_s, ξS_s * ξQ_s)
        | 2 => (b_s ^ 2, 2 * b_s * ξQ_s, ξQ_s ^ 2)
        | 3 => (Dual.C d_ab * a_s, Dual.C d_ab * ξS_s, 0)
        | 4 => (0, Dual.C d_ab * a_s, Dual.C d_ab * ξS_s)
        | 5 => (Dual.C d_ab * b_s, Dual.C d_ab * ξQ_s, 0)
        | 6 => (0, Dual.C d_ab * b_s, Dual.C d_ab * ξQ_s)
        | 7 => (Dual.C (d_ab ^ 2), 0, 0)
        | 8 => (0, Dual.C (d_ab ^ 2), 0)
        | 9 => (0, 0, Dual.C (d_ab ^ 2))
      Dual.C (1 / 16 : F) * (m2 * d10 - m1 * d20 + m0 * d21) := rfl
  have hlin :
      Dual.C (-(19708 / 1257375 : F)) * (5 * br2_0_m_sc S Q T 0 - 9 * br2_0_m_sc S Q T 1) +
        Dual.C (1472 / 1257375 : F) * (5 * br2_0_m_sc S Q T 1 - 9 * br2_0_m_sc S Q T 2) -
        Dual.C (16 / 729 : F) * (5 * br2_0_m_sc S Q T 3 - 9 * br2_0_m_sc S Q T 5) +
        Dual.C (188 / 2025 : F) * (5 * br2_0_m_sc S Q T 4 - 9 * br2_0_m_sc S Q T 6) =
      Dual.C (1 / 16 : F) *
        ((Dual.C (-(19708 / 1257375 : F)) * (5 * a_s ^ 2 - 9 * (a_s * b_s)) +
          Dual.C (1472 / 1257375 : F) * (5 * (a_s * b_s) - 9 * b_s ^ 2) -
          Dual.C (16 / 729 : F) * (5 * (Dual.C d_ab * a_s) - 9 * (Dual.C d_ab * b_s))) * d10 -
         (Dual.C (-(19708 / 1257375 : F)) * (5 * (2 * a_s * ξS_s) - 9 * (a_s * ξQ_s + b_s * ξS_s)) +
          Dual.C (1472 / 1257375 : F) * (5 * (a_s * ξQ_s + b_s * ξS_s) - 9 * (2 * b_s * ξQ_s)) -
          Dual.C (16 / 729 : F) * (5 * (Dual.C d_ab * ξS_s) - 9 * (Dual.C d_ab * ξQ_s)) +
          Dual.C (188 / 2025 : F) * (5 * (Dual.C d_ab * a_s) - 9 * (Dual.C d_ab * b_s))) * d20 +
         (Dual.C (-(19708 / 1257375 : F)) * (5 * ξS_s ^ 2 - 9 * (ξS_s * ξQ_s)) +
          Dual.C (1472 / 1257375 : F) * (5 * (ξS_s * ξQ_s) - 9 * ξQ_s ^ 2) +
          Dual.C (188 / 2025 : F) * (5 * (Dual.C d_ab * ξS_s) - 9 * (Dual.C d_ab * ξQ_s))) * d21) := by
    rw [hbr_m 0, hbr_m 1, hbr_m 2, hbr_m 3, hbr_m 4, hbr_m 5, hbr_m 6]
    ring
  rw [hlin, hd10, hd20, hd21]
  ext <;> (simp only [a_s, b_s, ξS_s, ξQ_s, d_ab, A, B, Q_quad,
    Dual.C_val, Dual.C_eps, Dual.add_val, Dual.sub_val, Dual.mul_val, Dual.pow_eq,
    Dual.add_eps, Dual.sub_eps, Dual.mul_eps, Dual.ofNat_val, Dual.ofNat_eps,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, add_zero, zero_mul]; ring)



end SymmetricSexticResidual.LocalResidueU0

theorem solution :
    ∀ {F : Type} [Field F] [CharZero F] (S Q T : F),
      let B := T - 3
      let A := 5 * S - 9 * Q
      let d_ab := 6 * S * B
      let Q_quad := 11943020 * S ^ 2 - 876486 * S * Q + 8382500 * S * T +
        5029500 * Q * T - 14837025 * S - 33647355 * Q
      let m_sc : Fin 10 → QuadraticCovers.Dual F := fun mi =>
        let a_s : QuadraticCovers.Dual F := ⟨6 * S ^ 2, 6 * S * B⟩
        let b_s : QuadraticCovers.Dual F := ⟨6 * S * Q, (5 * S - 3 * Q) * B⟩
        let ξS_s : QuadraticCovers.Dual F := ⟨-18 * S ^ 2, -6 * S * B * T⟩
        let ξQ_s : QuadraticCovers.Dual F := ⟨-18 * S * Q, -(5 * S - 3 * Q) * B * T⟩
        let dHS_v := fun s q : QuadraticCovers.Dual F => QuadraticCovers.Dual.C (-(25 / 243 : F)) * (5 * s - 9 * q) * (15 * s - 9 * q)
        let dHS_e := fun s q : QuadraticCovers.Dual F =>
          QuadraticCovers.Dual.C (143 / 81 : F) * s ^ 2 - QuadraticCovers.Dual.C (184 / 27 : F) * s * q + QuadraticCovers.Dual.C (52 / 9 : F) * q ^ 2
        let dHQ_v := fun s q : QuadraticCovers.Dual F => QuadraticCovers.Dual.C (50 / 27 : F) * s * (5 * s - 9 * q)
        let dHQ_e := fun (s q : QuadraticCovers.Dual F) (v0 : F) =>
          QuadraticCovers.Dual.C (-(92 / 27 : F)) * s ^ 2 + QuadraticCovers.Dual.C (104 / 9 : F) * s * q - QuadraticCovers.Dual.C (22 / 3 : F) * q ^ 2 +
            QuadraticCovers.Dual.C ((10 / 7 : F) * v0) * q + QuadraticCovers.Dual.C ((10 / 7 : F) * v0 ^ 2)
        let a2_v := dHS_v a_s b_s; let a2_e := dHS_e a_s b_s
        let a0_v := dHS_v ξS_s ξQ_s; let a0_e := dHS_e ξS_s ξQ_s
        let a1_v := dHS_v (a_s + ξS_s) (b_s + ξQ_s) - a2_v - a0_v
        let a1_e := dHS_e (a_s + ξS_s) (b_s + ξQ_s) - a2_e - a0_e
        let b2_v := dHQ_v a_s b_s; let b2_e := dHQ_e a_s b_s 0
        let b0_v := dHQ_v ξS_s ξQ_s; let b0_e := dHQ_e ξS_s ξQ_s d_ab
        let b1_v := dHQ_v (a_s + ξS_s) (b_s + ξQ_s) - b2_v - b0_v
        let b1_e := dHQ_e (a_s + ξS_s) (b_s + ξQ_s) 0 - b2_e - dHQ_e ξS_s ξQ_s 0 + QuadraticCovers.Dual.C ((10 / 7 : F) * d_ab) * b_s
        let d20_e := a2_v * b0_e + a2_e * b0_v - a0_v * b2_e - a0_e * b2_v
        let d21_e := a2_v * b1_e + a2_e * b1_v - a1_v * b2_e - a1_e * b2_v
        let d10_e := a1_v * b0_e + a1_e * b0_v - a0_v * b1_e - a0_e * b1_v
        let (m2, m1, m0) : QuadraticCovers.Dual F × QuadraticCovers.Dual F × QuadraticCovers.Dual F := match mi with
          | 0 => (a_s ^ 2, 2 * a_s * ξS_s, ξS_s ^ 2)
          | 1 => (a_s * b_s, a_s * ξQ_s + b_s * ξS_s, ξS_s * ξQ_s)
          | 2 => (b_s ^ 2, 2 * b_s * ξQ_s, ξQ_s ^ 2)
          | 3 => (QuadraticCovers.Dual.C d_ab * a_s, QuadraticCovers.Dual.C d_ab * ξS_s, 0)
          | 4 => (0, QuadraticCovers.Dual.C d_ab * a_s, QuadraticCovers.Dual.C d_ab * ξS_s)
          | 5 => (QuadraticCovers.Dual.C d_ab * b_s, QuadraticCovers.Dual.C d_ab * ξQ_s, 0)
          | 6 => (0, QuadraticCovers.Dual.C d_ab * b_s, QuadraticCovers.Dual.C d_ab * ξQ_s)
          | 7 => (QuadraticCovers.Dual.C (d_ab ^ 2), 0, 0)
          | 8 => (0, QuadraticCovers.Dual.C (d_ab ^ 2), 0)
          | 9 => (0, 0, QuadraticCovers.Dual.C (d_ab ^ 2))
        QuadraticCovers.Dual.C (1 / 16 : F) * (m2 * d10_e - m1 * d20_e + m0 * d21_e)
      QuadraticCovers.Dual.C (-(19708 / 1257375 : F)) * (5 * m_sc 0 - 9 * m_sc 1) +
        QuadraticCovers.Dual.C (1472 / 1257375 : F) * (5 * m_sc 1 - 9 * m_sc 2) -
        QuadraticCovers.Dual.C (16 / 729 : F) * (5 * m_sc 3 - 9 * m_sc 5) +
        QuadraticCovers.Dual.C (188 / 2025 : F) * (5 * m_sc 4 - 9 * m_sc 6) =
      QuadraticCovers.Dual.C (d_ab ^ 3) * ⟨(8248380 / 51331077 : F) * (5 * S - 3 * Q) * S ^ 3 * A ^ 2,
        -(2 / 51331077 : F) * B * S ^ 2 * A ^ 2 * Q_quad⟩ :=
  fun {_} _ _ S Q T => SymmetricSexticResidual.LocalResidueU0.br2_0_A0U_scaled_poly S Q T
