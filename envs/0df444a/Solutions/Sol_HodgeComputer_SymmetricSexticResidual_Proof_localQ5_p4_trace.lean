-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_p4_trace
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:51:58.52696+00:00
-- url     : https://prove2.me/submissions/ac26e4cc-96c0-4041-8783-4fc01d30043c

import Definitions.Def_HodgeComputerSSR_Q5ACDefs
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_ac_bridge
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_geom_bridge

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

private abbrev evalACache_AC_bridge := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_ac_bridge.ac_bridge
private abbrev evalGeomT_AC_bridge :=
  let h := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_geom_bridge.gt_props
  And.intro h.1 (And.intro h.2.2.1 (And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1
    (And.intro h.2.2.2.2.2.1 (And.intro h.2.2.2.2.2.2.1 (And.intro h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.1))))))

section NumMLead3Proofs
variable {R : Type*} [Field R] [CharZero R]
lemma numM_isPoly3_core (mi : Fin 10) (S Q T a1 b1 b0 A2 A2_1 A2_0 A1 A1_0 A0 B2 B2_1 B2_0 B1 B1_0 B0 : R) :
    let d21' : R → R := fun z => (A2 * z ^ 2 + A2_1 * z + A2_0) * (B1 * z + B1_0) - (A1 * z + A1_0) * (B2 * z ^ 2 + B2_1 * z + B2_0)
    let d20' : R → R := fun z => (A2 * z ^ 2 + A2_1 * z + A2_0) * B0 - A0 * (B2 * z ^ 2 + B2_1 * z + B2_0)
    let d10' : R → R := fun z => (A1 * z + A1_0) * B0 - A0 * (B1 * z + B1_0)
    let D21 : R → R := d21'
    let D20 : R → R := fun z => d20' z - T * d21' z
    let D10 : R → R := fun z => d10' z - 2 * T * d20' z + T ^ 2 * d21' z
    let d21_0 := A2 * B1 - A1 * B2
    let d20_0 := A2 * B0 - A0 * B2
    let d10_0 := A1 * B0 - A0 * B1
    ∃ c2 c1 c0 : R, ∀ z : R,
      (1 / 16 : R) * (match mi with
        | 0 => (a1 * z) ^ 2 * D10 z - 2 * (a1 * z) * (S - a1 * z * T) * D20 z + (S - a1 * z * T) ^ 2 * D21 z
        | 1 => (a1 * z) * (b1 * z + b0) * D10 z - ((a1 * z) * (Q - (b1 * z + b0) * T) + (b1 * z + b0) * (S - a1 * z * T)) * D20 z +
                 (S - a1 * z * T) * (Q - (b1 * z + b0) * T) * D21 z
        | 2 => (b1 * z + b0) ^ 2 * D10 z - 2 * (b1 * z + b0) * (Q - (b1 * z + b0) * T) * D20 z + (Q - (b1 * z + b0) * T) ^ 2 * D21 z
        | 3 => (a1 * z) * D10 z - (S - a1 * z * T) * D20 z
        | 4 => -(a1 * z) * D20 z + (S - a1 * z * T) * D21 z
        | 5 => (b1 * z + b0) * D10 z - (Q - (b1 * z + b0) * T) * D20 z
        | 6 => -(b1 * z + b0) * D20 z + (Q - (b1 * z + b0) * T) * D21 z
        | 7 => D10 z
        | 8 => -D20 z
        | 9 => D21 z) =
      ((1 / 16 : R) * match mi with
        | 0 => a1 ^ 2 * d10_0 - 2 * a1 * S * d20_0 + S ^ 2 * d21_0
        | 1 => a1 * b1 * d10_0 - (a1 * Q + b1 * S) * d20_0 + S * Q * d21_0
        | 2 => b1 ^ 2 * d10_0 - 2 * b1 * Q * d20_0 + Q ^ 2 * d21_0
        | 3 => T * (S * d21_0 - a1 * d20_0)
        | 4 => S * d21_0 - a1 * d20_0
        | 5 => T * (Q * d21_0 - b1 * d20_0)
        | 6 => Q * d21_0 - b1 * d20_0
        | 7 => T ^ 2 * d21_0
        | 8 => T * d21_0
        | 9 => d21_0) * z ^ 3 + c2 * z ^ 2 + c1 * z + c0 := by
  intro d21' d20' d10' D21 D20 D10 d21_0 d20_0 d10_0
  have hlin (p2 p1 p0 q1 q0 r0 : R) :
      ∃ c2 c1 c0 : R, ∀ z : R,
        (1 / 16 : R) * ((p2 * z ^ 2 + p1 * z + p0) * d10' z - (q1 * z + q0) * d20' z + r0 * d21' z) =
        (1 / 16 : R) * (p2 * d10_0 - q1 * d20_0 + r0 * d21_0) * z ^ 3 + c2 * z ^ 2 + c1 * z + c0 := by
    refine ⟨(1 / 16) * (p2 * (A1_0 * B0 - A0 * B1_0) + p1 * d10_0 - q1 * (A2_1 * B0 - A0 * B2_1) -
              q0 * d20_0 + r0 * (A2 * B1_0 + A2_1 * B1 - A1 * B2_1 - A1_0 * B2)),
            (1 / 16) * (p1 * (A1_0 * B0 - A0 * B1_0) + p0 * d10_0 - q1 * (A2_0 * B0 - A0 * B2_0) -
              q0 * (A2_1 * B0 - A0 * B2_1) + r0 * (A2_1 * B1_0 + A2_0 * B1 - A1 * B2_0 - A1_0 * B2_1)),
            (1 / 16) * (p0 * (A1_0 * B0 - A0 * B1_0) - q0 * (A2_0 * B0 - A0 * B2_0) + r0 * (A2_0 * B1_0 - A1_0 * B2_0)),
            fun z => by dsimp only [d21', d20', d10', d21_0, d20_0, d10_0]; ring⟩
  fin_cases mi
  · obtain ⟨c2, c1, c0, h⟩ := hlin (a1 ^ 2) 0 0 (2 * a1 * S) 0 (S ^ 2)
    refine ⟨c2, c1, c0, fun z => ?_⟩; have hz := h z; dsimp only [D21, D20, D10] at hz ⊢
    generalize d21' z = u1 at hz ⊢; generalize d20' z = u2 at hz ⊢; generalize d10' z = u3 at hz ⊢
    generalize d21_0 = v1 at hz ⊢; generalize d20_0 = v2 at hz ⊢; generalize d10_0 = v3 at hz ⊢; linear_combination hz
  · obtain ⟨c2, c1, c0, h⟩ := hlin (a1 * b1) (a1 * b0) 0 (a1 * Q + b1 * S) (b0 * S) (S * Q)
    refine ⟨c2, c1, c0, fun z => ?_⟩; have hz := h z; dsimp only [D21, D20, D10] at hz ⊢
    generalize d21' z = u1 at hz ⊢; generalize d20' z = u2 at hz ⊢; generalize d10' z = u3 at hz ⊢
    generalize d21_0 = v1 at hz ⊢; generalize d20_0 = v2 at hz ⊢; generalize d10_0 = v3 at hz ⊢; linear_combination hz
  · obtain ⟨c2, c1, c0, h⟩ := hlin (b1 ^ 2) (2 * b1 * b0) (b0 ^ 2) (2 * b1 * Q) (2 * b0 * Q) (Q ^ 2)
    refine ⟨c2, c1, c0, fun z => ?_⟩; have hz := h z; dsimp only [D21, D20, D10] at hz ⊢
    generalize d21' z = u1 at hz ⊢; generalize d20' z = u2 at hz ⊢; generalize d10' z = u3 at hz ⊢
    generalize d21_0 = v1 at hz ⊢; generalize d20_0 = v2 at hz ⊢; generalize d10_0 = v3 at hz ⊢; linear_combination hz
  · obtain ⟨c2, c1, c0, h⟩ := hlin 0 a1 0 (a1 * T) S (S * T)
    refine ⟨c2, c1, c0, fun z => ?_⟩; have hz := h z; dsimp only [D21, D20, D10] at hz ⊢
    generalize d21' z = u1 at hz ⊢; generalize d20' z = u2 at hz ⊢; generalize d10' z = u3 at hz ⊢
    generalize d21_0 = v1 at hz ⊢; generalize d20_0 = v2 at hz ⊢; generalize d10_0 = v3 at hz ⊢; linear_combination hz
  · obtain ⟨c2, c1, c0, h⟩ := hlin 0 0 0 a1 0 S
    refine ⟨c2, c1, c0, fun z => ?_⟩; have hz := h z; dsimp only [D21, D20, D10] at hz ⊢
    generalize d21' z = u1 at hz ⊢; generalize d20' z = u2 at hz ⊢; generalize d10' z = u3 at hz ⊢
    generalize d21_0 = v1 at hz ⊢; generalize d20_0 = v2 at hz ⊢; generalize d10_0 = v3 at hz ⊢; linear_combination hz
  · obtain ⟨c2, c1, c0, h⟩ := hlin 0 b1 b0 (b1 * T) (b0 * T + Q) (Q * T)
    refine ⟨c2, c1, c0, fun z => ?_⟩; have hz := h z; dsimp only [D21, D20, D10] at hz ⊢
    generalize d21' z = u1 at hz ⊢; generalize d20' z = u2 at hz ⊢; generalize d10' z = u3 at hz ⊢
    generalize d21_0 = v1 at hz ⊢; generalize d20_0 = v2 at hz ⊢; generalize d10_0 = v3 at hz ⊢; linear_combination hz
  · obtain ⟨c2, c1, c0, h⟩ := hlin 0 0 0 b1 b0 Q
    refine ⟨c2, c1, c0, fun z => ?_⟩; have hz := h z; dsimp only [D21, D20, D10] at hz ⊢
    generalize d21' z = u1 at hz ⊢; generalize d20' z = u2 at hz ⊢; generalize d10' z = u3 at hz ⊢
    generalize d21_0 = v1 at hz ⊢; generalize d20_0 = v2 at hz ⊢; generalize d10_0 = v3 at hz ⊢; linear_combination hz
  · obtain ⟨c2, c1, c0, h⟩ := hlin 0 0 1 0 (2 * T) (T ^ 2)
    refine ⟨c2, c1, c0, fun z => ?_⟩; have hz := h z; dsimp only [D21, D20, D10] at hz ⊢
    generalize d21' z = u1 at hz ⊢; generalize d20' z = u2 at hz ⊢; generalize d10' z = u3 at hz ⊢
    generalize d21_0 = v1 at hz ⊢; generalize d20_0 = v2 at hz ⊢; generalize d10_0 = v3 at hz ⊢; linear_combination hz
  · obtain ⟨c2, c1, c0, h⟩ := hlin 0 0 0 0 1 T
    refine ⟨c2, c1, c0, fun z => ?_⟩; have hz := h z; dsimp only [D21, D20, D10] at hz ⊢
    generalize d21' z = u1 at hz ⊢; generalize d20' z = u2 at hz ⊢; generalize d10' z = u3 at hz ⊢
    generalize d21_0 = v1 at hz ⊢; generalize d20_0 = v2 at hz ⊢; generalize d10_0 = v3 at hz ⊢; linear_combination hz
  · obtain ⟨c2, c1, c0, h⟩ := hlin 0 0 0 0 0 1
    refine ⟨c2, c1, c0, fun z => ?_⟩; have hz := h z; dsimp only [D21, D20, D10] at hz ⊢
    generalize d21' z = u1 at hz ⊢; generalize d20' z = u2 at hz ⊢; generalize d10' z = u3 at hz ⊢
    generalize d21_0 = v1 at hz ⊢; generalize d20_0 = v2 at hz ⊢; generalize d10_0 = v3 at hz ⊢; linear_combination hz

lemma numM_isPoly3 (mi : Fin 10) (S Q T a1 b1 b0 U V : R) :
    ∃ c2 c1 c0 : R, ∀ z : R,
      numM mi (a1 * z) (b1 * z + b0) (S - (a1 * z) * T) (Q - (b1 * z + b0) * T) U V =
        numM_lead3 mi S Q T a1 b1 U V * z ^ 3 + c2 * z ^ 2 + c1 * z + c0 := by
  set A2 := q1_a2 a1 b1 U V with hA2; set A2_1 := q1_a1 a1 b1 0 b0 U V; set A2_0 := q1_a0 0 b0 U V
  set A1 := q1_a1 a1 b1 S Q U V with hA1; set A1_0 := q1_a1 0 b0 S Q U V; set A0 := q1_a0 S Q U V with hA0
  set B2 := q2_b2 a1 b1 U V with hB2
  set B2_1 := dH_dQ a1 (b1 + b0) 0 U V - dH_dQ a1 b1 0 U V - dH_dQ 0 b0 0 U V
  set B2_0 := q2_b2 0 b0 U V
  set B1 := q2_b1 a1 b1 S Q U V with hB1; set B1_0 := q2_b1 0 b0 S Q U V; set B0 := q2_b0 S Q U V with hB0
  have ha2 (z : R) : q1_a2 (a1 * z) (b1 * z + b0) U V = A2 * z ^ 2 + A2_1 * z + A2_0 := by
    simp only [A2, A2_1, A2_0, q1_a2, q1_a1, q1_a0, dH_dS]; ring
  have ha1 (z : R) : q1_a1 (a1 * z) (b1 * z + b0) (S - a1 * z * T) (Q - (b1 * z + b0) * T) U V =
      (A1 * z + A1_0) - 2 * T * (A2 * z ^ 2 + A2_1 * z + A2_0) := by
    simp only [A2, A2_1, A2_0, A1, A1_0, q1_a2, q1_a1, q1_a0, dH_dS]; ring
  have ha0 (z : R) : q1_a0 (S - a1 * z * T) (Q - (b1 * z + b0) * T) U V =
      A0 - T * (A1 * z + A1_0) + T ^ 2 * (A2 * z ^ 2 + A2_1 * z + A2_0) := by
    simp only [A2, A2_1, A2_0, A1, A1_0, A0, q1_a2, q1_a1, q1_a0, dH_dS]; ring
  have hb2 (z : R) : q2_b2 (a1 * z) (b1 * z + b0) U V = B2 * z ^ 2 + B2_1 * z + B2_0 := by
    simp only [B2, B2_1, B2_0, q2_b2, dH_dQ]; ring
  have hb1 (z : R) : q2_b1 (a1 * z) (b1 * z + b0) (S - a1 * z * T) (Q - (b1 * z + b0) * T) U V =
      (B1 * z + B1_0) - 2 * T * (B2 * z ^ 2 + B2_1 * z + B2_0) := by
    simp only [B2, B2_1, B2_0, B1, B1_0, q2_b2, q2_b1, dH_dQ]; ring
  have hb0 (z : R) : q2_b0 (S - a1 * z * T) (Q - (b1 * z + b0) * T) U V =
      B0 - T * (B1 * z + B1_0) + T ^ 2 * (B2 * z ^ 2 + B2_1 * z + B2_0) := by
    simp only [B2, B2_1, B2_0, B1, B1_0, B0, q2_b2, q2_b1, q2_b0, dH_dQ]; ring
  have hshift (z : R) :
      let a2 := q1_a2 (a1 * z) (b1 * z + b0) U V
      let a1_ := q1_a1 (a1 * z) (b1 * z + b0) (S - a1 * z * T) (Q - (b1 * z + b0) * T) U V
      let a0_ := q1_a0 (S - a1 * z * T) (Q - (b1 * z + b0) * T) U V
      let b2 := q2_b2 (a1 * z) (b1 * z + b0) U V
      let b1_ := q2_b1 (a1 * z) (b1 * z + b0) (S - a1 * z * T) (Q - (b1 * z + b0) * T) U V
      let b0_ := q2_b0 (S - a1 * z * T) (Q - (b1 * z + b0) * T) U V
      (a2 * b1_ - a1_ * b2 = (A2 * z ^ 2 + A2_1 * z + A2_0) * (B1 * z + B1_0) - (A1 * z + A1_0) * (B2 * z ^ 2 + B2_1 * z + B2_0)) ∧
      (a2 * b0_ - a0_ * b2 = ((A2 * z ^ 2 + A2_1 * z + A2_0) * B0 - A0 * (B2 * z ^ 2 + B2_1 * z + B2_0)) -
        T * ((A2 * z ^ 2 + A2_1 * z + A2_0) * (B1 * z + B1_0) - (A1 * z + A1_0) * (B2 * z ^ 2 + B2_1 * z + B2_0))) ∧
      (a1_ * b0_ - a0_ * b1_ = ((A1 * z + A1_0) * B0 - A0 * (B1 * z + B1_0)) -
        2 * T * ((A2 * z ^ 2 + A2_1 * z + A2_0) * B0 - A0 * (B2 * z ^ 2 + B2_1 * z + B2_0)) +
        T ^ 2 * ((A2 * z ^ 2 + A2_1 * z + A2_0) * (B1 * z + B1_0) - (A1 * z + A1_0) * (B2 * z ^ 2 + B2_1 * z + B2_0))) := by
    simp only [ha2, ha1, ha0, hb2, hb1, hb0]
    generalize (A2 * z ^ 2 + A2_1 * z + A2_0) = pA2; generalize (A1 * z + A1_0) = pA1; generalize A0 = pA0
    generalize (B2 * z ^ 2 + B2_1 * z + B2_0) = pB2; generalize (B1 * z + B1_0) = pB1; generalize B0 = pB0
    exact ⟨by ring, by ring, by ring⟩
  obtain ⟨c2, c1, c0, h⟩ := numM_isPoly3_core mi S Q T a1 b1 b0 A2 A2_1 A2_0 A1 A1_0 A0 B2 B2_1 B2_0 B1 B1_0 B0
  refine ⟨c2, c1, c0, fun z => ?_⟩
  have hz := h z
  have hs := hshift z
  fin_cases mi <;> (
    simp only [numM, numM_lead3, hs.1, hs.2.1, hs.2.2, ← hA2, ← hA1, ← hA0, ← hB2, ← hB1, ← hB0,
      zero_mul, one_mul, sub_zero, add_zero, zero_sub, zero_add, neg_mul] at hz ⊢
    exact hz)

lemma numM_lead3_scale (mi : Fin 10) (S Q T a1 b1 U V lam : R) :
    numM_lead3 mi S Q T (lam * a1) (lam * b1) U V =
      lam ^ 3 * V ^ 2 * numM_lead3 mi S Q T a1 b1 U 1 := by
  have ha2 : q1_a2 (lam * a1) (lam * b1) U V = lam ^ 2 * V * q1_a2 a1 b1 U 1 := by
    simp only [q1_a2, dH_dS]; ring
  have ha1 : q1_a1 (lam * a1) (lam * b1) S Q U V = lam * V * q1_a1 a1 b1 S Q U 1 := by
    simp only [q1_a1, dH_dS]; ring
  have ha0 : q1_a0 S Q U V = V * q1_a0 S Q U 1 := by
    simp only [q1_a0, dH_dS]; ring
  have hb2 : q2_b2 (lam * a1) (lam * b1) U V = lam ^ 2 * V * q2_b2 a1 b1 U 1 := by
    simp only [q2_b2, dH_dQ]; ring
  have hb1 : q2_b1 (lam * a1) (lam * b1) S Q U V = lam * V * q2_b1 a1 b1 S Q U 1 := by
    simp only [q2_b1, dH_dQ]; ring
  have hb0 : q2_b0 S Q U V = V * q2_b0 S Q U 1 := by
    simp only [q2_b0, dH_dQ]; ring
  simp only [numM_lead3, ha2, ha1, ha0, hb2, hb1, hb0]
  generalize q1_a2 a1 b1 U 1 = x2; generalize q1_a1 a1 b1 S Q U 1 = x1; generalize q1_a0 S Q U 1 = x0
  generalize q2_b2 a1 b1 U 1 = y2; generalize q2_b1 a1 b1 S Q U 1 = y1; generalize q2_b0 S Q U 1 = y0
  fin_cases mi <;> ring

end NumMLead3Proofs

lemma R13_int_p_eval_zero : R13_int_p.eval 0 = 0 := by
  have hAY2_0 : AY2_p.eval 0 = 0 := by
    have h := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_ac_bridge.AY2_e0
    simp [AY2_p, h.1, h.2]
  have hAX2_0 : AX2_p.eval 0 = 0 := by
    have h := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_ac_bridge.AX2_e0
    simp [AX2_p, h.1, h.2.1, h.2.2]
  have hq0 := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_geom_bridge.gt_props.2.2.2.2.2.2.2.2.2
  simp only [R13_int_p, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, hAY2_0, hAX2_0, hq0.1, hq0.2.1, hq0.2.2.1, hq0.2.2.2]
  ring

lemma R13_int_p_eq_X_mul_R12 : R13_int_p = Polynomial.X * R12_int_p := by
  have h := Polynomial.X_mul_divX_add R13_int_p
  have hc0 : R13_int_p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]; exact R13_int_p_eval_zero
  rw [hc0, map_zero, add_zero] at h
  exact h.symm

-- Step 1 of `trace_AC_eta_AC_main_eq`: extract `p4_AC = (interp4 P18_z_AC).1` via `numM_isPoly3`, `numM_lead3_scale`, `interp4_eq`!
lemma p4_AC_eq :
    let S := ιC_K5 S_K; let Q := ιC_K5 Q_K; let T := ιC_K5 T_K
    let x := ιC_K5 x_K; let y := ιC_K5 y_K
    let ca := polyC k5Params.ca_h; let cb := polyC k5Params.cb_h
    let m := fun mi : Fin 10 => numM_lead3 mi S Q T cb (-ca) U_C 1
    let QX_dot := QX_num S Q T x y U_C V_C 0 * cb - QX_num S Q T x y U_C V_C 1 * ca
    let QY_dot := QY_num S Q T x y U_C V_C 0 * cb - QY_num S Q T x y U_C V_C 1 * ca
    let cA1_dot := (H0_of S Q T * dA1_fn 0 S Q U_C V_C - A1_of S Q U_C V_C * dH0_fn 0 S Q T) * cb -
      (H0_of S Q T * dA1_fn 1 S Q U_C V_C - A1_of S Q U_C V_C * dH0_fn 1 S Q T) * ca
    let q1_dot := H0_of S Q T * A1_of S Q U_C V_C * (QY_dot / v_of V_C) +
      H0_of S Q T * B1_of T U_C V_C * (QX_dot / u_of U_C) +
      (cA1_dot / v_of V_C) * EB_of S Q T x y U_C V_C
    let A0U_l : A_C := -(19708 / 1257375 : A_C) * (5 * m 0 - 9 * m 1) + (1472 / 1257375 : A_C) * (5 * m 1 - 9 * m 2) -
        (16 / 729 : A_C) * (5 * m 3 - 9 * m 5) + (188 / 2025 : A_C) * (5 * m 4 - 9 * m 6)
    let A0V_l : A_C := -(892 / 3645 : A_C) * (5 * m 3 - 9 * m 4) + (40 / 81 : A_C) * (5 * m 5 - 9 * m 6) -
        (112 / 2395 : A_C) * (5 * m 7 - 9 * m 8) + (392 / 11975 : A_C) * (5 * m 8 - 9 * m 9)
    let AY_l : A_C := -(100 / 243 : A_C) * (25 * m 3 - 45 * m 4 - 45 * m 5 + 81 * m 6) +
        V_C * (-(907876 / 33949125 : A_C) * (5 * m 0 - 9 * m 1) + (2258324 / 33949125 : A_C) * (5 * m 1 - 9 * m 2) +
          (8 / 243 : A_C) * (5 * m 3 - 9 * m 5) - (64 / 675 : A_C) * (5 * m 4 - 9 * m 6)) +
        U_C * V_C * (-(123236 / 24249375 : A_C) * (m 0 + (2790 / 77 : A_C) * m 6 + 28 * m 8 - (5904 / 77 : A_C) * m 9) +
          (492944 / 33949125 : A_C) * (m 1 + (927 / 77 : A_C) * m 6 + (49 / 5 : A_C) * m 8 - (21159 / 770 : A_C) * m 9))
    let AX_l : A_C := U_C * (-(8 / 405 : A_C) * (5 * m 3 - 9 * m 4) - (476 / 7185 : A_C) * (5 * m 7 - 9 * m 8) +
        (6916 / 35925 : A_C) * (5 * m 8 - 9 * m 9))
    p4_AC = (V_C ^ 2 / (W_C * cb) ^ 4) *
      ((A0U_l / U_C + A0V_l / V_C) * q1_dot + (AY_l * (QY_dot / v_of V_C) + AX_l * (QX_dot / u_of U_C)) * H0_of S Q T ^ 2) := by
  intro S Q T x y ca cb m QX_dot QY_dot cA1_dot q1_dot A0U_l A0V_l AY_l AX_l
  have hW_ne := W_C_ne_zero; have hU_ne := U_C_ne_zero; have hV_ne := V_C_ne_zero
  have hu_ne := u_of_U_C_ne_zero; have hv_ne := v_of_V_C_ne_zero
  have hcb_ne : cb ≠ 0 := polyC_ne_zero cb_h_K5_ne_zero
  set a1 : A_C := 1 / W_C
  set b1 : A_C := -ca / (W_C * cb)
  set b0 : A_C := -pairC k5Params.c0W / (W_C * cb)
  have hab_z (z : A_C) :
      z / W_C = a1 * z ∧ -(ca * z + pairC k5Params.c0W) / (W_C * cb) = b1 * z + b0 := by
    dsimp only [a1, b1, b0]; constructor
    · field_simp [hW_ne]
    · field_simp [hW_ne, hcb_ne]; ring
  have hnum_poly (mi : Fin 10) : ∃ c2 c1 c0 : A_C, ∀ z : A_C,
      numM mi (a1 * z) (b1 * z + b0) (S - (a1 * z) * T) (Q - (b1 * z + b0) * T) U_C V_C =
        (V_C ^ 2 / (W_C * cb) ^ 3 * m mi) * z ^ 3 + c2 * z ^ 2 + c1 * z + c0 := by
    obtain ⟨c2, c1, c0, h⟩ := numM_isPoly3 mi S Q T a1 b1 b0 U_C V_C
    have hsc : numM_lead3 mi S Q T a1 b1 U_C V_C = V_C ^ 2 / (W_C * cb) ^ 3 * m mi := by
      have h1 : a1 = (1 / (W_C * cb)) * cb := by dsimp only [a1]; field_simp [hW_ne, hcb_ne]
      have h2 : b1 = (1 / (W_C * cb)) * (-ca) := by dsimp only [b1]; field_simp [hW_ne, hcb_ne]
      rw [h1, h2, numM_lead3_scale]; dsimp only [m]; field_simp [hW_ne, hcb_ne]
    exact ⟨c2, c1, c0, fun z => by rw [h z, hsc]⟩
  choose c2 c1 c0 hnm using hnum_poly
  let fA0U (v : Fin 10 → A_C) : A_C :=
    -(19708 / 1257375 : A_C) * (5 * v 0 - 9 * v 1) + (1472 / 1257375 : A_C) * (5 * v 1 - 9 * v 2) -
    (16 / 729 : A_C) * (5 * v 3 - 9 * v 5) + (188 / 2025 : A_C) * (5 * v 4 - 9 * v 6)
  let fA0V (v : Fin 10 → A_C) : A_C :=
    -(892 / 3645 : A_C) * (5 * v 3 - 9 * v 4) + (40 / 81 : A_C) * (5 * v 5 - 9 * v 6) -
    (112 / 2395 : A_C) * (5 * v 7 - 9 * v 8) + (392 / 11975 : A_C) * (5 * v 8 - 9 * v 9)
  let fAY (v : Fin 10 → A_C) : A_C :=
    -(100 / 243 : A_C) * (25 * v 3 - 45 * v 4 - 45 * v 5 + 81 * v 6) +
    V_C * (-(907876 / 33949125 : A_C) * (5 * v 0 - 9 * v 1) + (2258324 / 33949125 : A_C) * (5 * v 1 - 9 * v 2) +
      (8 / 243 : A_C) * (5 * v 3 - 9 * v 5) - (64 / 675 : A_C) * (5 * v 4 - 9 * v 6)) +
    U_C * V_C * (-(123236 / 24249375 : A_C) * (v 0 + (2790 / 77 : A_C) * v 6 + 28 * v 8 - (5904 / 77 : A_C) * v 9) +
      (492944 / 33949125 : A_C) * (v 1 + (927 / 77 : A_C) * v 6 + (49 / 5 : A_C) * v 8 - (21159 / 770 : A_C) * v 9))
  let fAX (v : Fin 10 → A_C) : A_C :=
    U_C * (-(8 / 405 : A_C) * (5 * v 3 - 9 * v 4) - (476 / 7185 : A_C) * (5 * v 7 - 9 * v 8) +
      (6916 / 35925 : A_C) * (5 * v 8 - 9 * v 9))
  have hM0 : ∃ d2 d1 d0 : A_C, ∀ z : A_C,
      A_0U (a1 * z) (b1 * z + b0) (S - a1 * z * T) (Q - (b1 * z + b0) * T) U_C V_C / U_C +
      A_0V (a1 * z) (b1 * z + b0) (S - a1 * z * T) (Q - (b1 * z + b0) * T) U_C V_C / V_C =
      (V_C ^ 2 / (W_C * cb) ^ 3 * (A0U_l / U_C + A0V_l / V_C)) * z ^ 3 + d2 * z ^ 2 + d1 * z + d0 := by
    refine ⟨fA0U c2 / U_C + fA0V c2 / V_C, fA0U c1 / U_C + fA0V c1 / V_C, fA0U c0 / U_C + fA0V c0 / V_C, fun z => ?_⟩
    simp only [A_0U, A_0V, hnm, A0U_l, A0V_l, fA0U, fA0V]; ring
  have hMY : ∃ d2 d1 d0 : A_C, ∀ z : A_C,
      A_Y (a1 * z) (b1 * z + b0) (S - a1 * z * T) (Q - (b1 * z + b0) * T) U_C V_C =
      (V_C ^ 2 / (W_C * cb) ^ 3 * AY_l) * z ^ 3 + d2 * z ^ 2 + d1 * z + d0 := by
    refine ⟨fAY c2, fAY c1, fAY c0, fun z => ?_⟩
    simp only [A_Y, hnm, AY_l, fAY]; ring
  have hMX : ∃ d2 d1 d0 : A_C, ∀ z : A_C,
      A_X (a1 * z) (b1 * z + b0) (S - a1 * z * T) (Q - (b1 * z + b0) * T) U_C V_C =
      (V_C ^ 2 / (W_C * cb) ^ 3 * AX_l) * z ^ 3 + d2 * z ^ 2 + d1 * z + d0 := by
    refine ⟨fAX c2, fAX c1, fAX c0, fun z => ?_⟩
    simp only [A_X, hnm, AX_l, fAX]; ring
  obtain ⟨m2, m1, m0, hM0⟩ := hM0
  obtain ⟨y2, y1, y0, hMY⟩ := hMY
  obtain ⟨x2, x1, x0, hMX⟩ := hMX
  have hqY_z (z : A_C) : dot_ab (QY_num S Q T x y U_C V_C) (a1 * z) (b1 * z + b0) / v_of V_C =
      (QY_dot / (W_C * cb * v_of V_C)) * z + (QY_num S Q T x y U_C V_C 1 * b0 + QY_num S Q T x y U_C V_C 2) / v_of V_C := by
    simp only [dot_ab, QY_dot, a1, b1]; field_simp [hW_ne, hcb_ne, hv_ne]; ring
  have hqX_z (z : A_C) : dot_ab (QX_num S Q T x y U_C V_C) (a1 * z) (b1 * z + b0) / u_of U_C =
      (QX_dot / (W_C * cb * u_of U_C)) * z + (QX_num S Q T x y U_C V_C 1 * b0 + QX_num S Q T x y U_C V_C 2) / u_of U_C := by
    simp only [dot_ab, QX_dot, a1, b1]; field_simp [hW_ne, hcb_ne, hu_ne]; ring
  have hcA1_z (z : A_C) : cA1_of S Q T (a1 * z) (b1 * z + b0) U_C V_C / v_of V_C =
      (cA1_dot / (W_C * cb * v_of V_C)) * z +
      ((H0_of S Q T * dA1_fn 1 S Q U_C V_C - A1_of S Q U_C V_C * dH0_fn 1 S Q T) * b0 +
        (H0_of S Q T * dA1_fn 2 S Q U_C V_C - A1_of S Q U_C V_C * dH0_fn 2 S Q T)) / v_of V_C := by
    simp only [cA1_of, cA1_dot, a1, b1]; field_simp [hW_ne, hcb_ne, hv_ne]; ring
  set qY_0z := (QY_num S Q T x y U_C V_C 1 * b0 + QY_num S Q T x y U_C V_C 2) / v_of V_C
  set qX_0z := (QX_num S Q T x y U_C V_C 1 * b0 + QX_num S Q T x y U_C V_C 2) / u_of U_C
  set q1_0z := H0_of S Q T * A1_of S Q U_C V_C * qY_0z + H0_of S Q T * B1_of T U_C V_C * qX_0z +
    ((H0_of S Q T * dA1_fn 1 S Q U_C V_C - A1_of S Q U_C V_C * dH0_fn 1 S Q T) * b0 +
      (H0_of S Q T * dA1_fn 2 S Q U_C V_C - A1_of S Q U_C V_C * dH0_fn 2 S Q T)) / v_of V_C * EB_of S Q T x y U_C V_C
  have hP18_poly : ∀ z : A_C, P18_z_AC z =
      ((V_C ^ 2 / (W_C * cb) ^ 4) * ((A0U_l / U_C + A0V_l / V_C) * q1_dot +
        (AY_l * (QY_dot / v_of V_C) + AX_l * (QX_dot / u_of U_C)) * H0_of S Q T ^ 2)) * z ^ 4 +
      ((V_C ^ 2 / (W_C * cb) ^ 3 * (A0U_l / U_C + A0V_l / V_C)) * q1_0z + m2 * (q1_dot / (W_C * cb)) +
        ((V_C ^ 2 / (W_C * cb) ^ 3 * AY_l) * qY_0z + y2 * (QY_dot / (W_C * cb * v_of V_C)) +
         (V_C ^ 2 / (W_C * cb) ^ 3 * AX_l) * qX_0z + x2 * (QX_dot / (W_C * cb * u_of U_C))) * H0_of S Q T ^ 2) * z ^ 3 +
      (m2 * q1_0z + m1 * (q1_dot / (W_C * cb)) +
        (y2 * qY_0z + y1 * (QY_dot / (W_C * cb * v_of V_C)) + x2 * qX_0z + x1 * (QX_dot / (W_C * cb * u_of U_C))) * H0_of S Q T ^ 2) * z ^ 2 +
      (m1 * q1_0z + m0 * (q1_dot / (W_C * cb)) +
        (y1 * qY_0z + y0 * (QY_dot / (W_C * cb * v_of V_C)) + x1 * qX_0z + x0 * (QX_dot / (W_C * cb * u_of U_C))) * H0_of S Q T ^ 2) * z +
      (m0 * q1_0z + (y0 * qY_0z + x0 * qX_0z) * H0_of S Q T ^ 2) := fun z => by
    dsimp only [P18_z_AC, P18_of]
    rw [(hab_z z).1, (hab_z z).2, hM0 z, hMY z, hMX z, hqY_z z, hqX_z z, hcA1_z z]
    dsimp only [q1_dot, q1_0z]
    field_simp [hW_ne, hcb_ne, hU_ne, hV_ne, hu_ne, hv_ne]; ring
  have hint := interp4_eq hP18_poly
  simp only [p4_AC, hint]

-- Exact `trace_AC` formula for `eta_AC_main` via `p4_AC_eq`, 1-line `E0` reduction, and `trace_AC_euler`!
lemma trace_AC_eta_AC_main_eq :
    Algebra.trace (RatFunc K5) A_C eta_AC_main =
      toRat R12_int_p / (RatFunc.C (81 * k5Params.Cv0 * (M_R_int : K5)) * toRat (k5Params.Q7_z * k5Params.Q5_z)) := by
  set S := ιC_K5 S_K; set Q := ιC_K5 Q_K; set T := ιC_K5 T_K
  set x := ιC_K5 x_K; set y := ιC_K5 y_K
  set ca := polyC k5Params.ca_h; set cb := polyC k5Params.cb_h
  have hU_ne := U_C_ne_zero; have hV_ne := V_C_ne_zero
  have hcb_ne : cb ≠ 0 := polyC_ne_zero cb_h_K5_ne_zero
  have hCv0_ne : ιC_K5 k5Params.Cv0 ≠ 0 := (map_ne_zero_iff _ ιC_K5.injective).mpr k5Params_Cv0_ne
  have hMR_ne : (M_R_int : A_C) ≠ 0 := by
    have hZ : M_R_int ≠ 0 := by unfold M_R_int M_A_int L_all_A M_mid_int; decide
    exact Int.cast_ne_zero.mpr hZ
  set m := fun mi : Fin 10 => numM_lead3 mi S Q T cb (-ca) U_C 1
  set QX_dot := QX_num S Q T x y U_C V_C 0 * cb - QX_num S Q T x y U_C V_C 1 * ca
  set QY_dot := QY_num S Q T x y U_C V_C 0 * cb - QY_num S Q T x y U_C V_C 1 * ca
  set cA1_dot := (H0_of S Q T * dA1_fn 0 S Q U_C V_C - A1_of S Q U_C V_C * dH0_fn 0 S Q T) * cb -
    (H0_of S Q T * dA1_fn 1 S Q U_C V_C - A1_of S Q U_C V_C * dH0_fn 1 S Q T) * ca
  set q1_dot := H0_of S Q T * A1_of S Q U_C V_C * (QY_dot / v_of V_C) +
    H0_of S Q T * B1_of T U_C V_C * (QX_dot / u_of U_C) +
    (cA1_dot / v_of V_C) * EB_of S Q T x y U_C V_C
  set A0U_l : A_C := -(19708 / 1257375 : A_C) * (5 * m 0 - 9 * m 1) + (1472 / 1257375 : A_C) * (5 * m 1 - 9 * m 2) -
      (16 / 729 : A_C) * (5 * m 3 - 9 * m 5) + (188 / 2025 : A_C) * (5 * m 4 - 9 * m 6)
  set A0V_l : A_C := -(892 / 3645 : A_C) * (5 * m 3 - 9 * m 4) + (40 / 81 : A_C) * (5 * m 5 - 9 * m 6) -
      (112 / 2395 : A_C) * (5 * m 7 - 9 * m 8) + (392 / 11975 : A_C) * (5 * m 8 - 9 * m 9)
  set AY_l : A_C := -(100 / 243 : A_C) * (25 * m 3 - 45 * m 4 - 45 * m 5 + 81 * m 6) +
      V_C * (-(907876 / 33949125 : A_C) * (5 * m 0 - 9 * m 1) + (2258324 / 33949125 : A_C) * (5 * m 1 - 9 * m 2) +
        (8 / 243 : A_C) * (5 * m 3 - 9 * m 5) - (64 / 675 : A_C) * (5 * m 4 - 9 * m 6)) +
      U_C * V_C * (-(123236 / 24249375 : A_C) * (m 0 + (2790 / 77 : A_C) * m 6 + 28 * m 8 - (5904 / 77 : A_C) * m 9) +
        (492944 / 33949125 : A_C) * (m 1 + (927 / 77 : A_C) * m 6 + (49 / 5 : A_C) * m 8 - (21159 / 770 : A_C) * m 9))
  set AX_l : A_C := U_C * (-(8 / 405 : A_C) * (5 * m 3 - 9 * m 4) - (476 / 7185 : A_C) * (5 * m 7 - 9 * m 8) +
      (6916 / 35925 : A_C) * (5 * m 8 - 9 * m 9))
  have hp4_eq : p4_AC = (V_C ^ 2 / (W_C * cb) ^ 4) *
      ((A0U_l / U_C + A0V_l / V_C) * q1_dot + (AY_l * (QY_dot / v_of V_C) + AX_l * (QX_dot / u_of U_C)) * H0_of S Q T ^ 2) :=
    p4_AC_eq
  -- Step 2: 1-line `E0` trace reduction `-(p4_AC * U_C^3 * W_C * cb^4) = -Const + (Av0 / Cv0) * (R12 / M_R) * (bW + W_C)`!
  obtain ⟨hA0U, hA0V, hAY2, hAY3, hAX2⟩ := evalACache_AC_bridge
  obtain ⟨hH0, hAv0, hCv0, _, hBv1701, hqX, hqY, hq1⟩ := evalGeomT_AC_bridge
  have hM0_sub : (M_A_int : A_C) * (A0U_l / U_C) = polyC A0U_U_p := by
    rw [← mul_div_assoc, ← hA0U, mul_div_cancel_left₀ _ hU_ne]
  have hA0V_sub : (M_A_int : A_C) * A0V_l = polyC A0V_p := hA0V.symm
  have hAX_sub : (M_A_int : A_C) * AX_l = polyC AX2_p := hAX2.symm
  have hAY_sub : (M_A_int : A_C) * AY_l = polyC AY2_p + V_C * polyC AY3_p := by
    dsimp only [AY_l]
    linear_combination -hAY2 - V_C * hAY3
  have hE0_W : ιC_K5 k5Params.Av0 * U_C * V_C ^ 2 + (ιC_K5 k5Params.Av0 * polyC k5Params.bW) * V_C + ιC_K5 k5Params.Cv0 * U_C = 0 := by
    have hW : W_C ^ 2 + polyC k5Params.bW * W_C + polyC k5Params.cW = 0 := W_C_relation
    have hcW : polyC k5Params.cW = ιC_K5 k5Params.Cv0 * ιC_K5 k5Params.Av0_inv * U_C ^ 2 := by
      simp [CoverParams.cW, polyC_mul, polyC_pow, polyC_C, polyC_X]
    have hAv_inv : ιC_K5 k5Params.Av0 * ιC_K5 k5Params.Av0_inv = 1 := by
      rw [← map_mul, k5Params_Av0_mul_inv, map_one]
    rw [hcW] at hW
    have hV : W_C = U_C * V_C := by simp only [V_C, mul_div_cancel₀ _ hU_ne]
    rw [hV] at hW
    have hmul := congrArg (fun t => ιC_K5 k5Params.Av0 * t) hW
    simp only [mul_zero] at hmul
    have h1 : ιC_K5 k5Params.Av0 * ((U_C * V_C) ^ 2 + polyC k5Params.bW * (U_C * V_C) +
        ιC_K5 k5Params.Cv0 * ιC_K5 k5Params.Av0_inv * U_C ^ 2) =
        U_C * (ιC_K5 k5Params.Av0 * U_C * V_C ^ 2 + (ιC_K5 k5Params.Av0 * polyC k5Params.bW) * V_C + ιC_K5 k5Params.Cv0 * U_C) := by
      linear_combination (ιC_K5 k5Params.Cv0 * U_C ^ 2) * hAv_inv
    rw [h1] at hmul
    exact (mul_eq_zero.mp hmul).resolve_left hU_ne
  -- Compute `(M_R_int : A_C) * (V_C ^ 2 * (p4_AC * U_C ^ 3 * W_C * cb ^ 4)) = Const * V_C ^ 2 + polyC R13_int_p * V_C`!
  set q1_div_sc : A_C := -polyC A0V_p * polyC (evalUBivLK5 gtK.q1_0_div_sc)
  set pV4_div_sc : A_C := polyC A0U_U_p * polyC (evalUBivLK5 gtK.q1_2_div_sc) -
      (9 * 729 : A_C) * polyC AY3_p * polyC (evalUBivLK5 gtK.DY2_qE_63) * (ιC_K5 gtK.H0_7) ^ 2
  have hMR_def : (M_R_int : A_C) = (M_A_int : A_C) * 1701 * (M_mid_int : A_C) := by
    simp only [M_R_int, Int.cast_mul, Int.cast_ofNat]
  have hM_mid_def : (M_mid_int : A_C) = 7 * 321489 := by
    have hZ : M_mid_int = 7 * 321489 := by unfold M_mid_int; decide
    exact_mod_cast hZ
  have hH0_2_eq : ιC_K5 gtK.H0_7_2 = (7 * H0_of S Q T) ^ 2 := by
    have h2 : gtK.H0_7_2 = gtK.H0_7 ^ 2 := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_geom_bridge.gt_props.2.1
    rw [h2, map_pow, hH0]; simp only [H0_of, S, Q, T, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]
  have hH0_AC : ιC_K5 gtK.H0_7 = 7 * H0_of S Q T := by
    rw [hH0]; simp only [H0_of, S, Q, T, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat]
  have hCv0_AC : ιC_K5 gtK.Cv0_243 = 243 * ιC_K5 k5Params.Cv0 := by rw [hCv0]; simp [map_ofNat]
  set Const_sc : A_C :=
    1701 * ((1 / 243 : A_C) * polyC A0U_U_p * polyC (evalUBivLK5 gtK.q1_1_sc) +
      polyC A0V_p * ιC_K5 k5Params.Av0 * U_C * polyC (evalUBivLK5 gtK.q1_2_div_sc)) +
    (243 : A_C) * ιC_K5 gtK.H0_7_2 * (polyC AY3_p * polyC (evalUBivLK5 gtK.qY_0_321489) -
      (9 * 5103 : A_C) * polyC AY2_p * polyC (evalUBivLK5 gtK.DY2_qE_63) * U_C * ιC_K5 k5Params.Av0 +
      polyC AX2_p * polyC (evalUBivLK5 gtK.qX_1_sc)) -
    ((polyC Bv_1701_p) * pV4_div_sc - 1701 * ιC_K5 k5Params.Av0 * U_C * q1_div_sc)
  have hN_red : (M_R_int : A_C) * (V_C ^ 2 * (p4_AC * U_C ^ 3 * W_C * cb ^ 4)) =
      Const_sc * V_C ^ 2 + polyC R13_int_p * V_C := by
    have hV_mul : V_C ^ 2 * (p4_AC * U_C ^ 3 * W_C * cb ^ 4) =
        V_C * ((A0U_l / U_C + A0V_l / V_C) * q1_dot +
          (AY_l * (QY_dot / v_of V_C) + AX_l * (QX_dot / u_of U_C)) * H0_of S Q T ^ 2) := by
      rw [hp4_eq]
      have hW_UV : W_C = U_C * V_C := by simp only [V_C, mul_div_cancel₀ _ hU_ne]
      rw [hW_UV]
      have halg : ∀ (u v c x : A_C), u ≠ 0 → v ≠ 0 → c ≠ 0 →
          v ^ 2 * (v ^ 2 / (u * v * c) ^ 4 * x * u ^ 3 * (u * v) * c ^ 4) = v * x := by
        intro u v c x hu hv hc; field_simp [hu, hv, hc]
      exact halg U_C V_C cb _ hU_ne hV_ne hcb_ne
    rw [hV_mul, hMR_def]
    have hLHS_expand : (M_A_int : A_C) * 1701 * (M_mid_int : A_C) *
        (V_C * ((A0U_l / U_C + A0V_l / V_C) * q1_dot +
          (AY_l * (QY_dot / v_of V_C) + AX_l * (QX_dot / u_of U_C)) * H0_of S Q T ^ 2)) =
        1701 * (polyC A0U_U_p * V_C + polyC A0V_p) * ((M_mid_int : A_C) * q1_dot) +
        (243 : A_C) * ιC_K5 gtK.H0_7_2 * V_C *
          ((polyC AY2_p + V_C * polyC AY3_p) * (321489 * (QY_dot / v_of V_C)) +
           polyC AX2_p * (321489 * (QX_dot / u_of U_C))) := by
      have halg : ∀ (ma mm v a0u a0v ay ax q1 qy qx h0 : A_C), v ≠ 0 →
          mm = 7 * 321489 →
          ma * 1701 * mm * (v * ((a0u + a0v / v) * q1 + (ay * qy + ax * qx) * h0 ^ 2)) =
          1701 * ((ma * a0u) * v + ma * a0v) * (mm * q1) +
          243 * (7 * h0) ^ 2 * v * ((ma * ay) * (321489 * qy) + (ma * ax) * (321489 * qx)) := by
        intro ma mm v a0u a0v ay ax q1 qy qx h0 hv hmm
        rw [hmm]; field_simp [hv]; ring
      rw [hH0_2_eq, ← hM0_sub, ← hA0V_sub, ← hAY_sub, ← hAX_sub]
      exact halg (M_A_int : A_C) (M_mid_int : A_C) V_C (A0U_l / U_C) A0V_l AY_l AX_l
        q1_dot (QY_dot / v_of V_C) (QX_dot / u_of U_C) (H0_of S Q T) hV_ne hM_mid_def
    rw [hLHS_expand, hq1, ← hqY, ← hqX]
    simp only [R13_int_p, Const_sc, q1_div_sc, pV4_div_sc, polyC_add, polyC_sub, polyC_mul, polyC_C, polyC_X, polyC_ofNat,
      map_mul, map_ofNat, hCv0_AC, hH0_2_eq, hH0_AC, hBv1701]
    have hE := hE0_W
    generalize polyC A0U_U_p = a0u
    generalize polyC A0V_p = a0v
    generalize polyC AY2_p = ay2
    generalize polyC AY3_p = ay3
    generalize polyC AX2_p = ax2
    generalize polyC (evalUBivLK5 gtK.q1_0_div_sc) = q10
    generalize polyC (evalUBivLK5 gtK.q1_1_sc) = q11
    generalize polyC (evalUBivLK5 gtK.q1_2_div_sc) = q12
    generalize polyC (evalUBivLK5 gtK.DY2_qE_63) = dyq
    generalize polyC (evalUBivLK5 gtK.qY_0_321489) = qy0
    generalize polyC (evalUBivLK5 gtK.qX_0_sc) = qx0
    generalize polyC (evalUBivLK5 gtK.qX_1_sc) = qx1
    generalize H0_of S Q T = h0
    generalize polyC k5Params.bW = bw at hE ⊢
    generalize ιC_K5 k5Params.Av0 = av at hE ⊢
    generalize ιC_K5 k5Params.Cv0 = cv at hE ⊢
    generalize U_C = u at hE ⊢
    generalize V_C = v at hE ⊢
    linear_combination (1701 * (a0u * q12 - (9 * 729 : A_C) * ay3 * dyq * (7 * h0) ^ 2) * v + 1701 * a0v * q10) * hE
  -- Divide by `V_C^2` and rewrite `-1 / V_C = (Av0 / Cv0 / U_C) * (bW + W_C)`!
  have hinvV : -(1 / V_C) = (ιC_K5 k5Params.Av0 / ιC_K5 k5Params.Cv0 / U_C) * (polyC k5Params.bW + W_C) := by
    have h1 : V_C * (ιC_K5 k5Params.Av0 * (polyC k5Params.bW + W_C)) = -(ιC_K5 k5Params.Cv0 * U_C) := by
      have hW_UV : W_C = U_C * V_C := by simp only [V_C, mul_div_cancel₀ _ hU_ne]
      rw [hW_UV]; linear_combination hE0_W
    field_simp [hV_ne, hCv0_ne, hU_ne]
    linear_combination -h1
  -- Express `-(p4_AC * U_C^3 * W_C * cb^4)` in `evalAC` form and apply `trace_AC_euler`!
  set q1_div_rat : RatFunc K5 := -toRat A0V_p * toRat (evalUBivLK5 gtK.q1_0_div_sc)
  set pV4_div_rat : RatFunc K5 := toRat A0U_U_p * toRat (evalUBivLK5 gtK.q1_2_div_sc) -
      (9 * 729 : RatFunc K5) * toRat AY3_p * toRat (evalUBivLK5 gtK.DY2_qE_63) * (RatFunc.C gtK.H0_7) ^ 2
  set Const_rat : RatFunc K5 :=
    1701 * ((1 / 243 : RatFunc K5) * toRat A0U_U_p * toRat (evalUBivLK5 gtK.q1_1_sc) +
      toRat A0V_p * RatFunc.C k5Params.Av0 * RatFunc.X * toRat (evalUBivLK5 gtK.q1_2_div_sc)) +
    (243 : RatFunc K5) * RatFunc.C gtK.H0_7_2 * (toRat AY3_p * toRat (evalUBivLK5 gtK.qY_0_321489) -
      (9 * 5103 : RatFunc K5) * toRat AY2_p * toRat (evalUBivLK5 gtK.DY2_qE_63) * RatFunc.X * RatFunc.C k5Params.Av0 +
      toRat AX2_p * toRat (evalUBivLK5 gtK.qX_1_sc)) -
    ((toRat Bv_1701_p) * pV4_div_rat - 1701 * RatFunc.C k5Params.Av0 * RatFunc.X * q1_div_rat)
  have hN_evalAC :
      -(p4_AC * U_C ^ 3 * W_C * cb ^ 4) =
        evalAC ⟨-toRat (Polynomial.C (M_R_int : K5)⁻¹) * Const_rat +
            RatFunc.C (k5Params.Av0 / (k5Params.Cv0 * (M_R_int : K5))) * toRat R12_int_p * toRat k5Params.bW,
          RatFunc.C (k5Params.Av0 / (k5Params.Cv0 * (M_R_int : K5))) * toRat R12_int_p⟩ := by
    have hιC_K5 : ∀ c : K5, ιC_K5 c = ιC_rat (RatFunc.C c) := fun _ => rfl
    have hConst_in_base : Const_sc = ιC_rat Const_rat := by
      simp only [Const_sc, Const_rat, pV4_div_sc, pV4_div_rat, q1_div_sc, q1_div_rat,
        polyC, hιC_K5, U_C, map_add, map_sub, map_neg, map_mul, map_div₀, map_pow, map_one, map_ofNat]
    have hR13_C : polyC R13_int_p = U_C * polyC R12_int_p := by
      rw [R13_int_p_eq_X_mul_R12, polyC_mul, polyC_X]
    have hN_eq : -(p4_AC * U_C ^ 3 * W_C * cb ^ 4) =
        -(M_R_int : A_C)⁻¹ * Const_sc +
        (ιC_K5 k5Params.Av0 / (ιC_K5 k5Params.Cv0 * (M_R_int : A_C))) * polyC R12_int_p * (polyC k5Params.bW + W_C) := by
      have hstep : ∀ (P4 C0 R12 MR Av Cv U V bW W : A_C),
          MR ≠ 0 → V ≠ 0 → U ≠ 0 → Cv ≠ 0 →
          MR * (V ^ 2 * P4) = C0 * V ^ 2 + U * R12 * V →
          -(1 / V) = (Av / Cv / U) * (bW + W) →
          -P4 = -MR⁻¹ * C0 + (Av / (Cv * MR)) * R12 * (bW + W) := by
        intro P4 C0 R12 MR Av Cv U V bW W hMR hV hU hCv hred hinv
        have hdiv := congrArg (fun t => -t / (MR * V ^ 2)) hred
        have hl : -(MR * (V ^ 2 * P4)) / (MR * V ^ 2) = -P4 := by field_simp [hMR, hV]
        rw [hl] at hdiv
        rw [hdiv]
        calc -(C0 * V ^ 2 + U * R12 * V) / (MR * V ^ 2) =
              -MR⁻¹ * C0 + (-(1 / V)) * (U * R12 / MR) := by field_simp [hMR, hV]; ring
          _ = -MR⁻¹ * C0 + (Av / (Cv * MR)) * R12 * (bW + W) := by rw [hinv]; field_simp [hU, hCv, hMR]
      exact hstep _ _ _ _ _ _ _ _ _ _ hMR_ne hV_ne hU_ne hCv0_ne (by rw [← hR13_C]; exact hN_red) hinvV
    rw [hN_eq, hConst_in_base]
    have hMR_C : (M_R_int : A_C) = ιC_rat (RatFunc.C (M_R_int : K5)) := by
      simp only [map_intCast]
    have hMR_inv : (M_R_int : A_C)⁻¹ = ιC_rat (toRat (Polynomial.C (M_R_int : K5)⁻¹)) := by
      rw [hMR_C, ← map_inv₀ ιC_rat, ← map_inv₀ RatFunc.C, toRat, RatFunc.algebraMap_C]
    have hAv_C : ιC_K5 k5Params.Av0 / (ιC_K5 k5Params.Cv0 * (M_R_int : A_C)) =
        ιC_rat (RatFunc.C (k5Params.Av0 / (k5Params.Cv0 * (M_R_int : K5)))) := by
      rw [hMR_C, hιC_K5, hιC_K5]; simp only [map_div₀, map_mul]
    rw [hMR_inv, hAv_C]
    simp only [evalAC, polyC, map_add, map_neg, map_mul]
    generalize ιC_rat (toRat (Polynomial.C (M_R_int : K5)⁻¹)) = a
    generalize ιC_rat Const_rat = c0
    generalize ιC_rat (RatFunc.C (k5Params.Av0 / (k5Params.Cv0 * (M_R_int : K5)))) = k
    generalize ιC_rat (toRat R12_int_p) = r12
    generalize ιC_rat (toRat k5Params.bW) = bw
    ring
  -- Plug `hN_evalAC` into `eta_AC_main` and apply `trace_AC_euler` with `y = PairAlg.ofScalar 1`!
  set den_rat : RatFunc K5 :=
    RatFunc.C (81 * k5Params.Av0) * toRat k5Params.Q7_z * toRat k5Params.Q5_z
  set num_pair : PairAlg (RatFunc K5) :=
    ⟨-toRat (Polynomial.C (M_R_int : K5)⁻¹) * Const_rat +
       RatFunc.C (k5Params.Av0 / (k5Params.Cv0 * (M_R_int : K5))) * toRat R12_int_p * toRat k5Params.bW,
     RatFunc.C (k5Params.Av0 / (k5Params.Cv0 * (M_R_int : K5))) * toRat R12_int_p⟩
  have heta_main : eta_AC_main =
      evalAC (PairAlg.smul den_rat⁻¹ num_pair) /
        (evalAC (PairAlg.ofScalar (1 : RatFunc K5)) * (2 * W_C + ιC_rat (toRat k5Params.bW))) := by
    rw [evalAC_smul, evalAC_ofScalar, map_one, one_mul, ← hN_evalAC]
    have hιC_K5 : ∀ c : K5, ιC_K5 c = ιC_rat (RatFunc.C c) := fun _ => rfl
    have h81Av0 : (81 : A_C) * ιC_K5 k5Params.Av0 = ιC_rat (RatFunc.C (81 * k5Params.Av0)) := by
      rw [hιC_K5]; simp only [map_mul, map_ofNat]
    have hden_eq : ιC_rat den_rat⁻¹ =
        (81 * ιC_K5 k5Params.Av0 * polyC k5Params.Q7_z * polyC k5Params.Q5_z)⁻¹ := by
      dsimp only [den_rat, polyC]
      rw [map_inv₀, map_mul, map_mul, ← h81Av0]
    rw [hden_eq]
    have hdiv_alg : ∀ (N a b c d : A_C), N / (a * b * c * d) = (a * c * d)⁻¹ * N / b := fun N a b c d => by
      simp only [div_eq_mul_inv, mul_inv]; ring
    dsimp only [eta_AC_main]
    change -(p4_AC * U_C ^ 3 * W_C * cb ^ 4) /
        (81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW) * polyC k5Params.Q7_z * polyC k5Params.Q5_z) =
      (81 * ιC_K5 k5Params.Av0 * polyC k5Params.Q7_z * polyC k5Params.Q5_z)⁻¹ *
        -(p4_AC * U_C ^ 3 * W_C * cb ^ 4) / (2 * W_C + polyC k5Params.bW)
    exact hdiv_alg (-(p4_AC * U_C ^ 3 * W_C * cb ^ 4))
      (81 * ιC_K5 k5Params.Av0) (2 * W_C + polyC k5Params.bW) (polyC k5Params.Q7_z) (polyC k5Params.Q5_z)
  rw [heta_main, trace_AC_euler (PairAlg.smul den_rat⁻¹ num_pair) (PairAlg.ofScalar 1) (by simp [PairAlg.nm, PairAlg.ofScalar])]
  simp only [PairAlg.nm, PairAlg.ofScalar, PairAlg.smul, num_pair, den_rat,
    pow_two, mul_zero, zero_mul, add_zero, sub_zero, mul_one, div_one, map_mul, map_div₀, map_ofNat]
  have hAv_R : (RatFunc.C k5Params.Av0 : RatFunc K5) ≠ 0 := by
    simpa [map_eq_zero] using Av0_K5_ne_zero
  have hCv_R : (RatFunc.C k5Params.Cv0 : RatFunc K5) ≠ 0 := by
    simpa [map_eq_zero] using k5Params_Cv0_ne
  have hMR_R : (RatFunc.C (M_R_int : K5) : RatFunc K5) ≠ 0 := by
    have hZ : M_R_int ≠ 0 := by unfold M_R_int M_A_int L_all_A M_mid_int; decide
    have hK : (M_R_int : K5) ≠ 0 := Int.cast_ne_zero.mpr hZ
    simpa [map_eq_zero] using hK
  have hQ7_R : toRat k5Params.Q7_z ≠ 0 := by
    simpa [toRat, map_eq_zero] using Q7_K5_ne_zero
  have hQ5_R : toRat k5Params.Q5_z ≠ 0 := by
    simpa [toRat, map_eq_zero] using Q5_K5_ne_zero
  have hrat_alg : ∀ (a c m q7 q5 r12 : RatFunc K5), a ≠ 0 → c ≠ 0 → m ≠ 0 → q7 ≠ 0 → q5 ≠ 0 →
      (81 * a * q7 * q5)⁻¹ * (a / (c * m) * r12) = r12 / (81 * c * m * (q7 * q5)) := by
    intro a c m q7 q5 r12 ha hc hm hq7 hq5; field_simp [ha, hc, hm, hq7, hq5]
  exact hrat_alg _ _ _ _ _ _ hAv_R hCv_R hMR_R hQ7_R hQ5_R


end SymmetricSexticResidual.LocalResidueQ5

theorem solution :
    Algebra.trace (RatFunc SymmetricSexticResidual.K5Field.K5)
        SymmetricSexticResidual.CoverResidue.A_C
        SymmetricSexticResidual.LocalResidueQ5.eta_AC_main =
      SymmetricSexticResidual.CoverResidue.toRat SymmetricSexticResidual.LocalResidueQ5.R12_int_p /
        (RatFunc.C (81 * SymmetricSexticResidual.CoverAlgebra.k5Params.Cv0 *
            (SymmetricSexticResidual.LocalResidueQ5.M_R_int : SymmetricSexticResidual.K5Field.K5)) *
          SymmetricSexticResidual.CoverResidue.toRat
            (SymmetricSexticResidual.CoverAlgebra.k5Params.Q7_z *
              SymmetricSexticResidual.CoverAlgebra.k5Params.Q5_z)) :=
  SymmetricSexticResidual.LocalResidueQ5.trace_AC_eta_AC_main_eq
