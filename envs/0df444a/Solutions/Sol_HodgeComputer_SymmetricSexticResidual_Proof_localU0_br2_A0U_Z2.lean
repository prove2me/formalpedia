-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localU0_br2_A0U_Z2
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T13:53:16.054679+00:00
-- url     : https://prove2.me/submissions/aec1888d-4882-4c63-99c1-b5d2d0052e46

import Definitions.Def_HodgeComputerSSR_BranchHelpers
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localU0_br2_A0U_poly

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueU0
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  QuadraticCovers CrossedRationalResidue Polynomial
open scoped BigOperators LaurentSeries PowerSeries

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

private lemma br2_0_A0U_Z2_eval :
    let A := 5 * S_K - 9 * Q_K
    let B := T_K - 3
    let d_ab := 6 * S_K * B
    let Q_quad := 11943020 * S_K ^ 2 - 876486 * S_K * Q_K + 8382500 * S_K * T_K +
      5029500 * Q_K * T_K - 14837025 * S_K - 33647355 * Q_K
    let a_du : Dual K5 := Dual.C d_ab⁻¹ * ⟨6 * S_K ^ 2, 6 * S_K * B⟩
    let b_du : Dual K5 := Dual.C d_ab⁻¹ * ⟨6 * S_K * Q_K, (5 * S_K - 3 * Q_K) * B⟩
    Dual.C (d_ab ^ 3) * A0U_12_of Dual.C a_du b_du =
      ⟨(8248380 / 51331077 : K5) * (5 * S_K - 3 * Q_K) * S_K ^ 3 * A ^ 2,
       -(2 / 51331077 : K5) * B * S_K ^ 2 * A ^ 2 * Q_quad⟩ := by
  intro A B d_ab Q_quad a_du b_du
  have hS := S_K_ne_zero; have hB := T_K_sub_3_ne
  have h6_ne : (6 : K5) ≠ 0 := by exact_mod_cast (by decide : (6 : ℕ) ≠ 0)
  have hd_ab_ne : d_ab ≠ 0 := mul_ne_zero (mul_ne_zero h6_ne hS) hB
  set inv_d : K5 := d_ab⁻¹
  have hd_inv : d_ab * inv_d = 1 := mul_inv_cancel₀ hd_ab_ne
  set a_s : Dual K5 := ⟨6 * S_K ^ 2, 6 * S_K * B⟩
  set b_s : Dual K5 := ⟨6 * S_K * Q_K, (5 * S_K - 3 * Q_K) * B⟩
  set ξS_s : Dual K5 := ⟨-18 * S_K ^ 2, -6 * S_K * B * T_K⟩
  set ξQ_s : Dual K5 := ⟨-18 * S_K * Q_K, -(5 * S_K - 3 * Q_K) * B * T_K⟩
  have ha_du_eq : a_du = Dual.C inv_d * a_s := rfl
  have hb_du_eq : b_du = Dual.C inv_d * b_s := rfl
  have hξS_eq : Dual.C S_K - a_du * Dual.C T_K = Dual.C inv_d * ξS_s := by
    ext
    · simp only [a_du, ξS_s, Dual.C_val, Dual.sub_val, Dual.mul_val]
      have h := hd_inv; dsimp only [d_ab, B] at h; linear_combination S_K * h.symm
    · simp only [a_du, ξS_s, Dual.C_val, Dual.C_eps, Dual.sub_eps, Dual.mul_eps, Dual.mul_val]; ring
  have hξQ_eq : Dual.C Q_K - b_du * Dual.C T_K = Dual.C inv_d * ξQ_s := by
    ext
    · simp only [b_du, ξQ_s, Dual.C_val, Dual.sub_val, Dual.mul_val]
      have h := hd_inv; dsimp only [d_ab, B] at h; linear_combination Q_K * h.symm
    · simp only [b_du, ξQ_s, Dual.C_val, Dual.C_eps, Dual.sub_eps, Dual.mul_eps, Dual.mul_val]; ring
  let dHS_v := fun s q : Dual K5 => Dual.C (-(25 / 243 : K5)) * (5 * s - 9 * q) * (15 * s - 9 * q)
  let dHS_e := fun s q : Dual K5 =>
    Dual.C (143 / 81 : K5) * s ^ 2 - Dual.C (184 / 27 : K5) * s * q + Dual.C (52 / 9 : K5) * q ^ 2
  let dHQ_v := fun s q : Dual K5 => Dual.C (50 / 27 : K5) * s * (5 * s - 9 * q)
  let dHQ_e := fun (s q : Dual K5) (v0 : K5) =>
    Dual.C (-(92 / 27 : K5)) * s ^ 2 + Dual.C (104 / 9 : K5) * s * q - Dual.C (22 / 3 : K5) * q ^ 2 +
      Dual.C ((10 / 7 : K5) * v0) * q + Dual.C ((10 / 7 : K5) * v0 ^ 2)
  have hdHS_v (s q : Dual K5) : (dHS_12_of Dual.C (Dual.C inv_d * s) (Dual.C inv_d * q)).val =
      Dual.C (inv_d ^ 2) * dHS_v s q := by
    simp only [dHS_12_of, dHS_v, map_pow]; ring
  have hdHS_e (s q : Dual K5) : (dHS_12_of Dual.C (Dual.C inv_d * s) (Dual.C inv_d * q)).eps =
      Dual.C (inv_d ^ 2) * dHS_e s q := by
    simp only [dHS_12_of, dHS_e, map_pow]; ring
  have hdHQ_v (s q : Dual K5) (v0 : K5) : (dHQ_12_of Dual.C (Dual.C inv_d * s) (Dual.C inv_d * q) v0).val =
      Dual.C (inv_d ^ 2) * dHQ_v s q := by
    simp only [dHQ_12_of, dHQ_v, map_pow]; ring
  have hdHQ0_e (s q : Dual K5) : (dHQ_12_of Dual.C (Dual.C inv_d * s) (Dual.C inv_d * q) 0).eps =
      Dual.C (inv_d ^ 2) * dHQ_e s q 0 := by
    simp only [dHQ_12_of, dHQ_e, mul_zero, zero_pow (by decide : 2 ≠ 0), map_zero, zero_mul, add_zero, map_pow]; ring
  have hdHQ1_e (s q : Dual K5) : (dHQ_12_of Dual.C (Dual.C inv_d * s) (Dual.C inv_d * q) 1).eps =
      Dual.C (inv_d ^ 2) * dHQ_e s q d_ab := by
    have h1 : Dual.C (10 / 7 : K5) * (Dual.C inv_d * q) = Dual.C (inv_d ^ 2) * (Dual.C ((10 / 7 : K5) * d_ab) * q) := by
      have : (10 / 7 : K5) * inv_d = inv_d ^ 2 * ((10 / 7 : K5) * d_ab) := by
        linear_combination -(10 / 7 : K5) * inv_d * hd_inv
      rw [← mul_assoc, ← map_mul, this, map_mul, mul_assoc]
    have h2 : Dual.C (10 / 7 : K5) = Dual.C (inv_d ^ 2) * Dual.C ((10 / 7 : K5) * d_ab ^ 2) := by
      rw [← map_mul]; congr 1
      have h2 : (d_ab * inv_d) ^ 2 = 1 := by rw [hd_inv, one_pow]
      linear_combination -(10 / 7 : K5) * h2
    simp only [dHQ_12_of, dHQ_e, mul_one, one_pow]
    rw [h1, h2]; simp only [map_pow]; ring
  let a2_v := dHS_v a_s b_s; let a2_e := dHS_e a_s b_s
  let a0_v := dHS_v ξS_s ξQ_s; let a0_e := dHS_e ξS_s ξQ_s
  let a1_v := dHS_v (a_s + ξS_s) (b_s + ξQ_s) - a2_v - a0_v
  let a1_e := dHS_e (a_s + ξS_s) (b_s + ξQ_s) - a2_e - a0_e
  let b2_v := dHQ_v a_s b_s; let b2_e := dHQ_e a_s b_s 0
  let b0_v := dHQ_v ξS_s ξQ_s; let b0_e := dHQ_e ξS_s ξQ_s d_ab
  let b1_v := dHQ_v (a_s + ξS_s) (b_s + ξQ_s) - b2_v - b0_v
  let b1_e := dHQ_e (a_s + ξS_s) (b_s + ξQ_s) 0 - b2_e - dHQ_e ξS_s ξQ_s 0 + Dual.C ((10 / 7 : K5) * d_ab) * b_s
  let d20_e := a2_v * b0_e + a2_e * b0_v - a0_v * b2_e - a0_e * b2_v
  let d21_e := a2_v * b1_e + a2_e * b1_v - a1_v * b2_e - a1_e * b2_v
  let d10_e := a1_v * b0_e + a1_e * b0_v - a0_v * b1_e - a0_e * b1_v
  let m_sc : Fin 10 → Dual K5 := fun mi =>
    let (m2, m1, m0) : Dual K5 × Dual K5 × Dual K5 := match mi with
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
    Dual.C (1 / 16 : K5) * (m2 * d10_e - m1 * d20_e + m0 * d21_e)
  have hm_eq (mi : Fin 10) : m_sc mi = br2_0_m_sc S_K Q_K T_K mi := rfl
  have hnum_sc (mi : Fin 10) : Dual.C (d_ab ^ 6) * numM_12_of Dual.C mi a_du b_du = m_sc mi := by
    have hs : a_du + Dual.C inv_d * ξS_s = Dual.C inv_d * (a_s + ξS_s) := by rw [ha_du_eq]; ring
    have hq : b_du + Dual.C inv_d * ξQ_s = Dual.C inv_d * (b_s + ξQ_s) := by rw [hb_du_eq]; ring
    have hb_term : Dual.C (10 / 7 : K5) * b_du = Dual.C (inv_d ^ 2) * (Dual.C ((10 / 7 : K5) * d_ab) * b_s) := by
      have : (10 / 7 : K5) * inv_d = inv_d ^ 2 * ((10 / 7 : K5) * d_ab) := by
        calc (10 / 7 : K5) * inv_d = (10 / 7 : K5) * inv_d * (d_ab * inv_d) := by rw [hd_inv, mul_one]
          _ = _ := by ring
      rw [hb_du_eq, ← mul_assoc, ← map_mul, this, map_mul, mul_assoc]
    have hd_pow6 : Dual.C (d_ab ^ 6) * (Dual.C inv_d ^ 2 * Dual.C (inv_d ^ 4)) = (1 : Dual K5) := by
      rw [← map_pow, ← map_mul, ← map_mul]
      rw [show d_ab ^ 6 * (inv_d ^ 2 * inv_d ^ 4) = (d_ab * inv_d) ^ 6 by ring, hd_inv, one_pow, map_one]
    have hd_pow5 : Dual.C (d_ab ^ 6) * (Dual.C inv_d * Dual.C (inv_d ^ 4)) = Dual.C d_ab := by
      rw [← map_mul, ← map_mul]; congr 1
      rw [show d_ab ^ 6 * (inv_d * inv_d ^ 4) = d_ab * (d_ab * inv_d) ^ 5 by ring, hd_inv]; ring
    have hd_pow4 : Dual.C (d_ab ^ 6) * Dual.C (inv_d ^ 4) = Dual.C (d_ab ^ 2) := by
      rw [← map_mul]; congr 1
      rw [show d_ab ^ 6 * inv_d ^ 4 = d_ab ^ 2 * (d_ab * inv_d) ^ 4 by ring, hd_inv]; ring
    have hdet : ∀ (x y z w : Dual (Dual K5)) (xv xe yv ye zv ze wv we : Dual K5),
        x.val = Dual.C (inv_d ^ 2) * xv → x.eps = Dual.C (inv_d ^ 2) * xe →
        y.val = Dual.C (inv_d ^ 2) * yv → y.eps = Dual.C (inv_d ^ 2) * ye →
        z.val = Dual.C (inv_d ^ 2) * zv → z.eps = Dual.C (inv_d ^ 2) * ze →
        w.val = Dual.C (inv_d ^ 2) * wv → w.eps = Dual.C (inv_d ^ 2) * we →
        (x * y - z * w).eps = Dual.C (inv_d ^ 4) * (xv * ye + xe * yv - zv * we - ze * wv) := by
      intro x y z w xv xe yv ye zv ze wv we hxv hxe hyv hye hzv hze hwv hwe
      simp only [Dual.sub_eps, Dual.mul_eps, hxv, hxe, hyv, hye, hzv, hze, hwv, hwe]
      have hp : Dual.C (inv_d ^ 2) * Dual.C (inv_d ^ 2) = Dual.C (inv_d ^ 4) := by
        rw [← map_mul]; congr 1; ring
      linear_combination (xv * ye + xe * yv - zv * we - ze * wv) * hp
    have h10 : ((dHS_12_of Dual.C (a_du + Dual.C inv_d * ξS_s) (b_du + Dual.C inv_d * ξQ_s) -
        dHS_12_of Dual.C a_du b_du - dHS_12_of Dual.C (Dual.C inv_d * ξS_s) (Dual.C inv_d * ξQ_s)) *
        dHQ_12_of Dual.C (Dual.C inv_d * ξS_s) (Dual.C inv_d * ξQ_s) 1 -
        dHS_12_of Dual.C (Dual.C inv_d * ξS_s) (Dual.C inv_d * ξQ_s) *
        (dHQ_12_of Dual.C (a_du + Dual.C inv_d * ξS_s) (b_du + Dual.C inv_d * ξQ_s) 0 -
          dHQ_12_of Dual.C a_du b_du 0 - dHQ_12_of Dual.C (Dual.C inv_d * ξS_s) (Dual.C inv_d * ξQ_s) 0 +
          ⟨0, Dual.C (10 / 7 : K5) * b_du⟩)).eps = Dual.C (inv_d ^ 4) * d10_e := by
      refine hdet _ _ _ _ a1_v a1_e b0_v b0_e a0_v a0_e b1_v b1_e ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rw [hs, hq]; simp only [ha_du_eq, hb_du_eq, Dual.sub_val, hdHS_v, a1_v, a2_v, a0_v]; ring
      · rw [hs, hq]; simp only [ha_du_eq, hb_du_eq, Dual.sub_eps, hdHS_e, a1_e, a2_e, a0_e]; ring
      · exact hdHQ_v _ _ _
      · exact hdHQ1_e _ _
      · exact hdHS_v _ _
      · exact hdHS_e _ _
      · rw [hs, hq]; simp only [ha_du_eq, hb_du_eq, Dual.add_val, Dual.sub_val, hdHQ_v, b1_v, b2_v, b0_v]; ring
      · rw [hs, hq, hb_term]; simp only [ha_du_eq, hb_du_eq, Dual.add_eps, Dual.sub_eps, hdHQ0_e, b1_e, b2_e]; ring
    have h20 : (dHS_12_of Dual.C a_du b_du *
        dHQ_12_of Dual.C (Dual.C inv_d * ξS_s) (Dual.C inv_d * ξQ_s) 1 -
        dHS_12_of Dual.C (Dual.C inv_d * ξS_s) (Dual.C inv_d * ξQ_s) *
        dHQ_12_of Dual.C a_du b_du 0).eps = Dual.C (inv_d ^ 4) * d20_e := by
      rw [ha_du_eq, hb_du_eq]
      refine hdet _ _ _ _ a2_v a2_e b0_v b0_e a0_v a0_e b2_v b2_e ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · exact hdHS_v _ _
      · exact hdHS_e _ _
      · exact hdHQ_v _ _ _
      · exact hdHQ1_e _ _
      · exact hdHS_v _ _
      · exact hdHS_e _ _
      · exact hdHQ_v _ _ _
      · exact hdHQ0_e _ _
    have h21 : (dHS_12_of Dual.C a_du b_du *
        (dHQ_12_of Dual.C (a_du + Dual.C inv_d * ξS_s) (b_du + Dual.C inv_d * ξQ_s) 0 -
          dHQ_12_of Dual.C a_du b_du 0 - dHQ_12_of Dual.C (Dual.C inv_d * ξS_s) (Dual.C inv_d * ξQ_s) 0 +
          ⟨0, Dual.C (10 / 7 : K5) * b_du⟩) -
        (dHS_12_of Dual.C (a_du + Dual.C inv_d * ξS_s) (b_du + Dual.C inv_d * ξQ_s) -
          dHS_12_of Dual.C a_du b_du - dHS_12_of Dual.C (Dual.C inv_d * ξS_s) (Dual.C inv_d * ξQ_s)) *
        dHQ_12_of Dual.C a_du b_du 0).eps = Dual.C (inv_d ^ 4) * d21_e := by
      refine hdet _ _ _ _ a2_v a2_e b1_v b1_e a1_v a1_e b2_v b2_e ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rw [ha_du_eq, hb_du_eq]; exact hdHS_v _ _
      · rw [ha_du_eq, hb_du_eq]; exact hdHS_e _ _
      · rw [hs, hq]; simp only [ha_du_eq, hb_du_eq, Dual.add_val, Dual.sub_val, hdHQ_v, b1_v, b2_v, b0_v]; ring
      · rw [hs, hq, hb_term]; simp only [ha_du_eq, hb_du_eq, Dual.add_eps, Dual.sub_eps, hdHQ0_e, b1_e, b2_e]; ring
      · rw [hs, hq]; simp only [ha_du_eq, hb_du_eq, Dual.sub_val, hdHS_v, a1_v, a2_v, a0_v]; ring
      · rw [hs, hq]; simp only [ha_du_eq, hb_du_eq, Dual.sub_eps, hdHS_e, a1_e, a2_e, a0_e]; ring
      · rw [ha_du_eq, hb_du_eq]; exact hdHQ_v _ _ _
      · rw [ha_du_eq, hb_du_eq]; exact hdHQ0_e _ _
    clear_value a2_v a2_e a0_v a0_e a1_v a1_e b2_v b2_e b0_v b0_e b1_v b1_e d20_e d21_e d10_e
    have hbody (m2 m1 m0 : Dual K5) :
        Dual.C (d_ab ^ 6) * (Dual.C (1 / 16 : K5) *
          ((Dual.C inv_d ^ 2 * m2) * (Dual.C (inv_d ^ 4) * d10_e) -
           (Dual.C inv_d ^ 2 * m1) * (Dual.C (inv_d ^ 4) * d20_e) +
           (Dual.C inv_d ^ 2 * m0) * (Dual.C (inv_d ^ 4) * d21_e))) =
        Dual.C (1 / 16 : K5) * (m2 * d10_e - m1 * d20_e + m0 * d21_e) := by
      linear_combination (Dual.C (1 / 16 : K5) * (m2 * d10_e - m1 * d20_e + m0 * d21_e)) * hd_pow6
    have hbody1 (m2 m1 m0 : Dual K5) :
        Dual.C (d_ab ^ 6) * (Dual.C (1 / 16 : K5) *
          ((Dual.C inv_d * m2) * (Dual.C (inv_d ^ 4) * d10_e) -
           (Dual.C inv_d * m1) * (Dual.C (inv_d ^ 4) * d20_e) +
           (Dual.C inv_d * m0) * (Dual.C (inv_d ^ 4) * d21_e))) =
        Dual.C (1 / 16 : K5) * ((Dual.C d_ab * m2) * d10_e - (Dual.C d_ab * m1) * d20_e + (Dual.C d_ab * m0) * d21_e) := by
      linear_combination (Dual.C (1 / 16 : K5) * (m2 * d10_e - m1 * d20_e + m0 * d21_e)) * hd_pow5
    have hbody0 (m2 m1 m0 : Dual K5) :
        Dual.C (d_ab ^ 6) * (Dual.C (1 / 16 : K5) *
          (m2 * (Dual.C (inv_d ^ 4) * d10_e) -
           m1 * (Dual.C (inv_d ^ 4) * d20_e) +
           m0 * (Dual.C (inv_d ^ 4) * d21_e))) =
        Dual.C (1 / 16 : K5) * ((Dual.C (d_ab ^ 2) * m2) * d10_e - (Dual.C (d_ab ^ 2) * m1) * d20_e + (Dual.C (d_ab ^ 2) * m0) * d21_e) := by
      linear_combination (Dual.C (1 / 16 : K5) * (m2 * d10_e - m1 * d20_e + m0 * d21_e)) * hd_pow4
    dsimp only [numM_12_of, m_sc]
    rw [hξS_eq, hξQ_eq, h10, h20, h21]
    fin_cases mi
    · rw [show a_du ^ 2 * (Dual.C (inv_d ^ 4) * d10_e) - 2 * a_du * (Dual.C inv_d * ξS_s) * (Dual.C (inv_d ^ 4) * d20_e) +
            (Dual.C inv_d * ξS_s) ^ 2 * (Dual.C (inv_d ^ 4) * d21_e) =
            (Dual.C inv_d ^ 2 * a_s ^ 2) * (Dual.C (inv_d ^ 4) * d10_e) -
            (Dual.C inv_d ^ 2 * (2 * a_s * ξS_s)) * (Dual.C (inv_d ^ 4) * d20_e) +
            (Dual.C inv_d ^ 2 * ξS_s ^ 2) * (Dual.C (inv_d ^ 4) * d21_e) by rw [ha_du_eq]; ring]
      exact hbody _ _ _
    · rw [show (a_du * b_du) * (Dual.C (inv_d ^ 4) * d10_e) -
            (a_du * (Dual.C inv_d * ξQ_s) + b_du * (Dual.C inv_d * ξS_s)) * (Dual.C (inv_d ^ 4) * d20_e) +
            (Dual.C inv_d * ξS_s * (Dual.C inv_d * ξQ_s)) * (Dual.C (inv_d ^ 4) * d21_e) =
            (Dual.C inv_d ^ 2 * (a_s * b_s)) * (Dual.C (inv_d ^ 4) * d10_e) -
            (Dual.C inv_d ^ 2 * (a_s * ξQ_s + b_s * ξS_s)) * (Dual.C (inv_d ^ 4) * d20_e) +
            (Dual.C inv_d ^ 2 * (ξS_s * ξQ_s)) * (Dual.C (inv_d ^ 4) * d21_e) by rw [ha_du_eq, hb_du_eq]; ring]
      exact hbody _ _ _
    · rw [show b_du ^ 2 * (Dual.C (inv_d ^ 4) * d10_e) - 2 * b_du * (Dual.C inv_d * ξQ_s) * (Dual.C (inv_d ^ 4) * d20_e) +
            (Dual.C inv_d * ξQ_s) ^ 2 * (Dual.C (inv_d ^ 4) * d21_e) =
            (Dual.C inv_d ^ 2 * b_s ^ 2) * (Dual.C (inv_d ^ 4) * d10_e) -
            (Dual.C inv_d ^ 2 * (2 * b_s * ξQ_s)) * (Dual.C (inv_d ^ 4) * d20_e) +
            (Dual.C inv_d ^ 2 * ξQ_s ^ 2) * (Dual.C (inv_d ^ 4) * d21_e) by rw [hb_du_eq]; ring]
      exact hbody _ _ _
    · simpa only [ha_du_eq, mul_zero, zero_mul] using hbody1 a_s ξS_s 0
    · simpa only [ha_du_eq, mul_zero, zero_mul] using hbody1 0 a_s ξS_s
    · simpa only [hb_du_eq, mul_zero, zero_mul] using hbody1 b_s ξQ_s 0
    · simpa only [hb_du_eq, mul_zero, zero_mul] using hbody1 0 b_s ξQ_s
    · simpa only [mul_one, mul_zero, zero_mul] using hbody0 1 0 0
    · simpa only [mul_one, mul_zero, zero_mul] using hbody0 0 1 0
    · simpa only [mul_one, mul_zero, zero_mul] using hbody0 0 0 1
  have hpoly : Dual.C (d_ab ^ 6) * A0U_12_of Dual.C a_du b_du =
      Dual.C (d_ab ^ 3) * ⟨(8248380 / 51331077 : K5) * (5 * S_K - 3 * Q_K) * S_K ^ 3 * A ^ 2,
        -(2 / 51331077 : K5) * B * S_K ^ 2 * A ^ 2 * Q_quad⟩ := by
    have hlhs : Dual.C (d_ab ^ 6) * A0U_12_of Dual.C a_du b_du =
        Dual.C (-(19708 / 1257375 : K5)) * (5 * m_sc 0 - 9 * m_sc 1) +
        Dual.C (1472 / 1257375 : K5) * (5 * m_sc 1 - 9 * m_sc 2) -
        Dual.C (16 / 729 : K5) * (5 * m_sc 3 - 9 * m_sc 5) +
        Dual.C (188 / 2025 : K5) * (5 * m_sc 4 - 9 * m_sc 6) := by
      simp only [A0U_12_of, ← hnum_sc]; ring
    rw [hlhs, hm_eq 0, hm_eq 1, hm_eq 2, hm_eq 3, hm_eq 4, hm_eq 5, hm_eq 6]
    exact HodgeComputer.SymmetricSexticResidual.Proof.localU0_br2_A0U_poly S_K Q_K T_K
  have hmul_eq : Dual.C (d_ab ^ 3) * (Dual.C (d_ab ^ 3) * A0U_12_of Dual.C a_du b_du) =
      Dual.C (d_ab ^ 3) * ⟨(8248380 / 51331077 : K5) * (5 * S_K - 3 * Q_K) * S_K ^ 3 * A ^ 2,
        -(2 / 51331077 : K5) * B * S_K ^ 2 * A ^ 2 * Q_quad⟩ := by
    rw [← mul_assoc, ← map_mul, show d_ab ^ 3 * d_ab ^ 3 = d_ab ^ 6 by ring, hpoly]
  ext
  · apply mul_left_cancel₀ (pow_ne_zero 3 hd_ab_ne)
    have h := congrArg Dual.val hmul_eq
    simp only [Dual.mul_val, Dual.C_val] at h
    exact h
  · apply mul_left_cancel₀ (pow_ne_zero 3 hd_ab_ne)
    have h := congrArg Dual.eps hmul_eq
    simp only [Dual.mul_eps, Dual.mul_val, Dual.C_val, Dual.C_eps, zero_mul, add_zero] at h ⊢
    exact h


end SymmetricSexticResidual.LocalResidueU0

theorem solution :
    let A := 5 * SymmetricSexticResidual.K5Field.S_K - 9 * SymmetricSexticResidual.K5Field.Q_K
    let B := SymmetricSexticResidual.K5Field.T_K - 3
    let d_ab := 6 * SymmetricSexticResidual.K5Field.S_K * B
    let Q_quad := 11943020 * SymmetricSexticResidual.K5Field.S_K ^ 2 -
      876486 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.Q_K +
      8382500 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.T_K +
      5029500 * SymmetricSexticResidual.K5Field.Q_K * SymmetricSexticResidual.K5Field.T_K -
      14837025 * SymmetricSexticResidual.K5Field.S_K - 33647355 * SymmetricSexticResidual.K5Field.Q_K
    let a_du : QuadraticCovers.Dual SymmetricSexticResidual.K5Field.K5 :=
      QuadraticCovers.Dual.C d_ab⁻¹ * ⟨6 * SymmetricSexticResidual.K5Field.S_K ^ 2, 6 * SymmetricSexticResidual.K5Field.S_K * B⟩
    let b_du : QuadraticCovers.Dual SymmetricSexticResidual.K5Field.K5 :=
      QuadraticCovers.Dual.C d_ab⁻¹ * ⟨6 * SymmetricSexticResidual.K5Field.S_K * SymmetricSexticResidual.K5Field.Q_K,
        (5 * SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) * B⟩
    QuadraticCovers.Dual.C (d_ab ^ 3) *
      SymmetricSexticResidual.LocalResidueU0.A0U_12_of QuadraticCovers.Dual.C a_du b_du =
      ⟨(8248380 / 51331077 : SymmetricSexticResidual.K5Field.K5) *
        (5 * SymmetricSexticResidual.K5Field.S_K - 3 * SymmetricSexticResidual.K5Field.Q_K) *
        SymmetricSexticResidual.K5Field.S_K ^ 3 * A ^ 2,
       -(2 / 51331077 : SymmetricSexticResidual.K5Field.K5) * B *
        SymmetricSexticResidual.K5Field.S_K ^ 2 * A ^ 2 * Q_quad⟩ :=
  SymmetricSexticResidual.LocalResidueU0.br2_0_A0U_Z2_eval
