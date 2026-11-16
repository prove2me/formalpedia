-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.intrinsic_point_elimination
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T05:49:05.769202+00:00
-- url     : https://prove2.me/submissions/935c6bfd-44d4-4ebc-92de-d9ca1eaa3fae

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem solution
    (L Q A0 A1 B0 B1 alpha Ld Qd A0d A1d B0d B1d : ℂ) :
    let U := Q * A0 - L * A1
    let V := Q * B0 - L * B1
    let H := Q * U ^ 2 + L * V ^ 2
    let g1 := L + Q * alpha ^ 2
    let g2 := A0 + A1 * alpha ^ 2 + alpha * (B0 + B1 * alpha ^ 2)
    let dtau_g1 := Ld + Qd * alpha ^ 2
    let dalpha_g1 := 2 * Q * alpha
    let dtau_g2 := A0d + A1d * alpha ^ 2 + alpha * (B0d + B1d * alpha ^ 2)
    let dalpha_g2 := 2 * A1 * alpha + B0 + 3 * B1 * alpha ^ 2
    let dtau_U := Qd * A0 + Q * A0d - Ld * A1 - L * A1d
    let dtau_V := Qd * B0 + Q * B0d - Ld * B1 - L * B1d
    let dtau_H := Qd * U ^ 2 + 2 * Q * U * dtau_U + Ld * V ^ 2 + 2 * L * V * dtau_V
    (Q * g2 - (A1 + alpha * B1) * g1 = U + alpha * V) ∧
    (H = Q * (U + alpha * V) * (U - alpha * V) + g1 * V ^ 2) ∧
    (Q ≠ 0 → V ≠ 0 →
      ((g1 = 0 ∧ g2 = 0) ↔ (H = 0 ∧ alpha = -U / V))) ∧
    (g1 = 0 → g2 = 0 →
      dtau_H = Q * V * (dtau_g1 * dalpha_g2 - dalpha_g1 * dtau_g2)) := by
  intro U V H g1 g2 dtau_g1 dalpha_g1 dtau_g2 dalpha_g2 dtau_U dtau_V dtau_H
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [U, V, g1, g2]; ring
  · dsimp only [U, V, H, g1]; ring
  · intro hQ hV
    constructor
    · rintro ⟨hg1, hg2⟩
      have hlin : U + alpha * V = 0 := by
        calc
          U + alpha * V = Q * g2 - (A1 + alpha * B1) * g1 := by dsimp only [U, V, g1, g2]; ring
          _ = 0 := by rw [hg1, hg2]; ring
      have hH : H = 0 := by
        calc
          H = Q * (U + alpha * V) * (U - alpha * V) + g1 * V ^ 2 := by
            dsimp only [U, V, H, g1]; ring
          _ = 0 := by rw [hlin, hg1]; ring
      refine ⟨hH, ?_⟩
      apply (eq_div_iff hV).mpr
      linear_combination hlin
    · rintro ⟨hH, halpha⟩
      have hlin : U + alpha * V = 0 := by
        rw [halpha]
        field_simp [hV]
        ring
      have hg1 : g1 = 0 := by
        have hid : H = Q * (U + alpha * V) * (U - alpha * V) + g1 * V ^ 2 := by
          dsimp only [U, V, H, g1]; ring
        rw [hH, hlin] at hid
        have hV2 : V ^ 2 ≠ 0 := pow_ne_zero 2 hV
        have hmul : g1 * V ^ 2 = 0 := by linear_combination -hid
        exact (mul_eq_zero.mp hmul).resolve_right hV2
      have hg2 : g2 = 0 := by
        have hid : Q * g2 - (A1 + alpha * B1) * g1 = U + alpha * V := by
          dsimp only [U, V, g1, g2]; ring
        rw [hg1, hlin] at hid
        have hmul : Q * g2 = 0 := by linear_combination hid
        exact (mul_eq_zero.mp hmul).resolve_left hQ
      exact ⟨hg1, hg2⟩
  · intro hg1 hg2
    have hL : L = -(Q * alpha ^ 2) := by
      dsimp only [g1] at hg1
      linear_combination hg1
    have hA0 : A0 = -A1 * alpha ^ 2 - alpha * (B0 + B1 * alpha ^ 2) := by
      dsimp only [g2] at hg2
      linear_combination hg2
    dsimp only [dtau_H, dtau_U, dtau_V, U, V, dtau_g1, dalpha_g1, dtau_g2, dalpha_g2]
    rw [hL, hA0]
    ring
