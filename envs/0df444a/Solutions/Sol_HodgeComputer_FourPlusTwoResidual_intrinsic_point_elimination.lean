-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.intrinsic_point_elimination
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T06:54:29.613375+00:00
-- url     : https://prove2.me/submissions/f109db52-c957-4ddd-8514-cc85c30d5fef

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem solution
    {K : Type*} [Field K]
    (L Q A0 A1 B0 B1 alpha : K)
    (hQV : Q * (Q * B0 - L * B1) ≠ 0) :
    let U := Q * A0 - L * A1
    let V := Q * B0 - L * B1
    let H := Q * U ^ 2 + L * V ^ 2
    let g1 := L + Q * alpha ^ 2
    let g2 := A0 + A1 * alpha ^ 2 + alpha * (B0 + B1 * alpha ^ 2)
    (g1 = 0 ∧ g2 = 0) ↔ (H = 0 ∧ alpha = -U / V) := by
  intro U V H g1 g2
  have hQ : Q ≠ 0 := left_ne_zero_of_mul hQV
  have hV : V ≠ 0 := right_ne_zero_of_mul hQV
  have id_lin : Q * g2 - (A1 + alpha * B1) * g1 = U + alpha * V := by
    dsimp only [g1, g2, U, V]
    ring
  have id_H : H = Q * (U + alpha * V) * (U - alpha * V) + g1 * V ^ 2 := by
    dsimp only [H, g1, U, V]
    ring
  constructor
  · rintro ⟨hg1, hg2⟩
    have hlin : U + alpha * V = 0 := by
      rw [← id_lin, hg1, hg2]
      ring
    have hH : H = 0 := by
      rw [id_H, hg1, hlin]
      ring
    have hal : alpha = -U / V := by
      apply (eq_div_iff hV).mpr
      linear_combination hlin
    exact ⟨hH, hal⟩
  · rintro ⟨hH, rfl⟩
    have hlin : U + (-U / V) * V = 0 := by
      field_simp [hV]
      ring
    have hg1 : g1 = 0 := by
      have hg1V : g1 * V ^ 2 = 0 := by
        have := id_H
        rw [hH, hlin] at this
        linear_combination -this
      exact (mul_eq_zero.mp hg1V).resolve_right (pow_ne_zero 2 hV)
    have hg2 : g2 = 0 := by
      have hQg2 : Q * g2 = 0 := by
        have := id_lin
        rw [hg1, hlin] at this
        linear_combination this
      exact (mul_eq_zero.mp hQg2).resolve_left hQ
    exact ⟨hg1, hg2⟩
