-- Prove2me | solution 1 for IQPForrelation832.SingleQuery.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T05:23:37.376182+00:00
-- url     : https://prove2.me/submissions/65d97665-2cce-4d92-98e4-9e9fa88bd48b

import Definitions.Def_IQPForrelation832_SingleQuery_Programs

open IQPForrelation832.SingleQuery

theorem solution (n : ℕ) (x y : Cube n) :
    Q x + Q y + Q (x+y) = dot x y + (weight x : ZMod 2) * (weight y : ZMod 2) := by
  let B (v w : Cube n) : ZMod 2 :=
    ∑ i : Fin n, ∑ j : Fin n, if i < j then v i * w j else 0
  have polar : Q x + Q y + Q (x+y) = B x y + B y x := by
    simp only [Q, B, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i < j
    · simp only [h, if_true, Pi.add_apply, add_mul, mul_add]
      calc
        _ = (x i * x j + x i * x j) + (y i * y j + y i * y j) +
              (x i * y j + y i * x j) := by abel
        _ = _ := by simp [CharTwo.add_self_eq_zero]
    · simp [h]
  have swap : B y x = ∑ i : Fin n, ∑ j : Fin n, if j < i then x i * y j else 0 := by
    unfold B
    rw [Finset.sum_comm]
    simp_rw [mul_comm]
  have diag : dot x y = ∑ i : Fin n, ∑ j : Fin n, if i = j then x i * y j else 0 := by
    simp [dot, ExtremalForrelation.Nonadaptive.dot]
  have castWeight (v : Cube n) : (weight v : ZMod 2) = ∑ i, v i := by
    simp [weight, Nat.cast_sum]
  have prod : (∑ i, x i) * (∑ j, y j) = ∑ i, ∑ j, x i * y j := by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
  rw [polar, swap, diag, castWeight, castWeight, prod]
  simp only [B, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.ne, h.not_gt]
  · simp [CharTwo.add_self_eq_zero]
  · simp [h, h.ne', h.not_gt]
