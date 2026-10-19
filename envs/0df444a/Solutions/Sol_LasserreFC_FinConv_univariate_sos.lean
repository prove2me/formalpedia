-- Prove2me | solution 1 for LasserreFC.FinConv.univariate_sos
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T08:04:00.935611+00:00
-- url     : https://prove2.me/submissions/4913c0f6-0ab3-492e-8897-baaedcab389e

import Mathlib
set_option autoImplicit false

open Polynomial

theorem isSumSq_C_nonneg (r : ℝ) (hr : 0 ≤ r) : IsSumSq (C r : ℝ[X]) := by
  have : (C r : ℝ[X]) = C (Real.sqrt r) * C (Real.sqrt r) := by
    rw [← C_mul, Real.mul_self_sqrt hr]
  rw [this]
  exact IsSumSq.mul_self _

theorem isSumSq_aux (n : ℕ) :
    IsSumSq (((X : ℝ[X]) ^ 2) ^ (n + 1) - ((n : ℝ[X]) + 1) * X ^ 2 + (n : ℝ[X])) := by
  induction n with
  | zero =>
    have : ((X : ℝ[X]) ^ 2) ^ (0 + 1) - (((0 : ℕ) : ℝ[X]) + 1) * X ^ 2 + ((0 : ℕ) : ℝ[X]) = 0 := by
      simp
    rw [this]; exact IsSumSq.zero
  | succ m ih =>
    have h : (((X : ℝ[X]) ^ 2) ^ (m + 1 + 1) - (((m + 1 : ℕ) : ℝ[X]) + 1) * X ^ 2
        + ((m + 1 : ℕ) : ℝ[X]))
        = (X * X) * (((X : ℝ[X]) ^ 2) ^ (m + 1) - ((m : ℝ[X]) + 1) * X ^ 2 + (m : ℝ[X]))
          + ((m : ℝ[X]) + 1) * (X ^ 2 - 1) ^ 2 := by
      push_cast; ring
    rw [h]
    refine IsSumSq.add ((IsSumSq.mul_self X).mul ih) ?_
    exact ((IsSumSq.natCast m).add IsSumSq.one).mul (by simpa [sq] using IsSumSq.mul_self (X ^ 2 - 1 : ℝ[X]))

theorem solution (e : ℕ) (he : 1 ≤ e) :
    ∃ c : ℝ, 0 < c ∧ IsSumSq (1 + X + C c * X ^ (2 * e) : ℝ[X]) := by
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by omega⟩
  refine ⟨1 / (2 * ((n : ℝ) + 1)), by positivity, ?_⟩
  set k : ℝ[X] := C (1 / (2 * ((n : ℝ) + 1))) with hkdef
  have hk : k * (2 * ((n : ℝ[X]) + 1)) = 1 := by
    have : (1 / (2 * ((n : ℝ) + 1))) * (2 * ((n : ℝ) + 1)) = 1 := by
      field_simp
    have e2 : (2 * ((n : ℝ[X]) + 1)) = C (2 * ((n : ℝ) + 1)) := by
      rw [map_mul, map_add, map_natCast, map_one, map_ofNat]
    rw [e2, hkdef, ← C_mul, this, C_1]
  have hkS : IsSumSq k := isSumSq_C_nonneg _ (by positivity)
  have h : (1 + X + k * X ^ (2 * (n + 1)) : ℝ[X])
      = k * (((X : ℝ[X]) ^ 2) ^ (n + 1) - ((n : ℝ[X]) + 1) * X ^ 2 + (n : ℝ[X]))
        + (k * ((n : ℝ[X]) + 1)) * (X + 1) ^ 2 + k := by
    rw [pow_mul]
    linear_combination (-(1 + X)) * hk
  rw [h]
  refine IsSumSq.add (IsSumSq.add (hkS.mul (isSumSq_aux n)) ?_) hkS
  exact (hkS.mul (IsSumSq.natCast n |>.add IsSumSq.one)).mul (by simpa [sq] using IsSumSq.mul_self (X + 1 : ℝ[X]))
