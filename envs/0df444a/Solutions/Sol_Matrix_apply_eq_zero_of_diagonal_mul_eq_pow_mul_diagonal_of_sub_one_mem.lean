-- Prove2me | solution 1 for Matrix.apply_eq_zero_of_diagonal_mul_eq_pow_mul_diagonal_of_sub_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/39c9d25f-d524-50b6-8975-281a30fb4af1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_apply_eq_zero_of_diagonal_mul_eq_pow_mul_diagonal_of_sub_one_mem

set_option autoImplicit false

universe u

open IsLocalRing

theorem solution {A : Type u} [CommRing A] [IsLocalRing A]
    (hH : ∀ x : A, (∀ n : ℕ, x ∈ IsLocalRing.maximalIdeal A ^ n) → x = 0)
    {a d : A} {q : ℕ} (had : IsUnit (a - (q : A) * d)) (hda : IsUnit (d - (q : A) * a))
    {N : Matrix (Fin 2) (Fin 2) A} (hN : ∀ i j, N i j - (1 : Matrix (Fin 2) (Fin 2) A) i j ∈ IsLocalRing.maximalIdeal A)
    (hrel : Matrix.diagonal ![a, d] * N = N ^ q * Matrix.diagonal ![a, d]) :
    N 0 1 = 0 ∧ N 1 0 = 0 := by
  set 𝔪 := maximalIdeal A with h𝔪
  have h00 : N 0 0 - 1 ∈ 𝔪 := by simpa using hN 0 0
  have h11 : N 1 1 - 1 ∈ 𝔪 := by simpa using hN 1 1
  have h01m : N 0 1 ∈ 𝔪 := by simpa using hN 0 1
  have h10m : N 1 0 ∈ 𝔪 := by simpa using hN 1 0

  have hmul : ∀ (n : ℕ) (x y : A), x ∈ 𝔪 → y ∈ 𝔪 ^ n → x * y ∈ 𝔪 ^ (n + 1) := fun n x y hx hy => by
    rw [pow_succ']; exact Ideal.mul_mem_mul hx hy

  have step : ∀ n : ℕ, N 0 1 ∈ 𝔪 ^ n → N 1 0 ∈ 𝔪 ^ n → N 0 1 ∈ 𝔪 ^ (n + 1) ∧ N 1 0 ∈ 𝔪 ^ (n + 1) := by
    intro n h01 h10

    have hpow : ∀ j : ℕ, ((N ^ j) 0 0 - 1 ∈ 𝔪 ∧ (N ^ j) 1 1 - 1 ∈ 𝔪) ∧
        ((N ^ j) 0 1 - (j : A) * N 0 1 ∈ 𝔪 ^ (n + 1) ∧ (N ^ j) 1 0 - (j : A) * N 1 0 ∈ 𝔪 ^ (n + 1)) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        obtain ⟨⟨i00, i11⟩, i01, i10⟩ := ih
        have e00 : (N ^ (j + 1)) 0 0 = (N ^ j) 0 0 * N 0 0 + (N ^ j) 0 1 * N 1 0 := by
          rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
        have e11 : (N ^ (j + 1)) 1 1 = (N ^ j) 1 0 * N 0 1 + (N ^ j) 1 1 * N 1 1 := by
          rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
        have e01 : (N ^ (j + 1)) 0 1 = (N ^ j) 0 0 * N 0 1 + (N ^ j) 0 1 * N 1 1 := by
          rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
        have e10 : (N ^ (j + 1)) 1 0 = (N ^ j) 1 0 * N 0 0 + (N ^ j) 1 1 * N 1 0 := by
          rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

        have j01 : (N ^ j) 0 1 ∈ 𝔪 ^ n := by
          have : (N ^ j) 0 1 = ((N ^ j) 0 1 - (j : A) * N 0 1) + (j : A) * N 0 1 := by ring
          rw [this]
          exact Ideal.add_mem _ (Ideal.pow_le_pow_right (Nat.le_succ n) i01) (Ideal.mul_mem_left _ _ h01)
        have j10 : (N ^ j) 1 0 ∈ 𝔪 ^ n := by
          have : (N ^ j) 1 0 = ((N ^ j) 1 0 - (j : A) * N 1 0) + (j : A) * N 1 0 := by ring
          rw [this]
          exact Ideal.add_mem _ (Ideal.pow_le_pow_right (Nat.le_succ n) i10) (Ideal.mul_mem_left _ _ h10)
        have j01m : (N ^ j) 0 1 ∈ 𝔪 := by
          have : (N ^ j) 0 1 = ((N ^ j) 0 1 - (j : A) * N 0 1) + (j : A) * N 0 1 := by ring
          rw [this]
          exact Ideal.add_mem _ (Ideal.pow_le_self (Nat.succ_ne_zero n) i01) (Ideal.mul_mem_left _ _ h01m)
        have j10m : (N ^ j) 1 0 ∈ 𝔪 := by
          have : (N ^ j) 1 0 = ((N ^ j) 1 0 - (j : A) * N 1 0) + (j : A) * N 1 0 := by ring
          rw [this]
          exact Ideal.add_mem _ (Ideal.pow_le_self (Nat.succ_ne_zero n) i10) (Ideal.mul_mem_left _ _ h10m)
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
        ·
          have : (N ^ (j + 1)) 0 0 - 1
              = ((N ^ j) 0 0 - 1) * N 0 0 + (N 0 0 - 1) + (N ^ j) 0 1 * N 1 0 := by rw [e00]; ring
          rw [this]
          exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ i00) h00) (Ideal.mul_mem_left _ _ h10m)
        · have : (N ^ (j + 1)) 1 1 - 1
              = (N ^ j) 1 0 * N 0 1 + (((N ^ j) 1 1 - 1) * N 1 1 + (N 1 1 - 1)) := by rw [e11]; ring
          rw [this]
          exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h01m) (Ideal.add_mem _ (Ideal.mul_mem_right _ _ i11) h11)
        ·
          have : (N ^ (j + 1)) 0 1 - ((j + 1 : ℕ) : A) * N 0 1
              = ((N ^ j) 0 0 - 1) * N 0 1 + ((N ^ j) 0 1 - (j : A) * N 0 1) * N 1 1
                + ((j : A) * N 0 1) * (N 1 1 - 1) := by rw [e01]; push_cast; ring
          rw [this]
          refine Ideal.add_mem _ (Ideal.add_mem _ (hmul n _ _ i00 h01) (Ideal.mul_mem_right _ _ i01)) ?_
          rw [mul_comm]
          exact hmul n _ _ (h11) (Ideal.mul_mem_left _ _ h01)
        · have : (N ^ (j + 1)) 1 0 - ((j + 1 : ℕ) : A) * N 1 0
              = ((N ^ j) 1 0 - (j : A) * N 1 0) * N 0 0 + ((j : A) * N 1 0) * (N 0 0 - 1)
                + ((N ^ j) 1 1 - 1) * N 1 0 := by rw [e10]; push_cast; ring
          rw [this]
          refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ i10) ?_) (hmul n _ _ i11 h10)
          rw [mul_comm]
          exact hmul n _ _ h00 (Ideal.mul_mem_left _ _ h10)
    obtain ⟨-, q01, q10⟩ := hpow q

    have r01 : a * N 0 1 = (N ^ q) 0 1 * d := by
      have := congrFun (congrFun hrel 0) 1
      simpa [Matrix.diagonal_mul, Matrix.mul_diagonal] using this
    have r10 : d * N 1 0 = (N ^ q) 1 0 * a := by
      have := congrFun (congrFun hrel 1) 0
      simpa [Matrix.diagonal_mul, Matrix.mul_diagonal] using this
    constructor
    · have key : (a - (q : A) * d) * N 0 1 = ((N ^ q) 0 1 - (q : A) * N 0 1) * d := by
        rw [sub_mul, r01]; ring
      have hmem : (a - (q : A) * d) * N 0 1 ∈ 𝔪 ^ (n + 1) := by
        rw [key]; exact Ideal.mul_mem_right _ _ q01
      exact (Ideal.unit_mul_mem_iff_mem _ had).mp hmem
    · have key : (d - (q : A) * a) * N 1 0 = ((N ^ q) 1 0 - (q : A) * N 1 0) * a := by
        rw [sub_mul, r10]; ring
      have hmem : (d - (q : A) * a) * N 1 0 ∈ 𝔪 ^ (n + 1) := by
        rw [key]; exact Ideal.mul_mem_right _ _ q10
      exact (Ideal.unit_mul_mem_iff_mem _ hda).mp hmem

  have hall : ∀ n : ℕ, N 0 1 ∈ 𝔪 ^ n ∧ N 1 0 ∈ 𝔪 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => exact step n ih.1 ih.2
  exact ⟨hH _ fun n => (hall n).1, hH _ fun n => (hall n).2⟩

end S_Matrix_apply_eq_zero_of_diagonal_mul_eq_pow_mul_diagonal_of_sub_one_mem
end P2MW
export P2MW.S_Matrix_apply_eq_zero_of_diagonal_mul_eq_pow_mul_diagonal_of_sub_one_mem (solution)
