-- Prove2me | solution 1 for LL_Decomp1528a.vonMangoldt_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:25:30.349847+00:00
-- url     : https://prove2.me/submissions/bcd28dc7-a03c-4458-8335-307f06a907b9

import Mathlib

open Real Finset Chebyshev

namespace S218LM

lemma Icc_one_eq (n : ℕ) : Icc 1 n = Ioc 0 n := by ext; simp; omega

lemma log_factorial_eq (n : ℕ) :
    log (n.factorial : ℝ) =
      ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m * ((n / m : ℕ) : ℝ) := by
  rw [Icc_one_eq, ← ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum,
    ArithmeticFunction.vonMangoldt_mul_zeta]
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity),
      ih, Finset.sum_Ioc_succ_top (Nat.zero_le k), add_comm]
    simp [ArithmeticFunction.log_apply]

lemma mem_primesLE' {n p : ℕ} : p ∈ Nat.primesLE n ↔ p ≤ n ∧ p.Prime := by
  simp [Nat.primesLE, Nat.mem_primesBelow, Nat.lt_succ_iff]

lemma primesLE_sub (n : ℕ) : Nat.primesLE n ⊆ Icc 1 n := by
  intro p hp
  rw [mem_primesLE'] at hp
  exact mem_Icc.2 ⟨hp.2.one_lt.le, hp.1⟩

lemma div_le_floor_add_one (n m : ℕ) (hm : 0 < m) :
    (n : ℝ) / m ≤ ((n / m : ℕ) : ℝ) + 1 := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  rw [div_le_iff₀ hm']
  have h := Nat.div_add_mod n m
  have hlt := Nat.mod_lt n hm
  have : (n : ℝ) = m * ((n / m : ℕ) : ℝ) + ((n % m : ℕ) : ℝ) := by exact_mod_cast h.symm
  have : ((n % m : ℕ) : ℝ) ≤ m := by exact_mod_cast hlt.le
  nlinarith

lemma psi_nat (n : ℕ) : ψ (n : ℝ) = ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m := by
  rw [Chebyshev.psi, Nat.floor_natCast, Icc_one_eq]

end S218LM

theorem solution (n : ℕ) :
    (n : ℝ) * ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m / m ≤
      log (n.factorial : ℝ) + ψ n := by
  rw [S218LM.log_factorial_eq, S218LM.psi_nat, ← sum_add_distrib, mul_sum]
  apply sum_le_sum
  intro m hm
  have hm0 : 0 < m := (mem_Icc.1 hm).1
  have h := mul_le_mul_of_nonneg_left (S218LM.div_le_floor_add_one n m hm0)
    (ArithmeticFunction.vonMangoldt_nonneg (n := m))
  calc (n : ℝ) * (ArithmeticFunction.vonMangoldt m / m)
      = ArithmeticFunction.vonMangoldt m * ((n : ℝ) / m) := by ring
    _ ≤ ArithmeticFunction.vonMangoldt m * (((n / m : ℕ) : ℝ) + 1) := h
    _ = _ := by ring
