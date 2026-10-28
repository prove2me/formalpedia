-- Prove2me | solution 1 for LL_Decomp1528a.sum_sub_theta_le_log_factorial
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:25:43.972263+00:00
-- url     : https://prove2.me/submissions/c158eb3b-4f8b-4d9a-9d42-52b653cd1d4a

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
    (n : ℝ) * ∑ p ∈ Nat.primesLE n, log p / p - θ n ≤ log (n.factorial : ℝ) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, mul_sum, ← sum_sub_distrib, S218LM.log_factorial_eq]
  calc ∑ p ∈ Nat.primesLE n, ((n:ℝ) * (log p / p) - log p)
      ≤ ∑ p ∈ Nat.primesLE n, ArithmeticFunction.vonMangoldt p * ((n / p : ℕ) : ℝ) := by
        apply sum_le_sum
        intro p hp
        have hpp := (S218LM.mem_primesLE'.1 hp).2
        rw [ArithmeticFunction.vonMangoldt_apply_prime hpp]
        have := S218LM.div_le_floor_add_one n p hpp.pos
        have hl : 0 ≤ log (p:ℝ) := Real.log_natCast_nonneg p
        have : (n:ℝ) * (log p / p) = log p * ((n:ℝ) / p) := by ring
        rw [this]; nlinarith
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (S218LM.primesLE_sub n)
        (fun _ _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))
