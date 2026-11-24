-- Prove2me | solution 1 for GlobalTheory.sum_vonMangoldt_div_nat_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:10.791467+00:00
-- url     : https://prove2.me/submissions/e635b399-b15c-4b81-98ea-01cee2720bb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LogFactorialEqSumVonMangoldtMulDiv
import Theorems.Thm_GlobalTheory_log_factorial_eq_sum_vonMangoldt_mul_div

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (N : ℕ) (hN : 1 ≤ N) :
    Real.log N - 1 ≤ ∑ n ∈ Ioc 0 N, Λ n / (n : ℝ) ∧
      ∑ n ∈ Ioc 0 N, Λ n / (n : ℝ) ≤ Real.log N + (Real.log 4 + 4) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hF := log_factorial_eq_sum_vonMangoldt_mul_div N
  have hfp : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  have hup : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
    rw [← Real.log_pow]
    exact Real.log_le_log hfp (by exact_mod_cast N.factorial_le_pow)
  have hlo : N * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
    have h1 := Real.pow_div_factorial_le_exp (N : ℝ) hN'.le N
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_exp, Real.log_div (by positivity) hfp.ne', Real.log_pow] at h2
    linarith
  have h1 : Real.log (N.factorial : ℝ) ≤ N * ∑ n ∈ Ioc 0 N, Λ n / (n : ℝ) := by
    rw [hF, Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    calc Λ n * ((N / n : ℕ) : ℝ) ≤ Λ n * ((N : ℝ) / n) :=
          mul_le_mul_of_nonneg_left Nat.cast_div_le vonMangoldt_nonneg
      _ = N * (Λ n / n) := by ring
  have h2 : N * ∑ n ∈ Ioc 0 N, Λ n / (n : ℝ) ≤
      Real.log (N.factorial : ℝ) + ∑ n ∈ Ioc 0 N, Λ n := by
    rw [hF, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hlt : (N : ℝ) / n ≤ ((N / n : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hn']
      have h := Nat.lt_div_mul_add (a := N) hn0
      have h' : (N : ℝ) < ((N / n : ℕ) : ℝ) * n + n := by exact_mod_cast h
      linarith
    calc (N : ℝ) * (Λ n / n) = Λ n * ((N : ℝ) / n) := by ring
      _ ≤ Λ n * (((N / n : ℕ) : ℝ) + 1) := mul_le_mul_of_nonneg_left hlt vonMangoldt_nonneg
      _ = _ := by ring
  have h3 : ∑ n ∈ Ioc 0 N, Λ n ≤ (Real.log 4 + 4) * N := by
    have h := Chebyshev.psi_le_const_mul_self hN'.le
    rwa [Chebyshev.psi, Nat.floor_natCast] at h
  constructor
  · refine le_of_mul_le_mul_left ?_ hN'
    nlinarith
  · refine le_of_mul_le_mul_left ?_ hN'
    nlinarith
end GlobalTheory
