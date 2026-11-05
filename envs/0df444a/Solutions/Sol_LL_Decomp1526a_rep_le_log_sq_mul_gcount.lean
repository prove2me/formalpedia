-- Prove2me | solution 1 for LL_Decomp1526a.rep_le_log_sq_mul_gcount
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:12.453208+00:00
-- url     : https://prove2.me/submissions/7718ddb1-f2de-4ccd-9711-66c217c5cc5c

import Mathlib
import Definitions.Def_LL_Decomp1526a_rep
import Definitions.Def_LL_Decomp1526a_gcount

open Finset Real
open scoped Chebyshev Classical

theorem solution (N : ℕ) :
    LL_Decomp1526a.rep N ≤ Real.log N ^ 2 * LL_Decomp1526a.gcount N := by
  unfold LL_Decomp1526a.rep LL_Decomp1526a.gcount
  rw [← sum_filter, filter_filter]
  have : ∀ p ∈ (range (N + 1)).filter (fun p => p.Prime ∧ (N - p).Prime),
      Real.log p * Real.log ((N - p : ℕ) : ℝ) ≤ Real.log N ^ 2 := by
    intro p hp
    simp only [mem_filter, mem_range] at hp
    obtain ⟨hpN, hp, hq⟩ := hp
    have h1 : Real.log p ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast (by omega : p ≤ N))
    have h2 : Real.log ((N - p : ℕ) : ℝ) ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast hq.pos) (by exact_mod_cast (by omega : N - p ≤ N))
    have h3 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    have h4 : 0 ≤ Real.log ((N - p : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hq.one_lt.le)
    nlinarith
  calc _ ≤ ∑ p ∈ (range (N + 1)).filter (fun p => p.Prime ∧ (N - p).Prime), Real.log N ^ 2 :=
        sum_le_sum this
    _ = _ := by rw [sum_const, nsmul_eq_mul, mul_comm]
