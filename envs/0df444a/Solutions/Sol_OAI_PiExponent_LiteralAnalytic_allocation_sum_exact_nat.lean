-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.allocation_sum_exact_nat
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T18:14:10.756069+00:00
-- url     : https://prove2.me/submissions/a2895569-fd87-4762-beee-2c27fa979c5c

import Mathlib.Tactic
import Definitions.Def_allocationSum
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_allocation_sum_support_reduction
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_allocation_support_exponent_sum
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_allocation_sum_positive

open scoped BigOperators
open OAI.PiExponent.LiteralAnalytic

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) (k : ℕ) :
    (∑ n : σ → Fin (k + 1),
      (if ∑ i, (n i : ℕ) = k then
        ∏ i,
          (if e i = 0 then (if (n i : ℕ) = 0 then 1 else 0)
           else Nat.choose ((n i : ℕ) + e i - 1) (n i : ℕ))
       else 0)) =
      (if ∑ i, e i = 0 then (if k = 0 then 1 else 0)
       else Nat.choose (k + (∑ i, e i) - 1) k) := by
  change allocationSum e k = _
  rw [allocation_sum_support_reduction e k]
  have h := allocation_sum_positive
    (fun i : {j : σ // e j ≠ 0} => e i.1) k
    (fun i => Nat.pos_of_ne_zero i.2)
  simpa only [allocation_support_exponent_sum e] using h
