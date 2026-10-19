-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.allocation_support_exponent_sum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T18:33:02.459741+00:00
-- url     : https://prove2.me/submissions/c5230acc-c9d5-4956-9670-c89a8e283cfb

import Mathlib.Tactic
import Definitions.Def_allocationSum

open scoped BigOperators

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) :
    (∑ i : {j : σ // e j ≠ 0}, e i.1) = ∑ i, e i := by
  classical
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (p := fun j : σ => e j ≠ 0) (f := e)
  have hzero : (∑ i : {j : σ // ¬ e j ≠ 0}, e i.1) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact not_not.mp i.2
  rw [hzero, add_zero] at hsplit
  exact hsplit