-- Prove2me | solution 1 for Kyprianou.Ch01.branchingMechanismExpLaplaceIdentity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:26:21.762676+00:00
-- url     : https://prove2.me/submissions/ce4b2247-bfbe-4dba-8dff-e00c16218968

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    (offspring : PMF ℕ) (q : ℝ) (hq : 0 < q) :
    (∑' k : ℕ,
      (offspring k).toReal *
        (1 - Real.exp (-q * ((k : ℝ) - 1)))) =
      1 - Real.exp q *
        (∑' k : ℕ,
          (offspring k).toReal * Real.exp (-q * (k : ℝ))) := by
  have hs : Summable (fun k => (offspring k).toReal) :=
    ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)
  have h1 : ∑' k, (offspring k).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun k => PMF.apply_ne_top offspring k), PMF.tsum_coe]; simp
  have hs2 : Summable (fun k : ℕ => (offspring k).toReal * Real.exp (-q * (k : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hs
    have : Real.exp (-q * (k : ℝ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have : (0:ℝ) ≤ k := k.cast_nonneg; nlinarith
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg this
  have heq : ∀ k : ℕ, (offspring k).toReal * (1 - Real.exp (-q * ((k : ℝ) - 1))) =
      (offspring k).toReal - Real.exp q * ((offspring k).toReal * Real.exp (-q * (k : ℝ))) := by
    intro k
    have : Real.exp (-q * ((k : ℝ) - 1)) = Real.exp q * Real.exp (-q * (k : ℝ)) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; ring
  simp_rw [heq]
  rw [hs.tsum_sub (hs2.mul_left _), tsum_mul_left, h1]
