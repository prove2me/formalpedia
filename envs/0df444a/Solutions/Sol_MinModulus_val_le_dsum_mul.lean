-- Prove2me | solution 1 for MinModulus.val_le_dsum_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:33.060735+00:00
-- url     : https://prove2.me/submissions/07a17b34-8b64-435f-91d4-745aec36d6e4

module
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_MinModulusUniqueMultisetSum_UniqueSums

set_option autoImplicit true
@[expose] public section
public section
open MinModulus
open Finset
namespace MinModulus
theorem _root_.solution (n : ℕ) (k : ℕ → ℕ) :
    val n k ≤ dsum n k * 2 ^ (n - 1) := by
  unfold val dsum
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hin : i ≤ n - 1 := by have := Finset.mem_range.mp hi; omega
  exact Nat.mul_le_mul le_rfl (Nat.pow_le_pow_right (by norm_num) hin)
end MinModulus
