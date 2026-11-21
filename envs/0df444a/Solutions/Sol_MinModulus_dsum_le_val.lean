-- Prove2me | solution 1 for MinModulus.dsum_le_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:32.379889+00:00
-- url     : https://prove2.me/submissions/a9e4a1fb-492f-4238-92b6-e49a825e0069

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
theorem _root_.solution (n : ℕ) (k : ℕ → ℕ) : dsum n k ≤ val n k :=
  Finset.sum_le_sum fun i _ =>
    Nat.le_mul_of_pos_right (k i) (pow_pos (by norm_num) i)
end MinModulus
