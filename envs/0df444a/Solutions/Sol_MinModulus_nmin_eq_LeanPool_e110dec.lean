-- Prove2me | solution 1 for MinModulus.nmin_eq_LeanPool_e110dec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:43:08.945801+00:00
-- url     : https://prove2.me/submissions/68517d90-e5c2-409c-b0b2-3b9cab6ab798

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
public import Theorems.Thm_MinModulus_theoremA

set_option autoImplicit true
@[expose] public section
public section
open MinModulus
open Finset
namespace MinModulus
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) :
    IsLeast {N | 2 ≤ N ∧ Valid n N} (2 ^ n - 2 ^ Nat.log 2 n) := by
  have hmn : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hnlt : n < 2 ^ n := Nat.lt_two_pow_self
  have hmlt : Nat.log 2 n < n := by
    by_contra hc
    push Not at hc
    have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hc
    omega
  have hple : 2 ^ Nat.log 2 n ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h2p : 2 ≤ 2 ^ (n - 1) := by
    have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 1 ≤ n - 1)
    simpa using h
  constructor
  · exact ⟨by omega, theoremA hn⟩
  · rintro N ⟨hN2, hNv⟩
    by_contra hc
    push Not at hc
    exact theoremB_LeanPool_e110dec hn hN2 hc hNv
end MinModulus
