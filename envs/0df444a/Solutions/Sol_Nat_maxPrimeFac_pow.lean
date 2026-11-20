-- Prove2me | solution 1 for Nat.maxPrimeFac_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:15:28.918878+00:00
-- url     : https://prove2.me/submissions/8b889a21-dd59-4b2d-af58-fa210414a1d7

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Theorems.Thm_Nat_maxPrimeFac_zero
public import Theorems.Thm_Nat_maxPrimeFac_one
public import Theorems.Thm_Nat_one_le_maxPrimeFac_iff
public import Theorems.Thm_Nat_one_lt_maxPrimeFac_iff
public import Theorems.Thm_Nat_maxPrimeFac_mul
attribute [local simp] Nat.maxPrimeFac_zero
attribute [local simp] Nat.maxPrimeFac_one
attribute [local simp] Nat.one_le_maxPrimeFac_iff
attribute [local simp] Nat.one_lt_maxPrimeFac_iff

set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}
namespace Nat
theorem _root_.solution : ∀ {k : ℕ}, k ≠ 0 → ∀ n, maxPrimeFac (n ^ k) = maxPrimeFac n := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro _ n
    by_cases hk : k = 0
    · subst k
      simp
    by_cases hn : n = 0
    · subst n
      simp
    rw [pow_succ, maxPrimeFac_mul (pow_ne_zero _ hn) hn, ih hk n, max_self]
end Nat
