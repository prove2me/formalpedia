-- Prove2me | solution 1 for Nat.maxPrimeFac_eq_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:15:52.089474+00:00
-- url     : https://prove2.me/submissions/b363ba33-b8eb-449c-ae4b-595109e806ce

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Theorems.Thm_Nat_maxPrimeFac_zero
public import Theorems.Thm_Nat_maxPrimeFac_one
public import Theorems.Thm_Nat_prime_maxPrimeFac_of_one_lt
public import Theorems.Thm_Nat_one_le_maxPrimeFac_iff
public import Theorems.Thm_Nat_one_lt_maxPrimeFac_iff
public import Theorems.Thm_Nat_maxPrimeFac_pow
public import Theorems.Thm_Nat_Prime_maxPrimeFac_eq_self
attribute [local simp] Nat.maxPrimeFac_zero
attribute [local simp] Nat.maxPrimeFac_one
attribute [local simp] Nat.one_le_maxPrimeFac_iff
attribute [local simp] Nat.one_lt_maxPrimeFac_iff
attribute [local simp] Nat.maxPrimeFac_pow
attribute [local simp] Nat.Prime.maxPrimeFac_eq_self

set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}
namespace Nat
theorem _root_.solution : maxPrimeFac n = n ↔ n ≤ 1 ∨ n.Prime where
  mp h := by
    by_cases hn : n ≤ 1
    · exact Or.inl hn
    · exact Or.inr <| h ▸ prime_maxPrimeFac_of_one_lt (lt_of_not_ge hn)
  mpr := by
    rintro (hn | hn)
    · obtain rfl | rfl : n = 0 ∨ n = 1 := by lia
      all_goals simp
    · exact hn.maxPrimeFac_eq_self
end Nat
