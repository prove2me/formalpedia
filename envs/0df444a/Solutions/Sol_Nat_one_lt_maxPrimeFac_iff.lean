-- Prove2me | solution 1 for Nat.one_lt_maxPrimeFac_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:12:34.644174+00:00
-- url     : https://prove2.me/submissions/d24196b9-781e-4b13-9318-1b252c1bb3b7

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Theorems.Thm_Nat_maxPrimeFac_zero
public import Theorems.Thm_Nat_maxPrimeFac_one
public import Theorems.Thm_Nat_prime_maxPrimeFac_of_one_lt
public import Theorems.Thm_Nat_one_le_maxPrimeFac_iff
attribute [local simp] Nat.maxPrimeFac_zero
attribute [local simp] Nat.maxPrimeFac_one
attribute [local simp] Nat.one_le_maxPrimeFac_iff

set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}
namespace Nat
theorem _root_.solution : ∀ {n : ℕ}, 1 < maxPrimeFac n ↔ 1 < n := fun {n} =>
  match n with
  | 0 | 1 => by simp
  | n + 2 => by simpa using (prime_maxPrimeFac_of_one_lt <| by lia).one_lt
end Nat
