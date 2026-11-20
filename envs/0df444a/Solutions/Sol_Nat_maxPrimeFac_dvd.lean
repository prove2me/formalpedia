-- Prove2me | solution 1 for Nat.maxPrimeFac_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:11:36.606242+00:00
-- url     : https://prove2.me/submissions/a8d37395-5aad-410e-9c15-be8c5782582a

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Theorems.Thm_Nat_maxPrimeFac_zero
public import Theorems.Thm_Nat_maxPrimeFac_one
attribute [local simp] Nat.maxPrimeFac_zero
attribute [local simp] Nat.maxPrimeFac_one

set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}
namespace Nat
theorem _root_.solution : ∀ {n : ℕ}, maxPrimeFac n ∣ n := fun {n} =>
  match n with
  | 0 | 1 => by simp
  | n + 2 => by
    have : (n + 2).primeFactorsList ≠ [] := by simp
    simpa [maxPrimeFac, List.getLast?_eq_getLast_of_ne_nil this]
      using dvd_of_mem_primeFactorsList <| List.getLast_mem _
end Nat
