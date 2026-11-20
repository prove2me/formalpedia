-- Prove2me | solution 1 for Nat.prime_maxPrimeFac_of_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:11:36.204159+00:00
-- url     : https://prove2.me/submissions/4e6e3e23-1e70-4d7b-a729-d2ab0c722939

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
theorem _root_.solution (h : 1 < n) : n.maxPrimeFac.Prime := by
  have : n.primeFactorsList ≠ [] := by simp; lia
  simpa [maxPrimeFac, List.getLast?_eq_getLast_of_ne_nil this]
    using prime_of_mem_primeFactorsList <| List.getLast_mem _
end Nat
