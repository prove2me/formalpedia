-- Prove2me | solution 1 for Nat.le_maxPrimeFac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:11:36.966905+00:00
-- url     : https://prove2.me/submissions/e525c10b-d29f-4995-9083-55e83b27c3b3

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
theorem _root_.solution (hn : n ≠ 0) (hp : p.Prime) (h_dvd : p ∣ n) :
    p ≤ maxPrimeFac n := by
  have := (mem_primeFactorsList hn).2 ⟨hp, h_dvd⟩
  simpa [maxPrimeFac, List.getLast?_eq_getLast_of_ne_nil <| List.ne_nil_of_mem this]
    using (primeFactorsList_sorted n).pairwise.rel_getLast this
end Nat
