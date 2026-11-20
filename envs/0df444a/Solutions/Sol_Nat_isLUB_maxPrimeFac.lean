-- Prove2me | solution 1 for Nat.isLUB_maxPrimeFac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:12:45.413923+00:00
-- url     : https://prove2.me/submissions/98b4f0bc-1cb0-405d-a4c4-5cbd92c68a05

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Theorems.Thm_Nat_isGreatest_maxPrimeFac

set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}
namespace Nat
theorem _root_.solution (hn : 1 < n) :
    IsLUB {p : ℕ | p.Prime ∧ p ∣ n} (maxPrimeFac n) :=
  (isGreatest_maxPrimeFac hn).isLUB
end Nat
