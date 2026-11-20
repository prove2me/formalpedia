-- Prove2me | solution 1 for Nat.maxPrimeFac_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:10:25.781951+00:00
-- url     : https://prove2.me/submissions/4a06469c-5112-425c-8564-0fd498a5a8b1

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac

set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}
namespace Nat
theorem _root_.solution : maxPrimeFac 0 = 0 := by simp [maxPrimeFac]
end Nat
