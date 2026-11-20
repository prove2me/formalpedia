-- Prove2me | solution 1 for Nat.maxPrimeFac_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:13:08.443759+00:00
-- url     : https://prove2.me/submissions/7b3978ed-7dc4-4306-975e-8b4ed1cc5de6

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Theorems.Thm_Nat_maxPrimeFac_zero
public import Theorems.Thm_Nat_maxPrimeFac_one
public import Theorems.Thm_Nat_isLUB_maxPrimeFac
attribute [local simp] Nat.maxPrimeFac_zero
attribute [local simp] Nat.maxPrimeFac_one

set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}
namespace Nat
theorem _root_.solution (hn : 1 < n) :
    n.maxPrimeFac ≤ m ↔ ∀ p, p.Prime → p ∣ n → p ≤ m := by
  simp [isLUB_le_iff <| isLUB_maxPrimeFac hn, upperBounds]
end Nat
