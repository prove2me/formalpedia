-- Prove2me | solution 1 for Nat.maxPrimeFac_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:11:02.880169+00:00
-- url     : https://prove2.me/submissions/cbe9d08e-6018-4a1d-9249-dd5605f2e39a

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Theorems.Thm_Nat_maxPrimeFac_zero
attribute [local simp] Nat.maxPrimeFac_zero

set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}
namespace Nat
theorem _root_.solution : maxPrimeFac 1 = 1 := by simp [maxPrimeFac]
end Nat
