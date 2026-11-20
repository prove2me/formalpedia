-- Prove2me | solution 1 for Nat.maxPrimeFac_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:13:42.021933+00:00
-- url     : https://prove2.me/submissions/b6fd0d68-5b16-4d72-a56a-2b451e963a48

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Theorems.Thm_Nat_maxPrimeFac_zero
public import Theorems.Thm_Nat_maxPrimeFac_one
public import Theorems.Thm_Nat_maxPrimeFac_le_iff
public import Theorems.Thm_Nat_one_le_maxPrimeFac_iff
public import Theorems.Thm_Nat_one_lt_maxPrimeFac_iff
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
theorem _root_.solution (hm : m ≠ 0) (hn : n ≠ 0) :
    maxPrimeFac (m * n) = max (maxPrimeFac m) (maxPrimeFac n) := by
  obtain rfl | hm : m = 1 ∨ 1 < m := by lia
  · simp
    lia
  obtain rfl | hn : n = 1 ∨ 1 < n := by lia
  · simp
    lia
  refine eq_of_forall_ge_iff fun c ↦ ?_
  simp +contextual [maxPrimeFac_le_iff, one_lt_mul'' hm hn, Nat.Prime.dvd_mul, or_imp,
    forall_and, *]
end Nat
