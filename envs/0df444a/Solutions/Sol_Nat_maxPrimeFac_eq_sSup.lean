-- Prove2me | solution 1 for Nat.maxPrimeFac_eq_sSup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:16:26.376866+00:00
-- url     : https://prove2.me/submissions/e91c67af-23f6-4d80-b327-8a1469d3b343

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Theorems.Thm_Nat_maxPrimeFac_zero
public import Theorems.Thm_Nat_maxPrimeFac_one
public import Theorems.Thm_Nat_isGreatest_maxPrimeFac
public import Theorems.Thm_Nat_isLUB_maxPrimeFac
public import Theorems.Thm_Nat_one_le_maxPrimeFac_iff
public import Theorems.Thm_Nat_one_lt_maxPrimeFac_iff
public import Theorems.Thm_Nat_maxPrimeFac_pow
public import Theorems.Thm_Nat_Prime_maxPrimeFac_eq_self
public import Theorems.Thm_Nat_maxPrimeFac_eq_self_iff
attribute [local simp] Nat.maxPrimeFac_zero
attribute [local simp] Nat.maxPrimeFac_one
attribute [local simp] Nat.one_le_maxPrimeFac_iff
attribute [local simp] Nat.one_lt_maxPrimeFac_iff
attribute [local simp] Nat.maxPrimeFac_pow
attribute [local simp] Nat.Prime.maxPrimeFac_eq_self
attribute [local simp] Nat.maxPrimeFac_eq_self_iff

set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}
namespace Nat
theorem _root_.solution (hn_one : n ≠ 1) :
    maxPrimeFac n = sSup {p : ℕ | p.Prime ∧ p ∣ n} := by
  obtain rfl | hn : n = 0 ∨ 1 < n := by lia
  · simpa using (Set.Infinite.Nat.sSup_eq_zero infinite_setOfPred_prime).symm
  · exact ((isLUB_maxPrimeFac hn).csSup_eq ⟨_, (isGreatest_maxPrimeFac hn).1⟩).symm
end Nat
