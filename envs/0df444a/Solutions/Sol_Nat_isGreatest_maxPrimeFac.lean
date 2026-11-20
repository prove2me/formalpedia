-- Prove2me | solution 1 for Nat.isGreatest_maxPrimeFac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:12:11.633541+00:00
-- url     : https://prove2.me/submissions/83440339-6216-4754-afb9-c0cd41d47fe9

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Theorems.Thm_Nat_prime_maxPrimeFac_of_one_lt
public import Theorems.Thm_Nat_maxPrimeFac_dvd
public import Theorems.Thm_Nat_le_maxPrimeFac

set_option autoImplicit true
@[expose] public section
public section
open Nat
variable {m n p : ℕ}
namespace Nat
theorem _root_.solution (hn : 1 < n) :
    IsGreatest {p : ℕ | p.Prime ∧ p ∣ n} (maxPrimeFac n) :=
  ⟨⟨prime_maxPrimeFac_of_one_lt hn, maxPrimeFac_dvd⟩,
    fun _ hp => le_maxPrimeFac (zero_lt_of_lt hn).ne' hp.1 hp.2⟩
end Nat
