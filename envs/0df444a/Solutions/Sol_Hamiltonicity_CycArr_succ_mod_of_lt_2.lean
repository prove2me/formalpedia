-- Prove2me | solution 2 for Hamiltonicity.CycArr.succ_mod_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:45:39.282426+00:00
-- url     : https://prove2.me/submissions/7695b0c7-a7d3-481c-b75a-7711d2669a7b

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_CyclicArrangement

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
open Hamiltonicity.CycArr
variable {G : SimpleGraph V} {m : ℕ} {f : ℕ → V}
namespace Hamiltonicity.CycArr
theorem _root_.solution {i : ℕ} (hc : i % m + 1 < m) : (i + 1) % m = i % m + 1 := by
  have h1 := Nat.mod_add_div i m
  have : i + 1 = (i % m + 1) + m * (i / m) := by omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
end Hamiltonicity.CycArr
