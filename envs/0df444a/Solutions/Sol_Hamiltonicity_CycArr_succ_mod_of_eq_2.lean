-- Prove2me | solution 2 for Hamiltonicity.CycArr.succ_mod_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:45:43.469796+00:00
-- url     : https://prove2.me/submissions/1770559a-03cb-4668-9cd1-7384f384dd04

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
theorem _root_.solution {i : ℕ} (hc : i % m + 1 = m) : (i + 1) % m = 0 := by
  have h1 := Nat.mod_add_div i m
  have : i + 1 = m * (i / m + 1) := by rw [Nat.mul_succ]; omega
  rw [this, Nat.mul_mod_right]
end Hamiltonicity.CycArr
