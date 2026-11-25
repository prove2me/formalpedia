-- Prove2me | solution 1 for Hamiltonicity.CycArr.eq_mod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:13:46.445653+00:00
-- url     : https://prove2.me/submissions/0e3dc8b0-4773-4603-9185-6460505c2fee

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
theorem _root_.solution (h : CycArr G m f) (i : ℕ) : f i = f (i % m) := by
  conv_lhs => rw [← Nat.mod_add_div i m]
  induction i / m with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, ← Nat.add_assoc, h.periodic, ih]
end Hamiltonicity.CycArr
