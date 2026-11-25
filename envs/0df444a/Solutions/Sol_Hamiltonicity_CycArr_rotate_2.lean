-- Prove2me | solution 2 for Hamiltonicity.CycArr.rotate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:48:42.470803+00:00
-- url     : https://prove2.me/submissions/e52a01e8-022a-4e20-9d24-3ec247496bc0

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_CyclicArrangement
public import Theorems.Thm_Hamiltonicity_CycArr_eq_iff

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
open Hamiltonicity.CycArr
variable {G : SimpleGraph V} {m : ℕ} {f : ℕ → V}
namespace Hamiltonicity.CycArr
theorem _root_.solution (h : CycArr G m f) (a : ℕ) : CycArr G m (fun i => f (a + i)) where
  three_le := h.three_le
  periodic i := by rw [← Nat.add_assoc, h.periodic]
  inj i j hi hj hij := by
    rw [h.eq_iff] at hij
    have := Nat.ModEq.add_left_cancel' a hij
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  adj i := h.adj (a + i)
end Hamiltonicity.CycArr
