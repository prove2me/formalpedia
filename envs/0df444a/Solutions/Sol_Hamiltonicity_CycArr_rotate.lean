-- Prove2me | solution 1 for Hamiltonicity.CycArr.rotate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:16:30.690111+00:00
-- url     : https://prove2.me/submissions/8882ffcd-795b-4f9d-a641-f957084a98c0

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
