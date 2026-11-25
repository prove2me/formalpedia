-- Prove2me | solution 1 for Hamiltonicity.CycArr.eq_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:16:41.909074+00:00
-- url     : https://prove2.me/submissions/406d211a-03a0-4b82-903b-7d70169c2592

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
theorem _root_.solution (h : CycArr G m f) {i j : ℕ} (hij : f i = f j) : f (i + 1) = f (j + 1) := by
  rw [h.eq_iff] at hij ⊢
  exact Nat.ModEq.add_right 1 hij
end Hamiltonicity.CycArr
