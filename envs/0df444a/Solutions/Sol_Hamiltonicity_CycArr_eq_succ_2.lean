-- Prove2me | solution 2 for Hamiltonicity.CycArr.eq_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:49:48.618442+00:00
-- url     : https://prove2.me/submissions/36a46021-ef48-4a5f-8441-d56e0c3ac258

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
