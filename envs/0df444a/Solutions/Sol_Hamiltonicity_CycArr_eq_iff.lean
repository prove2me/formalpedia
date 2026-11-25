-- Prove2me | solution 1 for Hamiltonicity.CycArr.eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:15:21.310136+00:00
-- url     : https://prove2.me/submissions/cadccb4f-172d-469d-b0e3-0a85aaec5c10

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_CyclicArrangement
public import Theorems.Thm_Hamiltonicity_CycArr_pos
public import Theorems.Thm_Hamiltonicity_CycArr_eq_mod

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
open Hamiltonicity.CycArr
variable {G : SimpleGraph V} {m : ℕ} {f : ℕ → V}
namespace Hamiltonicity.CycArr
theorem _root_.solution (h : CycArr G m f) {i j : ℕ} : f i = f j ↔ i % m = j % m := by
  constructor
  · intro hij
    rw [h.eq_mod i, h.eq_mod j] at hij
    exact h.inj _ _ (Nat.mod_lt _ h.pos) (Nat.mod_lt _ h.pos) hij
  · intro hij
    rw [h.eq_mod i, h.eq_mod j, hij]
end Hamiltonicity.CycArr
