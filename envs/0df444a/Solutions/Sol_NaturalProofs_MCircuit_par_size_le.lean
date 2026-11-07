-- Prove2me | solution 1 for NaturalProofs.MCircuit.par_size_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:36:48.916441+00:00
-- url     : https://prove2.me/submissions/be6d442c-1a99-43e0-8e45-765e3dec9791

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
public import Theorems.Thm_NaturalProofs_MCircuit_wires_size
public import Theorems.Thm_NaturalProofs_MCircuit_mapOut_size
public import Theorems.Thm_NaturalProofs_MCircuit_mapIn_size
public import Theorems.Thm_NaturalProofs_MCircuit_extend_size

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit
namespace NaturalProofs.MCircuit
theorem _root_.solution [DecidableEq α] (E : α → MCircuit β Unit) (l : List α) (B : ℕ)
    (hE : ∀ a, (E a).size ≤ B) : (par E l).size ≤ l.length * B := by
  induction l with
  | nil => simp [par, wires_size]
  | cons a l ih =>
    simp only [par, mapOut_size, extend_size, mapIn_size, List.length_cons]
    have := hE a
    nlinarith
end NaturalProofs.MCircuit
