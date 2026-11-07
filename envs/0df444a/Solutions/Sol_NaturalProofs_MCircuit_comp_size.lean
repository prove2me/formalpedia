-- Prove2me | solution 1 for NaturalProofs.MCircuit.comp_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:36:36.807774+00:00
-- url     : https://prove2.me/submissions/50ce33bf-5187-42dd-b23b-fb4d0719982c

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
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
theorem _root_.solution (C : MCircuit α γ) (E : MCircuit β α) :
    (C.comp E).size = E.size + C.size := by
  simp [comp, mapOut_size, extend_size, mapIn_size]
end NaturalProofs.MCircuit
