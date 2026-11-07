-- Prove2me | solution 1 for NaturalProofs.MCircuit.wires_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:30:40.087449+00:00
-- url     : https://prove2.me/submissions/f1cfd5b2-5fc5-4545-9452-0aa5725edff2

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit
namespace NaturalProofs.MCircuit
theorem _root_.solution (w : γ → Wire α) : (wires w).size = 0 := rfl
end NaturalProofs.MCircuit
