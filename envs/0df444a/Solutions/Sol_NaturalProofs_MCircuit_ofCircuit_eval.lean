-- Prove2me | solution 1 for NaturalProofs.MCircuit.ofCircuit_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:28:43.084589+00:00
-- url     : https://prove2.me/submissions/f65e6271-402a-4f3f-bd5d-9357aa221011

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
theorem _root_.solution (C : Circuit α) (x : α → Bool) (u : Unit) :
    (ofCircuit C).eval x u = C.eval x := rfl
end NaturalProofs.MCircuit
