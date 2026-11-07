-- Prove2me | solution 1 for NaturalProofs.MCircuit.toCircuit_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:28:23.716648+00:00
-- url     : https://prove2.me/submissions/1d8adcab-e813-4329-8a6b-d44befc87458

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
theorem _root_.solution (C : MCircuit α γ) (c : γ) (x : α → Bool) :
    (C.toCircuit c).eval x = C.eval x c := rfl
end NaturalProofs.MCircuit
