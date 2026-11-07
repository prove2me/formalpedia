-- Prove2me | solution 1 for NaturalProofs.MCircuit.wires_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:35:41.783984+00:00
-- url     : https://prove2.me/submissions/a6834dca-34b2-41b1-942e-29070ababb82

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
theorem _root_.solution (w : γ → Wire α) (x : α → Bool) (c : γ) :
    (wires w).eval x c = (w c).eval x [] := rfl
end NaturalProofs.MCircuit
