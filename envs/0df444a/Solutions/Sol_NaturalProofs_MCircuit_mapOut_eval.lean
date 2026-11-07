-- Prove2me | solution 1 for NaturalProofs.MCircuit.mapOut_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:24:52.958825+00:00
-- url     : https://prove2.me/submissions/9192dfec-af83-4f51-a4fc-ed0c442bdb90

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
theorem _root_.solution (g : δ → γ) (C : MCircuit α γ) (x : α → Bool) (c : δ) :
    (C.mapOut g).eval x c = C.eval x (g c) := rfl
end NaturalProofs.MCircuit
