-- Prove2me | solution 1 for NaturalProofs.MCircuit.toCircuit_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:28:38.196303+00:00
-- url     : https://prove2.me/submissions/4ca09c35-78a0-4f75-8a2a-d18c98ee0f33

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
theorem _root_.solution (C : MCircuit α γ) (c : γ) : (C.toCircuit c).size = C.size := rfl
end NaturalProofs.MCircuit
