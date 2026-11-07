-- Prove2me | solution 1 for NaturalProofs.MCircuit.mapOut_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:25:06.554885+00:00
-- url     : https://prove2.me/submissions/5db73b23-1ad1-4d47-b9e2-15dd51fbf9c8

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
theorem _root_.solution (g : δ → γ) (C : MCircuit α γ) : (C.mapOut g).size = C.size := rfl
end NaturalProofs.MCircuit
