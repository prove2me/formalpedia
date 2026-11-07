-- Prove2me | solution 1 for NaturalProofs.MCircuit.ofCircuit_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:35:20.963414+00:00
-- url     : https://prove2.me/submissions/3246ed63-455d-4adc-82b3-02764d778a95

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
theorem _root_.solution (C : Circuit α) : (ofCircuit C).size = C.size := rfl
end NaturalProofs.MCircuit
