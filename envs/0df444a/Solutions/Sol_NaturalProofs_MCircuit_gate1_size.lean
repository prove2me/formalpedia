-- Prove2me | solution 1 for NaturalProofs.MCircuit.gate1_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:42:07.725633+00:00
-- url     : https://prove2.me/submissions/c320e127-e25c-4f30-873b-87c232f0ca07

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
theorem _root_.solution (g : Gate α) : (gate1 g).size = 1 := rfl
end NaturalProofs.MCircuit
