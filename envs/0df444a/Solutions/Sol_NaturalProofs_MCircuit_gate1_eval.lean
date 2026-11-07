-- Prove2me | solution 1 for NaturalProofs.MCircuit.gate1_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:42:07.165096+00:00
-- url     : https://prove2.me/submissions/4ff72fef-b4d6-4ed4-b723-6410791f6d4e

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
theorem _root_.solution (g : Gate α) (x : α → Bool) (u : Unit) :
    (gate1 g).eval x u = g.eval x [] := by
  simp [gate1, eval, evalGates, Wire.eval]
end NaturalProofs.MCircuit
