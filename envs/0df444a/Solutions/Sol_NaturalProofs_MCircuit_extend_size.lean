-- Prove2me | solution 1 for NaturalProofs.MCircuit.extend_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:25:24.059193+00:00
-- url     : https://prove2.me/submissions/f607850c-9d9c-40e6-b095-1100526f2b29

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
theorem _root_.solution (E : MCircuit β α) (C : MCircuit (β ⊕ α) γ) :
    (extend E C).size = E.size + C.size := by
  simp [extend, size]
end NaturalProofs.MCircuit
