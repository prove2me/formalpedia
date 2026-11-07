-- Prove2me | solution 1 for NaturalProofs.MCircuit.mapIn_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:25:21.328005+00:00
-- url     : https://prove2.me/submissions/4a5b927e-f39c-4d76-bf34-7b3ddda29867

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
theorem _root_.solution (f : α → β) (C : MCircuit α γ) : (C.mapIn f).size = C.size := by
  simp [mapIn, size]
end NaturalProofs.MCircuit
