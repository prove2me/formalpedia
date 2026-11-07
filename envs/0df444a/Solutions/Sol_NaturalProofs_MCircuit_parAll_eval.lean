-- Prove2me | solution 1 for NaturalProofs.MCircuit.parAll_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:42:13.787564+00:00
-- url     : https://prove2.me/submissions/ef7a37d6-5245-48ff-bdc3-05e130a60925

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
public import Theorems.Thm_NaturalProofs_MCircuit_par_eval

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit
namespace NaturalProofs.MCircuit
theorem _root_.solution [Fintype α] [DecidableEq α] (E : α → MCircuit β Unit) (x : β → Bool)
    (b : α) : (parAll E).eval x b = (E b).eval x () :=
  par_eval E _ x b (by simp)
end NaturalProofs.MCircuit
