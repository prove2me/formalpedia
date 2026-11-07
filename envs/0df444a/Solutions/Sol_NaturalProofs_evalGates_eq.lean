-- Prove2me | solution 1 for NaturalProofs.evalGates_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:23:29.40539+00:00
-- url     : https://prove2.me/submissions/9d11e8e2-8204-4a75-8bbe-d6dfc82f1e49

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
namespace NaturalProofs
theorem _root_.solution (x : α → Bool) (gs : List (Gate α)) :
    evalGates x gs = evalFrom x [] gs := rfl
end NaturalProofs
