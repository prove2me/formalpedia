-- Prove2me | solution 1 for NaturalProofs.length_evalGates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:36:07.096963+00:00
-- url     : https://prove2.me/submissions/5d4a1a1e-8dce-4f99-8c90-29cec255be9e

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
public import Theorems.Thm_NaturalProofs_evalGates_eq
public import Theorems.Thm_NaturalProofs_length_evalFrom

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
namespace NaturalProofs
theorem _root_.solution (x : α → Bool) (gs : List (Gate α)) :
    (evalGates x gs).length = gs.length := by
  simp [evalGates_eq, length_evalFrom]
end NaturalProofs
