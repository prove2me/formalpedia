-- Prove2me | solution 1 for NaturalProofs.evalFrom_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:34:13.981311+00:00
-- url     : https://prove2.me/submissions/8d8bd7d1-8367-44f0-99d3-e6a642d6df36

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
namespace NaturalProofs
theorem _root_.solution (x : α → Bool) (acc : List Bool) (gs₁ gs₂ : List (Gate α)) :
    evalFrom x acc (gs₁ ++ gs₂) = evalFrom x (evalFrom x acc gs₁) gs₂ := by
  simp [evalFrom, List.foldl_append]
end NaturalProofs
