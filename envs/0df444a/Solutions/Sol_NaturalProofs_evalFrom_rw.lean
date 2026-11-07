-- Prove2me | solution 1 for NaturalProofs.evalFrom_rw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:28:45.655205+00:00
-- url     : https://prove2.me/submissions/dab269ff-1ab7-4bb9-87d1-fc275811e1bb

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
public import Theorems.Thm_NaturalProofs_Wire_eval_rw
public import Theorems.Thm_NaturalProofs_Gate_eval_rw

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
namespace NaturalProofs
theorem _root_.solution (x : β → Bool) (acc W : List Bool) (σ : α → Wire β)
    (hσ : ∀ a, (σ a).Local acc.length) (gs : List (Gate α)) :
    evalFrom x (acc ++ W) (gs.map (Gate.rw acc.length σ)) =
      acc ++ evalFrom (fun a => (σ a).eval x acc) W gs := by
  induction gs generalizing W with
  | nil => simp [evalFrom]
  | cons g gs ih =>
    simp only [List.map_cons, evalFrom, List.foldl_cons] at ih ⊢
    rw [Gate.eval_rw x acc W σ hσ, List.append_assoc, ih]
end NaturalProofs
