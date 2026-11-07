-- Prove2me | solution 1 for NaturalProofs.length_evalFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:34:28.7172+00:00
-- url     : https://prove2.me/submissions/d04fb9a5-7c49-47a4-8592-51a40d51ae7c

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
namespace NaturalProofs
theorem _root_.solution (x : α → Bool) (acc : List Bool) (gs : List (Gate α)) :
    (evalFrom x acc gs).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [evalFrom]
  | cons g gs ih =>
    simp only [evalFrom, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega
end NaturalProofs
