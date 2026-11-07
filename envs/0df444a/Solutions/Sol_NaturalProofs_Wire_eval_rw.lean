-- Prove2me | solution 1 for NaturalProofs.Wire.eval_rw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:26:06.285203+00:00
-- url     : https://prove2.me/submissions/418fa931-4bbf-4769-a8c4-d4ecee8397e1

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
public import Theorems.Thm_NaturalProofs_Wire_eval_local

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
namespace NaturalProofs
namespace Wire
theorem _root_.solution (x : β → Bool) (acc W : List Bool) (σ : α → Wire β)
    (hσ : ∀ a, (σ a).Local acc.length) (w : Wire α) :
    (w.rw acc.length σ).eval x (acc ++ W) = w.eval (fun a => (σ a).eval x acc) W := by
  cases w with
  | input a =>
    simp only [Wire.rw]
    exact Wire.eval_local _ _ _ _ (hσ a)
  | const b => simp [Wire.rw, Wire.eval]
  | gate i =>
    simp only [Wire.rw, Wire.eval]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp
end Wire
end NaturalProofs
