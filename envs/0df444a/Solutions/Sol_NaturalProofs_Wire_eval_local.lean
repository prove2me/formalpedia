-- Prove2me | solution 1 for NaturalProofs.Wire.eval_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:24:48.672691+00:00
-- url     : https://prove2.me/submissions/f4d45641-bacf-4a45-ab2f-c2b8569d9844

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
namespace NaturalProofs
namespace Wire
theorem _root_.solution (x : β → Bool) (acc W : List Bool) (w : Wire β)
    (h : w.Local acc.length) : w.eval x (acc ++ W) = w.eval x acc := by
  cases w with
  | gate j =>
    show (acc ++ W).getD j false = acc.getD j false
    exact List.getD_append _ _ _ _ h
  | _ => simp [Wire.eval]
end Wire
end NaturalProofs
