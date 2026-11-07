-- Prove2me | solution 1 for NaturalProofs.Wire.local_san
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:34:42.343199+00:00
-- url     : https://prove2.me/submissions/8a280e88-d5b8-4495-9dc7-fcc64828b7dc

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
theorem _root_.solution (n : ℕ) (w : Wire β) : (w.san n).Local n := by
  cases w with
  | gate j => by_cases h : j < n <;> simp [Wire.san, Wire.Local, h]
  | _ => simp [Wire.san, Wire.Local]
end Wire
end NaturalProofs
