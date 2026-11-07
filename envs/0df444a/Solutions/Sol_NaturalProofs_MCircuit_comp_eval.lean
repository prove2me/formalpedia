-- Prove2me | solution 1 for NaturalProofs.MCircuit.comp_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:39:48.642741+00:00
-- url     : https://prove2.me/submissions/98149d9a-dd3b-49e8-a26e-1711eba4adbb

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
public import Theorems.Thm_NaturalProofs_MCircuit_mapOut_eval
public import Theorems.Thm_NaturalProofs_MCircuit_mapIn_eval
public import Theorems.Thm_NaturalProofs_MCircuit_extend_eval

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit
namespace NaturalProofs.MCircuit
theorem _root_.solution (C : MCircuit α γ) (E : MCircuit β α) (x : β → Bool) (c : γ) :
    (C.comp E).eval x c = C.eval (E.eval x) c := by
  simp only [comp, mapOut_eval, extend_eval, Sum.elim_inr, mapIn_eval]
  rfl
end NaturalProofs.MCircuit
