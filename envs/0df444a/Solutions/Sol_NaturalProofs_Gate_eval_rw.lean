-- Prove2me | solution 1 for NaturalProofs.Gate.eval_rw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:27:29.118368+00:00
-- url     : https://prove2.me/submissions/21d4f6d5-4959-4c28-a79d-3e3fc569abde

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
public import Theorems.Thm_NaturalProofs_Wire_eval_rw

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
namespace NaturalProofs
namespace Gate
theorem _root_.solution (x : β → Bool) (acc W : List Bool) (σ : α → Wire β)
    (hσ : ∀ a, (σ a).Local acc.length) (g : Gate α) :
    (g.rw acc.length σ).eval x (acc ++ W) = g.eval (fun a => (σ a).eval x acc) W := by
  cases g <;> simp [Gate.rw, Gate.eval, Wire.eval_rw x acc W σ hσ]
end Gate
end NaturalProofs
