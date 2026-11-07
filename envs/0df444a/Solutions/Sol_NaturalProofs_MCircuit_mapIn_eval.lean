-- Prove2me | solution 1 for NaturalProofs.MCircuit.mapIn_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:30:01.483264+00:00
-- url     : https://prove2.me/submissions/e0d92959-6223-4538-8f35-845a08e2a784

module
public import Definitions.Def_NaturalProofs_Defs
public import Definitions.Def_NaturalProofs_Circuits
public import Theorems.Thm_NaturalProofs_evalGates_eq
public import Theorems.Thm_NaturalProofs_Wire_eval_rw
public import Theorems.Thm_NaturalProofs_Gate_eval_rw
public import Theorems.Thm_NaturalProofs_evalFrom_rw

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
variable {α β γ δ : Type}
open NaturalProofs.MCircuit
namespace NaturalProofs.MCircuit
theorem _root_.solution (f : α → β) (C : MCircuit α γ) (x : β → Bool) (c : γ) :
    (C.mapIn f).eval x c = C.eval (x ∘ f) c := by
  have hσ : ∀ a, (Wire.input (f a) : Wire β).Local ([] : List Bool).length :=
    fun _ => trivial
  have h := evalFrom_rw x [] [] (fun a => .input (f a)) hσ C.gates
  simp only [List.nil_append, List.length_nil] at h
  simp only [eval, mapIn, evalGates_eq]
  rw [h]
  have := Wire.eval_rw x [] (evalFrom (fun a => (Wire.input (f a) : Wire β).eval x []) [] C.gates)
    (fun a => .input (f a)) hσ (C.out c)
  simp only [List.nil_append, List.length_nil] at this
  rw [this]
  rfl
end NaturalProofs.MCircuit
