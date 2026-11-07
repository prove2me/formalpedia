-- Prove2me | solution 1 for NaturalProofs.muxC_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:42:03.280627+00:00
-- url     : https://prove2.me/submissions/dc3ff5c8-cc31-48ff-a34a-10e6683b855c

module
public import Definitions.Def_NaturalProofs_Circuits
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_GGM

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open MCircuit
variable (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)
variable {β : Type} (gc : (k : ℕ) → Fin (2 * k) → Circuit (Fin k))
namespace NaturalProofs
theorem _root_.solution (k : ℕ) (s : β ⊕ Bool) (j : Fin k) (z : β ⊕ (Fin k ⊕ Fin (2 * k)) → Bool) :
    (muxC k s j).eval z () =
      if bitval (fun b => z (.inl b)) s then z (.inr (.inr ⟨k + j, by omega⟩))
      else z (.inr (.inr ⟨j, by omega⟩)) := by
  cases s with
  | inl b =>
    cases h : z (.inl b) <;>
      simp [muxC, MCircuit.eval, evalGates, Gate.eval, Wire.eval, bitval, h]
  | inr c =>
    cases c <;> simp [muxC, MCircuit.eval, evalGates, Gate.eval, Wire.eval, bitval]
end NaturalProofs
