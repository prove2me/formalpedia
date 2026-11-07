-- Prove2me | solution 1 for NaturalProofs.expand_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:39:27.189533+00:00
-- url     : https://prove2.me/submissions/58c4a440-a211-46d4-9712-0e867e61e152

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
namespace NaturalProofs
theorem _root_.solution (k i : ℕ) :
    Function.Injective (expand : ((Fin i → Bool) → Fin (2 * k) → Bool) → _ → Bits k) := by
  intro M M' h
  funext p j
  by_cases hj : k ≤ (j : ℕ)
  · have := congrFun (congrFun h (Fin.snoc p true)) ⟨j - k, by omega⟩
    simp only [expand, Fin.init_snoc, Fin.snoc_last, half] at this
    convert this using 2 <;> exact Fin.ext (by simp; omega)
  · have := congrFun (congrFun h (Fin.snoc p false)) ⟨j, by omega⟩
    simp only [expand, Fin.init_snoc, Fin.snoc_last, half] at this
    convert this using 2 <;> exact Fin.ext (by simp)
end NaturalProofs
