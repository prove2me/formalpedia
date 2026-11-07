-- Prove2me | solution 1 for NaturalProofs.walkC_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:44:05.188604+00:00
-- url     : https://prove2.me/submissions/827d4fe2-e12a-4ea1-8357-a767476f293c

module
public import Definitions.Def_NaturalProofs_Circuits
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_GGM
public import Theorems.Thm_NaturalProofs_stepC_size

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open MCircuit
variable (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)
variable {β : Type} (gc : (k : ℕ) → Fin (2 * k) → Circuit (Fin k))
namespace NaturalProofs
theorem _root_.solution {k B : ℕ} (hB : ∀ j, (gc k j).size ≤ B) (Cv : MCircuit β (Fin k))
    (ss : List (β ⊕ Bool)) :
    (walkC gc Cv ss).size ≤ Cv.size + ss.length * (2 * k * B + 4 * k) := by
  induction ss generalizing Cv with
  | nil => simp [walkC]
  | cons s ss ih =>
    simp only [walkC, List.foldl_cons, List.length_cons] at ih ⊢
    have := ih (stepC gc s Cv)
    have := stepC_size gc hB s Cv
    nlinarith
end NaturalProofs
