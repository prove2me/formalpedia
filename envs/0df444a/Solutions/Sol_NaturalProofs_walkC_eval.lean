-- Prove2me | solution 1 for NaturalProofs.walkC_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:47:37.540701+00:00
-- url     : https://prove2.me/submissions/01953902-bbd0-49ec-a772-0820c966bea7

module
public import Definitions.Def_NaturalProofs_Circuits
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_GGM
public import Theorems.Thm_NaturalProofs_stepC_eval

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open MCircuit
variable (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)
variable {β : Type} (gc : (k : ℕ) → Fin (2 * k) → Circuit (Fin k))
namespace NaturalProofs
theorem _root_.solution (hgc : ∀ k j x, (gc k j).eval x = G k x j) {k : ℕ} (Cv : MCircuit β (Fin k))
    (ss : List (β ⊕ Bool)) (x : β → Bool) :
    (walkC gc Cv ss).eval x = walk G (Cv.eval x) (ss.map (bitval x)) := by
  induction ss generalizing Cv with
  | nil => rfl
  | cons s ss ih =>
    simp only [walkC, List.foldl_cons] at ih ⊢
    rw [ih, stepC_eval G gc hgc]
    rfl
end NaturalProofs
