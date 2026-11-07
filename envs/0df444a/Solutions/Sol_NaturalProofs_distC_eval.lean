-- Prove2me | solution 1 for NaturalProofs.distC_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:49:45.483214+00:00
-- url     : https://prove2.me/submissions/6e70ed0f-b45f-464f-ac9f-31410e38942c

module
public import Definitions.Def_NaturalProofs_Circuits
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_GGM
public import Theorems.Thm_NaturalProofs_leafC_eval
public import Theorems.Thm_NaturalProofs_MCircuit_comp_eval
public import Theorems.Thm_NaturalProofs_MCircuit_ofCircuit_eval
public import Theorems.Thm_NaturalProofs_MCircuit_parAll_eval
public import Theorems.Thm_NaturalProofs_MCircuit_toCircuit_eval


set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open MCircuit
variable (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)
variable {β : Type} (gc : (k : ℕ) → Fin (2 * k) → Circuit (Fin k))
namespace NaturalProofs
theorem _root_.solution (hgc : ∀ k j x, (gc k j).eval x = G k x j) {k n : ℕ} (hk : 0 < k) (i : ℕ)
    (e : Fin i → Bool) (c : (Fin i → Bool) → Fin (2 * k) → Bool) (D : Circuit (Fin n → Bool))
    (y : Fin (2 * k) → Bool) :
    (distC gc hk i e c D).eval y = D.eval (hybF G (i + 1) (expand (Function.update c e y))) := by
  simp only [distC, toCircuit_eval, comp_eval, ofCircuit_eval]
  congr 1
  funext x
  rw [parAll_eval, leafC_eval G gc hgc]
end NaturalProofs
