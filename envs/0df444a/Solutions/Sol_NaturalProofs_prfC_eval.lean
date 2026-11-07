-- Prove2me | solution 1 for NaturalProofs.prfC_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:48:41.273914+00:00
-- url     : https://prove2.me/submissions/2cadf2e7-9595-4743-b3b9-3d125a3bd35a

module
public import Definitions.Def_NaturalProofs_Circuits
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_GGM
public import Theorems.Thm_NaturalProofs_walkC_eval
public import Theorems.Thm_NaturalProofs_MCircuit_mapOut_eval
public import Theorems.Thm_NaturalProofs_MCircuit_toCircuit_eval


set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open MCircuit
variable (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)
variable {β : Type} (gc : (k : ℕ) → Fin (2 * k) → Circuit (Fin k))
namespace NaturalProofs
theorem _root_.solution (hgc : ∀ k j x, (gc k j).eval x = G k x j) {k : ℕ} (hk : 0 < k) (n : ℕ)
    (s : Bits k) : (prfC gc hk n s).eval = prf G k n s := by
  funext x
  simp only [prfC, toCircuit_eval, mapOut_eval, walkC_eval G gc hgc, prf, firstBit, hk,
    dite_true, List.map_map]
  congr 2
  rw [List.ofFn_eq_map]
  rfl
end NaturalProofs
