-- Prove2me | solution 1 for NaturalProofs.leafC_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:48:41.698602+00:00
-- url     : https://prove2.me/submissions/6d980108-33b8-4fd8-8944-8dcd5d54af27

module
public import Definitions.Def_NaturalProofs_Circuits
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_GGM
public import Theorems.Thm_NaturalProofs_expand_pre
public import Theorems.Thm_NaturalProofs_walkC_eval
public import Theorems.Thm_NaturalProofs_startC_eval
public import Theorems.Thm_NaturalProofs_MCircuit_mapOut_eval


set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open MCircuit
variable (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)
variable {β : Type} (gc : (k : ℕ) → Fin (2 * k) → Circuit (Fin k))
namespace NaturalProofs
theorem _root_.solution (hgc : ∀ k j x, (gc k j).eval x = G k x j) {k n : ℕ} (hk : 0 < k) (i : ℕ)
    (e : Fin i → Bool) (c : (Fin i → Bool) → Fin (2 * k) → Bool) (x : Fin n → Bool)
    (y : Fin (2 * k) → Bool) :
    (leafC gc hk i e c x).eval y () = hybF G (i + 1) (expand (Function.update c e y)) x := by
  simp only [leafC, mapOut_eval, walkC_eval G gc hgc, startC_eval, hybF, expand_pre,
    List.map_map, firstBit, hk, dite_true]
  congr 3
  conv_rhs => rw [← List.map_id ((List.ofFn x).drop (i + 1))]
  rfl
end NaturalProofs
