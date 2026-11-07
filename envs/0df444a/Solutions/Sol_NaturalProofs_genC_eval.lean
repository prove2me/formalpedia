-- Prove2me | solution 1 for NaturalProofs.genC_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:44:16.0215+00:00
-- url     : https://prove2.me/submissions/86d0b833-1062-4f9d-ae59-15f41d35e0ba

module
public import Definitions.Def_NaturalProofs_Circuits
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_GGM
public import Theorems.Thm_NaturalProofs_MCircuit_ofCircuit_eval
public import Theorems.Thm_NaturalProofs_MCircuit_parAll_eval


set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open MCircuit
variable (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)
variable {β : Type} (gc : (k : ℕ) → Fin (2 * k) → Circuit (Fin k))
namespace NaturalProofs
theorem _root_.solution (hgc : ∀ k j x, (gc k j).eval x = G k x j) (k : ℕ) (x : Fin k → Bool) :
    (genC gc k).eval x = G k x := by
  funext j
  simp [genC, parAll_eval, ofCircuit_eval, hgc]
end NaturalProofs
