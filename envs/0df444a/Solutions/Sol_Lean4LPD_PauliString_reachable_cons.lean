-- Prove2me | solution 1 for Lean4LPD.PauliString.reachable_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:58:58.043808+00:00
-- url     : https://prove2.me/submissions/6102157a-5000-48e8-bec5-8f92667e6b2b

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}
namespace Lean4LPD.PauliString
theorem _root_.solution (L : List (PauliString n)) (Ls : List (List (PauliString n)))
    (p : PauliString n) :
    reachable (L :: Ls) p = (oneLayer L p).biUnion (reachable Ls) := rfl
end Lean4LPD.PauliString
