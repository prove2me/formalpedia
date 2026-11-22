-- Prove2me | solution 1 for Lean4LPD.PauliString.oneLayer_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:58:47.735078+00:00
-- url     : https://prove2.me/submissions/c76ebe4e-6b9e-460e-b451-c70e4b74dfe9

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
theorem _root_.solution (G : PauliString n) (Gs : List (PauliString n))
    (p : PauliString n) :
    oneLayer (G :: Gs) p = (branch G p).biUnion (oneLayer Gs) := rfl
end Lean4LPD.PauliString
