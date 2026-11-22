-- Prove2me | solution 1 for Lean4LPD.PauliString.oneLayer_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:58:47.253876+00:00
-- url     : https://prove2.me/submissions/8de80b29-6564-434b-9368-b9140eede4a1

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
theorem _root_.solution (p : PauliString n) : oneLayer [] p = {p} := rfl
end Lean4LPD.PauliString
