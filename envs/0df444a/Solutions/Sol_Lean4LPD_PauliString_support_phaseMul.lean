-- Prove2me | solution 1 for Lean4LPD.PauliString.support_phaseMul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:58:41.180486+00:00
-- url     : https://prove2.me/submissions/cf12a73e-2d34-4614-a87c-3f3b7def7249

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
theorem _root_.solution (k : ZMod 4) (s : PauliString n) :
    support (phaseMul k s) = support s := rfl
end Lean4LPD.PauliString
