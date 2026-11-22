-- Prove2me | solution 1 for Lean4LPD.PauliString.subset_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:09:30.158207+00:00
-- url     : https://prove2.me/submissions/c08f949c-c734-43eb-abf8-35f6483acf38

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
theorem _root_.solution (L : List (PauliString n)) (S : Finset (Fin n)) : S ⊆ cover L S :=
  Finset.subset_union_left
end Lean4LPD.PauliString
