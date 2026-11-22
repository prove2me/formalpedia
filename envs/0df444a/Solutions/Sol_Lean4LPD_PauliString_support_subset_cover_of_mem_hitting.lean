-- Prove2me | solution 1 for Lean4LPD.PauliString.support_subset_cover_of_mem_hitting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:09:35.409296+00:00
-- url     : https://prove2.me/submissions/a95c6b96-f3e5-4e86-882d-7889c832220a

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
theorem _root_.solution (h : G ∈ hitting L S) :
    support G ⊆ cover L S :=
  (Finset.subset_biUnion_of_mem support h).trans Finset.subset_union_right
end Lean4LPD.PauliString
