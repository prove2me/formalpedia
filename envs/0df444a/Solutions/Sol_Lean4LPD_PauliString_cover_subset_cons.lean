-- Prove2me | solution 1 for Lean4LPD.PauliString.cover_subset_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:10:46.409362+00:00
-- url     : https://prove2.me/submissions/e018943b-5d7f-4d75-92a9-58f92dd839a1

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Theorems.Thm_Lean4LPD_PauliString_hitting_subset_cons

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}
namespace Lean4LPD.PauliString
theorem _root_.solution (G : PauliString n) (Gs : List (PauliString n))
    (S : Finset (Fin n)) : cover Gs S ⊆ cover (G :: Gs) S :=
  Finset.union_subset_union_right
    (Finset.biUnion_subset_biUnion_of_subset_left _ (hitting_subset_cons G Gs S))
end Lean4LPD.PauliString
