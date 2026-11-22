-- Prove2me | solution 1 for Lean4LPD.PauliString.hitting_subset_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:09:57.936937+00:00
-- url     : https://prove2.me/submissions/2c1674e1-f683-4411-b1ff-7dd66cf1bfc7

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Theorems.Thm_Lean4LPD_PauliString_mem_hitting

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}
namespace Lean4LPD.PauliString
theorem _root_.solution (G : PauliString n) (Gs : List (PauliString n))
    (S : Finset (Fin n)) : hitting Gs S ⊆ hitting (G :: Gs) S := by
  intro H hH
  rw [mem_hitting] at hH ⊢
  exact ⟨List.mem_cons_of_mem _ hH.1, hH.2⟩
end Lean4LPD.PauliString
