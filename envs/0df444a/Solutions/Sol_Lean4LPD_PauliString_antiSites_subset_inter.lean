-- Prove2me | solution 1 for Lean4LPD.PauliString.antiSites_subset_inter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:08:24.279381+00:00
-- url     : https://prove2.me/submissions/2ce17211-38f4-4113-80bf-45e4694c3451

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Theorems.Thm_Lean4LPD_PauliString_mem_antiSites
public import Theorems.Thm_Lean4LPD_PauliString_mem_support
attribute [local simp] Lean4LPD.PauliString.mem_antiSites
attribute [local simp] Lean4LPD.PauliString.mem_support



set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}
namespace Lean4LPD.PauliString
theorem _root_.solution (G s : PauliString n) :
    antiSites G s ⊆ support G ∩ support s := by
  intro i hi
  rw [mem_antiSites] at hi
  exact Finset.mem_inter.2 ⟨mem_support.2 hi.1, mem_support.2 hi.2.1⟩
end Lean4LPD.PauliString
