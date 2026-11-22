-- Prove2me | solution 1 for Lean4LPD.PauliString.inter_support_nonempty_of_sympForm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:09:20.768885+00:00
-- url     : https://prove2.me/submissions/c27c5ad2-947b-4bdb-b236-6fd557165412

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Theorems.Thm_Lean4LPD_PauliString_antiSites_subset_inter
public import Theorems.Thm_Lean4LPD_PauliString_one_le_card_antiSites


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}
namespace Lean4LPD.PauliString
theorem _root_.solution (h : sympForm G p = 1) :
    (support G ∩ support p).Nonempty := by
  obtain ⟨i, hi⟩ := Finset.card_pos.1 (one_le_card_antiSites h)
  exact ⟨i, antiSites_subset_inter G p hi⟩
end Lean4LPD.PauliString
