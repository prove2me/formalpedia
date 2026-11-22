-- Prove2me | solution 1 for Lean4LPD.PauliString.sympForm_eq_zero_of_disjoint_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:09:27.389839+00:00
-- url     : https://prove2.me/submissions/1394b5db-419f-4638-8313-29f1eace470e

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Theorems.Thm_Lean4LPD_PauliString_antiSites_subset_inter
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_eq_card_antiSites


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}
namespace Lean4LPD.PauliString
theorem _root_.solution (h : Disjoint (support G) (support p)) :
    sympForm G p = 0 := by
  have hempty : antiSites G p = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i hi
    have := antiSites_subset_inter G p hi
    rw [Finset.mem_inter] at this
    exact (Finset.disjoint_left.1 h this.1) this.2
  rw [sympForm_eq_card_antiSites, hempty, Finset.card_empty, Nat.cast_zero]
end Lean4LPD.PauliString
