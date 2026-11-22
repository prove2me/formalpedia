-- Prove2me | solution 1 for Lean4LPD.PauliString.one_le_weight_of_sympForm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:10:39.300972+00:00
-- url     : https://prove2.me/submissions/52ed4dfd-4e9d-47a7-8791-31769c71f8aa

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Theorems.Thm_Lean4LPD_PauliString_card_cancelSites_add_card_antiSites_add_card_createSites
public import Theorems.Thm_Lean4LPD_PauliString_one_le_card_antiSites

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n} {i : Fin n}
namespace Lean4LPD.PauliString
theorem _root_.solution (h : sympForm G s = 1) : 1 ≤ weight G :=
  le_trans (one_le_card_antiSites h)
    (by have := card_cancelSites_add_card_antiSites_add_card_createSites G s; omega)
end Lean4LPD.PauliString
