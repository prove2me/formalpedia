-- Prove2me | solution 1 for Lean4LPD.PauliString.card_cancelSites_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:10:39.85075+00:00
-- url     : https://prove2.me/submissions/7ae91159-3236-41af-aded-1ba9f08cd7bc

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
theorem _root_.solution (h : sympForm G s = 1) :
    (cancelSites G s).card ≤ weight G - 1 := by
  have hp := card_cancelSites_add_card_antiSites_add_card_createSites G s
  have ha := one_le_card_antiSites h
  omega
end Lean4LPD.PauliString
