-- Prove2me | solution 1 for Lean4LPD.PauliString.weight_le_weight_mul_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:11:16.336802+00:00
-- url     : https://prove2.me/submissions/afde535c-7c4c-423b-b350-dffb8c1e86de

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Theorems.Thm_Lean4LPD_PauliString_weight_mul_add_card_cancelSites
public import Theorems.Thm_Lean4LPD_PauliString_card_cancelSites_le

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n} {i : Fin n}
namespace Lean4LPD.PauliString
theorem _root_.solution (h : sympForm G s = 1) :
    weight s ≤ weight (G * s) + (weight G - 1) := by
  have hb := weight_mul_add_card_cancelSites G s
  have hc := card_cancelSites_le h
  omega
end Lean4LPD.PauliString
