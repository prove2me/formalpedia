-- Prove2me | solution 1 for Lean4LPD.PauliString.weight_mul_le_weight_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:11:29.959771+00:00
-- url     : https://prove2.me/submissions/5d85f23e-c809-419d-a3c3-796f548641ac

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Theorems.Thm_Lean4LPD_PauliString_weight_mul_add_card_cancelSites
public import Theorems.Thm_Lean4LPD_PauliString_card_createSites_le

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n} {i : Fin n}
namespace Lean4LPD.PauliString
theorem _root_.solution (h : sympForm G s = 1) :
    weight (G * s) ≤ weight s + (weight G - 1) := by
  have hb := weight_mul_add_card_cancelSites G s
  have hc := card_createSites_le h
  omega
end Lean4LPD.PauliString
