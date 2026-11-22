-- Prove2me | solution 1 for Lean4LPD.PauliString.abs_weight_mul_sub_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:13:25.768588+00:00
-- url     : https://prove2.me/submissions/c5d55663-96f2-47b8-93e0-a4e1ab9c2501

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Theorems.Thm_Lean4LPD_PauliString_one_le_weight_of_sympForm_eq_one
public import Theorems.Thm_Lean4LPD_PauliString_weight_le_weight_mul_add
public import Theorems.Thm_Lean4LPD_PauliString_weight_mul_le_weight_add

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n} {i : Fin n}
namespace Lean4LPD.PauliString
theorem _root_.solution (h : sympForm G s = 1) :
    |(weight (G * s) : ℤ) - (weight s : ℤ)| ≤ (weight G : ℤ) - 1 := by
  have h1 := weight_le_weight_mul_add h
  have h2 := weight_mul_le_weight_add h
  have h3 := one_le_weight_of_sympForm_eq_one h
  rw [abs_le]
  omega
end Lean4LPD.PauliString
