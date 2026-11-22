-- Prove2me | solution 1 for Lean4LPD.PauliString.weight_mul_le_weight_add_kh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:07.034972+00:00
-- url     : https://prove2.me/submissions/83173e6e-c23f-42e7-afd7-742fd8cb8af9

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Theorems.Thm_Lean4LPD_PauliString_weight_mul_le_weight_add

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n} {i : Fin n}
variable {kh : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (hk : weight G ≤ kh) (h : sympForm G s = 1) :
    weight (G * s) ≤ weight s + (kh - 1) := by
  have := weight_mul_le_weight_add h
  omega
end Lean4LPD.PauliString
