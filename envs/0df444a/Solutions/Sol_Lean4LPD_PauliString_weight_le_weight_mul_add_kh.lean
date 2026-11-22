-- Prove2me | solution 1 for Lean4LPD.PauliString.weight_le_weight_mul_add_kh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:11:52.265567+00:00
-- url     : https://prove2.me/submissions/723da0f5-ad77-459d-bb17-45887c0f9b6a

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Theorems.Thm_Lean4LPD_PauliString_weight_le_weight_mul_add

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n} {i : Fin n}
variable {kh : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (hk : weight G ≤ kh) (h : sympForm G s = 1) :
    weight s ≤ weight (G * s) + (kh - 1) := by
  have := weight_le_weight_mul_add h
  omega
end Lean4LPD.PauliString
