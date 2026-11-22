-- Prove2me | solution 1 for Lean4LPD.PauliString.weight_sub_le_weight_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:28.305105+00:00
-- url     : https://prove2.me/submissions/488490e0-5629-47a3-9a27-ecfd47ccfb88

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Theorems.Thm_Lean4LPD_PauliString_weight_le_weight_mul_add_kh

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n} {i : Fin n}
variable {kh : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (hk : weight G ≤ kh) (h : sympForm G s = 1) :
    weight s - (kh - 1) ≤ weight (G * s) := by
  have := weight_le_weight_mul_add_kh hk h
  omega
end Lean4LPD.PauliString
