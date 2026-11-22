-- Prove2me | solution 1 for Lean4LPD.PauliString.coeff_toMatrix_herm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:23:49.180801+00:00
-- url     : https://prove2.me/submissions/757dfa3c-7dfb-4a50-bfc2-7c3eccf62520

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Theorems.Thm_Lean4LPD_PauliString_coeff_toMatrix_herm

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution {p q : PauliIndex n} (h : wt q < wt p) :
    coeff (toMatrix (herm q)) p = 0 := by
  refine (coeff_toMatrix_herm p q).trans (if_neg fun hpq => ?_)
  rw [hpq] at h
  exact absurd h (lt_irrefl _)
end Lean4LPD.PauliString
