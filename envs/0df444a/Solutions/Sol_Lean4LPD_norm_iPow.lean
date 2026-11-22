-- Prove2me | solution 1 for Lean4LPD.norm_iPow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:17:17.967965+00:00
-- url     : https://prove2.me/submissions/a9f60ff0-2b8b-4990-82ea-a5825ab17b3e

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution (k : ZMod 4) : ‖iPow k‖ = 1 := by
  rw [iPow, norm_pow, Complex.norm_I, one_pow]
end Lean4LPD
