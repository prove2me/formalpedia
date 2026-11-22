-- Prove2me | solution 1 for Lean4LPD.PauliString.pauliNorm_eq_sqrt_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:22:42.602609+00:00
-- url     : https://prove2.me/submissions/f14e5f5a-1ff8-4f64-9f44-23e233b06add

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Theorems.Thm_Lean4LPD_PauliString_sum_norm_coeff_sq

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm O = Real.sqrt (∑ p : PauliIndex n, ‖coeff O p‖ ^ 2) := by
  rw [pauliNorm, sum_norm_coeff_sq]
end Lean4LPD.PauliString
