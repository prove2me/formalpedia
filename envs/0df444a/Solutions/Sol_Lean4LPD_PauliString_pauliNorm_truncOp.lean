-- Prove2me | solution 1 for Lean4LPD.PauliString.pauliNorm_truncOp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:28.850826+00:00
-- url     : https://prove2.me/submissions/3fbe0049-bbf4-490d-b86b-eb39853f07a3

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Truncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Theorems.Thm_Lean4LPD_PauliString_norm_coeffVec


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (S : Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm (truncOp S O) = ‖restr S (coeffVec O)‖ := by
  rw [← norm_coeffVec, coeffVec_truncOp]
end Lean4LPD.PauliString
