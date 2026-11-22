-- Prove2me | solution 1 for Lean4LPD.PauliString.pauliNorm_truncOp_highSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:40:01.135338+00:00
-- url     : https://prove2.me/submissions/a619b813-9c38-4218-ba1d-06f0c36364f0

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Truncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Theorems.Thm_Lean4LPD_PauliString_pauliNorm_truncOp

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (w : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm (truncOp (highSet n w) O) = highNorm w O := by
  rw [pauliNorm_truncOp, highNorm]
end Lean4LPD.PauliString
