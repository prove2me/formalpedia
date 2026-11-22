-- Prove2me | solution 1 for Lean4LPD.PauliString.bitsMatrixEquiv_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:21:24.735718+00:00
-- url     : https://prove2.me/submissions/98412863-062e-4726-a016-cfc0b4df7aa1

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Tensor

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Matrix Finset
namespace Lean4LPD.PauliString
theorem _root_.solution (n : ℕ) (A : Matrix (Bits n) (Bits n) ℂ) :
    bitsMatrixEquiv n (star A) = star (bitsMatrixEquiv n A) := rfl
end Lean4LPD.PauliString
