-- Prove2me | solution 1 for Lean4LPD.PauliString.sum_coeff_smul_toMatrix_herm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:39:55.445441+00:00
-- url     : https://prove2.me/submissions/62e9c3bb-3091-4beb-bd29-8d4292162e6f

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Truncate
public import Theorems.Thm_Lean4LPD_PauliString_truncOp_univ

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n ko kh : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (O : Matrix (Bits n) (Bits n) ℂ) :
    ∑ p : PauliIndex n, coeff O p • toMatrix (herm p) = O := truncOp_univ O
end Lean4LPD.PauliString
