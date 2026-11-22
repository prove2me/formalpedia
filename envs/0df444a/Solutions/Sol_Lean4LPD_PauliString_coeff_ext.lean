-- Prove2me | solution 1 for Lean4LPD.PauliString.coeff_ext
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:42:25.836736+00:00
-- url     : https://prove2.me/submissions/b7a1e410-a227-4e0d-8c48-95fe0fee8248

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Truncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Theorems.Thm_Lean4LPD_PauliString_sum_coeff_smul_toMatrix_herm


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution {A B : Matrix (Bits n) (Bits n) ℂ}
    (h : ∀ p : PauliIndex n, coeff A p = coeff B p) : A = B := by
  calc
    A = ∑ p : PauliIndex n, coeff A p • toMatrix (herm p) :=
      (sum_coeff_smul_toMatrix_herm A).symm
    _ = ∑ p : PauliIndex n, coeff B p • toMatrix (herm p) :=
      Finset.sum_congr rfl fun p _ => by rw [h p]
    _ = B := sum_coeff_smul_toMatrix_herm B
end Lean4LPD.PauliString
