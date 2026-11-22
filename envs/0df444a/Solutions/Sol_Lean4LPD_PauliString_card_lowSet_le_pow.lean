-- Prove2me | solution 1 for Lean4LPD.PauliString.card_lowSet_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:26:37.817275+00:00
-- url     : https://prove2.me/submissions/497e6810-24c3-4c55-8ad2-9aeed12a7893

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Count

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (n w : ℕ) (hw : w ≤ n) :
    (lowSet n w).card ≤ 4 ^ w * n ^ w :=
  (card_lowSet_le n w hw).trans <| by
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.choose_le_pow n w)
end Lean4LPD.PauliString
