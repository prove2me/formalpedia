-- Prove2me | solution 1 for Lean4LPD.PauliString.trotterStepTraj_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:11.294799+00:00
-- url     : https://prove2.me/submissions/85852869-1447-47c7-9e73-59f610151e20

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
open Finset
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) :
    trotterStepTraj Gs θ period wstar O 0 = O := rfl
end Lean4LPD.PauliString
