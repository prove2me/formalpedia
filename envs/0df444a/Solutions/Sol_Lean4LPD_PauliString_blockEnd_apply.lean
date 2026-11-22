-- Prove2me | solution 1 for Lean4LPD.PauliString.blockEnd_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:42:20.561185+00:00
-- url     : https://prove2.me/submissions/ce16df4f-a70b-4661-a213-34a805e4fd89

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
open Finset
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period : ℕ) (A : Matrix (Bits n) (Bits n) ℂ) :
    blockEnd Gs θ period A = traj Gs θ A period := rfl
end Lean4LPD.PauliString
