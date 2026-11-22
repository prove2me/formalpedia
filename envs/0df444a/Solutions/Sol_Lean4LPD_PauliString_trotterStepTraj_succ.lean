-- Prove2me | solution 1 for Lean4LPD.PauliString.trotterStepTraj_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:21.123989+00:00
-- url     : https://prove2.me/submissions/9bef5693-1b9b-4302-b1ea-5a17132dad52

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
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) :
    trotterStepTraj Gs θ period wstar O (d + 1) =
      truncOp (highSet n wstar)ᶜ
        (traj Gs θ (trotterStepTraj Gs θ period wstar O d) period) := rfl
end Lean4LPD.PauliString
