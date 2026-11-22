-- Prove2me | solution 1 for Lean4LPD.PauliString.pauliNorm_discardedStep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:49:23.177081+00:00
-- url     : https://prove2.me/submissions/97c3a40b-9250-47cd-978c-4d243497b33e

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Theorems.Thm_Lean4LPD_PauliString_trotterStepTraj_succ
public import Theorems.Thm_Lean4LPD_PauliString_pauliNorm_sub_truncOp_highSet_compl


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
    pauliNorm (discardedStep Gs θ period wstar O d) =
      highNorm wstar (traj Gs θ (trotterStepTraj Gs θ period wstar O d) period) := by
  rw [discardedStep, trotterStepTraj_succ, pauliNorm_sub_truncOp_highSet_compl]
end Lean4LPD.PauliString
