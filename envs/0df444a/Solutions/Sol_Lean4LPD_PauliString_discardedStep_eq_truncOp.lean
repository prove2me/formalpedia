-- Prove2me | solution 1 for Lean4LPD.PauliString.discardedStep_eq_truncOp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:48:05.309407+00:00
-- url     : https://prove2.me/submissions/d3a0a638-9148-4be7-a842-0fc6fea07036

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Theorems.Thm_Lean4LPD_PauliString_trotterStepTraj_succ
public import Theorems.Thm_Lean4LPD_PauliString_sub_truncOp_compl


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
    discardedStep Gs θ period wstar O d = truncOp (highSet n wstar)
      (traj Gs θ (trotterStepTraj Gs θ period wstar O d) period) := by
  rw [discardedStep, trotterStepTraj_succ, sub_truncOp_compl]
end Lean4LPD.PauliString
