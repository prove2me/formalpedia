-- Prove2me | solution 1 for Lean4LPD.PauliString.trajTrunc_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:47:10.054345+00:00
-- url     : https://prove2.me/submissions/6a45475e-6e1b-47d8-96b1-a7359450b701

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
theorem _root_.solution (Gs : ℕ → PauliString n) (θ : ℕ → ℝ) (O : Matrix (Bits n) (Bits n) ℂ)
    (g : ℕ) : trajTrunc Gs θ (fun _ => univ) O g = traj Gs θ O g := by
  induction g with
  | zero => rfl
  | succ g ih => rw [trajTrunc_succ, ih, truncOp_univ, traj_succ]
end Lean4LPD.PauliString
