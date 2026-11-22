-- Prove2me | solution 1 for Lean4LPD.PauliString.trotterBlock_eq_boundary_pre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:47:52.793892+00:00
-- url     : https://prove2.me/submissions/584110ba-3831-4da7-9135-958c48d2d4a1

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Theorems.Thm_Lean4LPD_PauliString_trotterTraj_within_step
public import Theorems.Thm_Lean4LPD_PauliString_trotterTraj_at_boundary

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
open Finset
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) (hp : 0 < period) :
    traj Gs θ (trotterStepTraj Gs θ period wstar O d) period =
      rot (toMatrix (Gs (period - 1))) (θ (period - 1)) *
        trotterTraj Gs θ period wstar O (d * period + (period - 1)) *
        rot (toMatrix (Gs (period - 1))) (-(θ (period - 1))) := by
  rw [trotterTraj_within_step Gs θ period wstar O d (period - 1) (by omega),
    trotterTraj_at_boundary Gs θ period wstar O d hp]
  have htraj := traj_succ Gs θ (trotterStepTraj Gs θ period wstar O d) (period - 1)
  rw [Nat.sub_add_cancel hp] at htraj
  exact htraj
end Lean4LPD.PauliString
