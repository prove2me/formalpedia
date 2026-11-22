-- Prove2me | solution 1 for Lean4LPD.PauliString.discardedStep_eq_boundary_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:49:20.724362+00:00
-- url     : https://prove2.me/submissions/edf3872f-3578-4d75-bd44-5848df5fe9b3

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Theorems.Thm_Lean4LPD_PauliString_trotterTraj_at_boundary
public import Theorems.Thm_Lean4LPD_PauliString_trotterBlock_eq_boundary_pre

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
    discardedStep Gs θ period wstar O d =
      rot (toMatrix (Gs (period - 1))) (θ (period - 1)) *
        trotterTraj Gs θ period wstar O (d * period + (period - 1)) *
        rot (toMatrix (Gs (period - 1))) (-(θ (period - 1))) -
      trotterTraj Gs θ period wstar O ((d + 1) * period) := by
  rw [discardedStep, trotterBlock_eq_boundary_pre Gs θ period wstar O d hp,
    trotterTraj_at_boundary Gs θ period wstar O (d + 1) hp]
end Lean4LPD.PauliString
