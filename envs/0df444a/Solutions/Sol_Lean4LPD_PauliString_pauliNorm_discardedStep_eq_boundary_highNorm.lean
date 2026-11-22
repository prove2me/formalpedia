-- Prove2me | solution 1 for Lean4LPD.PauliString.pauliNorm_discardedStep_eq_boundary_highNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:51:03.516386+00:00
-- url     : https://prove2.me/submissions/35dd2998-8f9f-42dc-b655-4b4a3033f20f

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Theorems.Thm_Lean4LPD_PauliString_pauliNorm_discardedStep
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
    pauliNorm (discardedStep Gs θ period wstar O d) = highNorm wstar
      (rot (toMatrix (Gs (period - 1))) (θ (period - 1)) *
        trotterTraj Gs θ period wstar O (d * period + (period - 1)) *
        rot (toMatrix (Gs (period - 1))) (-(θ (period - 1)))) := by
  rw [pauliNorm_discardedStep, trotterBlock_eq_boundary_pre Gs θ period wstar O d hp]
end Lean4LPD.PauliString
