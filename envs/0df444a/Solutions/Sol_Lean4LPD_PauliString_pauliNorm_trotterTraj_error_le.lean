-- Prove2me | solution 1 for Lean4LPD.PauliString.pauliNorm_trotterTraj_error_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:53:12.974157+00:00
-- url     : https://prove2.me/submissions/260e51e2-456a-4333-ae2f-fd64a1bf1fe8

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
public import Theorems.Thm_Lean4LPD_PauliString_pauliNorm_periodic_traj_error_le
public import Theorems.Thm_Lean4LPD_PauliString_trotterTraj_at_boundary


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
open Finset
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution {Gs : ℕ → PauliString n}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (θ : ℕ → ℝ) (period wstar : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) (hp : 0 < period) :
    pauliNorm (traj (fun g => Gs (g % period)) (fun g => θ (g % period)) O (r * period) -
        trotterTraj Gs θ period wstar O (r * period)) ≤
      ∑ d ∈ range r, pauliNorm (discardedStep Gs θ period wstar O d) := by
  rw [trotterTraj_at_boundary Gs θ period wstar O r hp]
  exact pauliNorm_periodic_traj_error_le hG θ period wstar O r
end Lean4LPD.PauliString
