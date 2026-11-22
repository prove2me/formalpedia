-- Prove2me | solution 1 for Lean4LPD.PauliString.pauliNorm_blockEnd_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:48:19.591611+00:00
-- url     : https://prove2.me/submissions/0f64070d-4ae7-4f06-9528-8eaf1a0db9a7

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
public import Theorems.Thm_Lean4LPD_PauliString_blockEnd_pow_eq_periodic_traj

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
open Finset
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution {Gs : ℕ → PauliString n}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (θ : ℕ → ℝ) (period : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) :
    pauliNorm (((blockEnd Gs θ period) ^ r) O) = pauliNorm O := by
  rw [blockEnd_pow_eq_periodic_traj]
  exact pauliNorm_traj (fun g => hG (g % period)) _ _ _
end Lean4LPD.PauliString
