-- Prove2me | solution 1 for Lean4LPD.PauliString.pauliNorm_trotterStep_error_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:50:24.576456+00:00
-- url     : https://prove2.me/submissions/a60d81c5-72b3-4263-ad0a-d6c75fa3ad5b

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
public import Theorems.Thm_Lean4LPD_PauliString_pauliNorm_sum_le
public import Theorems.Thm_Lean4LPD_PauliString_trotterStep_telescoping
public import Theorems.Thm_Lean4LPD_PauliString_pauliNorm_blockEnd_pow

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
    (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) :
    pauliNorm (((blockEnd Gs θ period) ^ r) O - trotterStepTraj Gs θ period wstar O r) ≤
      ∑ d ∈ range r, pauliNorm (discardedStep Gs θ period wstar O d) := by
  rw [trotterStep_telescoping]
  refine (pauliNorm_sum_le _ _).trans ?_
  exact le_of_eq (Finset.sum_congr rfl fun d _ => pauliNorm_blockEnd_pow hG θ period _ _)
end Lean4LPD.PauliString
