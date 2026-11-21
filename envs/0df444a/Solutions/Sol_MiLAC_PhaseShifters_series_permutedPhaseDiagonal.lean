-- Prove2me | solution 1 for MiLAC.PhaseShifters.series_permutedPhaseDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:39:29.107122+00:00
-- url     : https://prove2.me/submissions/d4f01e9a-fff3-4aa3-b9ef-744d92eca055

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Definitions.Def_LeanPool_MicrowaveNetworks_PhaseShifters
public import Theorems.Thm_MiLAC_PhaseShifters_permutedPhaseDiagonal_apply
public import Theorems.Thm_MiLAC_castAdd_ne_natAdd
public import Theorems.Thm_MiLAC_natAdd_ne_castAdd
public import Theorems.Thm_MiLAC_parallel_castAdd_castAdd
public import Theorems.Thm_MiLAC_parallel_castAdd_natAdd
public import Theorems.Thm_MiLAC_parallel_natAdd_castAdd
public import Theorems.Thm_MiLAC_parallel_natAdd_natAdd
attribute [local simp] MiLAC.castAdd_ne_natAdd
attribute [local simp] MiLAC.natAdd_ne_castAdd
attribute [local simp] MiLAC.parallel_castAdd_castAdd
attribute [local simp] MiLAC.parallel_castAdd_natAdd
attribute [local simp] MiLAC.parallel_natAdd_castAdd
attribute [local simp] MiLAC.parallel_natAdd_natAdd


attribute [local simp] MiLAC.PhaseShifters.permutedPhaseDiagonal_apply

set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.PhaseShifters
namespace MiLAC.PhaseShifters
theorem _root_.solution
    {n : ℕ} (φ ψ : Fin n → ℝ) (σ τ : Equiv.Perm (Fin n)) :
    ∃ χ : Fin n → ℝ, ∃ ρ : Equiv.Perm (Fin n),
      series (permutedPhaseDiagonal φ σ)
        (permutedPhaseDiagonal ψ τ) =
        permutedPhaseDiagonal χ ρ := by
  refine ⟨fun i => φ i + ψ (σ.symm i), τ.trans σ, ?_⟩
  ext i j
  simp only [series, Matrix.mul_apply, permutedPhaseDiagonal_apply]
  rw [Finset.sum_eq_single (τ i) (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  by_cases h : σ (τ i) = j
  · subst j
    simp [Equiv.trans_apply, ← Complex.exp_add, add_mul, add_comm]
  · simp [Equiv.trans_apply, h]
end MiLAC.PhaseShifters
