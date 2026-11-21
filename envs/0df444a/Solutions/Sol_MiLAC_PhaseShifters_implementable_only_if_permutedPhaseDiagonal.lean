-- Prove2me | solution 1 for MiLAC.PhaseShifters.implementable_only_if_permutedPhaseDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:56.249215+00:00
-- url     : https://prove2.me/submissions/a0dcb4c8-d779-4e24-b197-434197534511

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Definitions.Def_LeanPool_MicrowaveNetworks_PhaseShifters
public import Theorems.Thm_MiLAC_PhaseShifters_permutedPhaseDiagonal_apply
public import Theorems.Thm_MiLAC_PhaseShifters_series_permutedPhaseDiagonal
public import Theorems.Thm_MiLAC_PhaseShifters_parallel_permutedPhaseDiagonal
public import Theorems.Thm_MiLAC_castAdd_ne_natAdd
public import Theorems.Thm_MiLAC_interconnection_eq_phaseShifter_zero
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
theorem _root_.solution {n : ℕ}
    {S : Network n} (hS : Implementable S) :
    ∃ φ : Fin n → ℝ, ∃ σ : Equiv.Perm (Fin n), S = permutedPhaseDiagonal φ σ := by
  induction hS with
  | ps φ =>
    refine ⟨fun _ => φ, Equiv.refl _, ?_⟩
    ext i j
    fin_cases i
    fin_cases j
    simp [permutedPhaseDiagonal, phaseShifter]
  | ic =>
    refine ⟨fun _ => 0, Equiv.refl _, ?_⟩
    rw [interconnection_eq_phaseShifter_zero]
    ext i j
    fin_cases i
    fin_cases j
    simp [permutedPhaseDiagonal, phaseShifter]
  | pn σ =>
    refine ⟨fun _ => 0, σ, ?_⟩
    ext i j
    simp [permutedPhaseDiagonal, permutationNetwork]
  | series _ _ ihA ihB =>
    obtain ⟨φ, σ, rfl⟩ := ihA
    obtain ⟨ψ, τ, rfl⟩ := ihB
    exact series_permutedPhaseDiagonal φ ψ σ τ
  | parallel _ _ ihA ihB =>
    obtain ⟨φ, σ, rfl⟩ := ihA
    obtain ⟨ψ, τ, rfl⟩ := ihB
    exact parallel_permutedPhaseDiagonal φ ψ σ τ
end MiLAC.PhaseShifters
