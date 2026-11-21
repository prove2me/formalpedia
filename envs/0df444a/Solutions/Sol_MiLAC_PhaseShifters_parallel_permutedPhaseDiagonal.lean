-- Prove2me | solution 1 for MiLAC.PhaseShifters.parallel_permutedPhaseDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:39:29.555934+00:00
-- url     : https://prove2.me/submissions/7cc8b971-8941-4bd1-abd3-2c86e84b0e61

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
    {n m : ℕ} (φ : Fin n → ℝ) (ψ : Fin m → ℝ)
    (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m)) :
    ∃ χ : Fin (n + m) → ℝ, ∃ ρ : Equiv.Perm (Fin (n + m)),
      parallel (permutedPhaseDiagonal φ σ)
        (permutedPhaseDiagonal ψ τ) =
        permutedPhaseDiagonal χ ρ := by
  refine ⟨Sum.elim φ ψ ∘ finSumFinEquiv.symm,
    finSumFinEquiv.symm.trans ((Equiv.sumCongr σ τ).trans finSumFinEquiv), ?_⟩
  ext i j
  induction i using Fin.addCases <;> induction j using Fin.addCases <;>
    simp [parallel, Matrix.reindex_apply, permutedPhaseDiagonal_apply]
end MiLAC.PhaseShifters
