-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.ImplementableOn.submatrix_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:43:08.477768+00:00
-- url     : https://prove2.me/submissions/1819f344-b3aa-42c1-bdd3-63a27bdd9664

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_mul_permutationNetwork_eq_submatrix
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_implementable_mul
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_ImplementableOn_to_equiv
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



set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters
namespace MiLAC.HybridCouplersPhaseShifters
namespace ImplementableOn
theorem _root_.solution {ι : Type*}
    {M : Matrix ι ι ℂ} (h : ImplementableOn M) {n : ℕ} (e₁ e₂ : ι ≃ Fin n) :
    Implementable (M.submatrix e₁.symm e₂.symm) := by
  have hM : M.submatrix e₁.symm e₂.symm =
      Matrix.reindex e₁ e₁ M * permutationNetwork (e₁.symm.trans e₂) := by
    rw [mul_permutationNetwork_eq_submatrix]
    ext i j
    simp [Matrix.reindex_apply]
  rw [hM]
  exact implementable_mul (h.to_equiv n e₁) (Implementable.pn _)
end ImplementableOn
end MiLAC.HybridCouplersPhaseShifters
