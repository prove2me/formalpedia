-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.ImplementableOn.to_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:42:22.196174+00:00
-- url     : https://prove2.me/submissions/88dc53fb-ff94-4eae-b783-283b0672785b

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_implementable_submatrix
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
theorem _root_.solution {ι : Type*} {M : Matrix ι ι ℂ}
    (h : ImplementableOn M) (n : ℕ) (e : ι ≃ Fin n) :
    Implementable (Matrix.reindex e e M) := by
  obtain ⟨m, g, h⟩ := h
  have hmn : m = n := by simpa using Fintype.card_congr (g.symm.trans e)
  subst hmn
  have hM : Matrix.reindex e e M =
      (Matrix.reindex g g M).submatrix (e.symm.trans g) (e.symm.trans g) := by
    ext i j
    simp [Matrix.reindex_apply]
  rw [hM]
  exact implementable_submatrix h _ _
end ImplementableOn
end MiLAC.HybridCouplersPhaseShifters
