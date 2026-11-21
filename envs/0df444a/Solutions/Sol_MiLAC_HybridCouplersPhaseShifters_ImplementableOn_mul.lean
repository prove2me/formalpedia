-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.ImplementableOn.mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:43:07.075684+00:00
-- url     : https://prove2.me/submissions/c5030faa-1794-4589-a9aa-62fa3067ee4c

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
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
theorem _root_.solution {ι : Type*} [Fintype ι] {A B : Matrix ι ι ℂ}
    (hA : ImplementableOn A) (hB : ImplementableOn B) : ImplementableOn (A * B) := by
  obtain ⟨n, e, hA⟩ := hA
  refine ImplementableOn.of_equiv e ?_
  have hM : Matrix.reindex e e (A * B) = Matrix.reindex e e A * Matrix.reindex e e B := by
    simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [hM]
  exact implementable_mul hA (hB.to_equiv n e)
end ImplementableOn
end MiLAC.HybridCouplersPhaseShifters
