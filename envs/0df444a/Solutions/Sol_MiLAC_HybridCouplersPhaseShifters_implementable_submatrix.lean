-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.implementable_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:41:47.702215+00:00
-- url     : https://prove2.me/submissions/fe09e234-26d8-4428-b351-69465088c056

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_permutationNetwork_mul_eq_submatrix
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_mul_permutationNetwork_eq_submatrix
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_implementable_mul
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
theorem _root_.solution {n : ℕ} {A : Network n} (hA : Implementable A)
    (σ τ : Equiv.Perm (Fin n)) : Implementable (A.submatrix σ τ) := by
  have h : A.submatrix σ τ =
      permutationNetwork σ * A * permutationNetwork τ.symm := by
    rw [permutationNetwork_mul_eq_submatrix, mul_permutationNetwork_eq_submatrix,
      Matrix.submatrix_submatrix]
    simp
  rw [h]
  exact implementable_mul (implementable_mul (Implementable.pn σ) hA)
    (Implementable.pn τ.symm)
end MiLAC.HybridCouplersPhaseShifters
