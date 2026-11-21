-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.IsLayered.of_netEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:43:47.770961+00:00
-- url     : https://prove2.me/submissions/19af83d2-77e7-4400-983d-71d07ab62411

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_permutationNetwork_mul_eq_submatrix
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_mul_permutationNetwork_eq_submatrix
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_ImplementableOn_mul
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_isLayered_permutationNetwork
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_IsLayered_mul
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
namespace IsLayered
theorem _root_.solution {X Y : Σ n : ℕ, Network n}
    (h : NetEquiv X Y) (hY : IsLayered Y.2) : IsLayered X.2 := by
  obtain ⟨e, he⟩ := h
  obtain ⟨a, A⟩ := X
  obtain ⟨b, B⟩ := Y
  have hab : a = b := by simpa using Fintype.card_congr e
  subst hab
  dsimp only at e he hY ⊢
  have hA : A = permutationNetwork e * B * permutationNetwork e.symm := by
    rw [permutationNetwork_mul_eq_submatrix, mul_permutationNetwork_eq_submatrix,
      Matrix.submatrix_submatrix, he]
    simp
  rw [hA]
  exact ((isLayered_permutationNetwork e).mul hY).mul
    (isLayered_permutationNetwork e.symm)
end IsLayered
end MiLAC.HybridCouplersPhaseShifters
