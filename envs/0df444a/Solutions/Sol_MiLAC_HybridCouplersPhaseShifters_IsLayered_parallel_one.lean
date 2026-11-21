-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.IsLayered.parallel_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:45:07.447928+00:00
-- url     : https://prove2.me/submissions/4fc70a6a-0430-4c18-9c0b-cf79f840e452

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_parallel_mul
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_parallel_permutationNetwork
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_ImplementableOn_mul
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_isLayered_permutationNetwork
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_IsLayered_mul
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_isLayered_parallel_blockDiagonal_one
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
theorem _root_.solution {n : ℕ} {S : Network n}
    (hS : IsLayered S) (m : ℕ) : IsLayered (parallel S (1 : Network m)) := by
  obtain ⟨σ₀, layers, rfl⟩ := hS
  induction layers with
  | nil =>
      have hone : (1 : Network m) = permutationNetwork 1 := by
        simp [permutationNetwork, Equiv.Perm.one_def]
      simp only [layered]
      rw [hone, parallel_permutationNetwork]
      exact isLayered_permutationNetwork _
  | cons layer layers ih =>
      have hone : (1 : Network m) = permutationNetwork 1 * 1 * 1 := by
        simp [permutationNetwork, Equiv.Perm.one_def]
      simp only [layered]
      rw [hone, ← parallel_mul, ← parallel_mul, parallel_permutationNetwork]
      exact ((isLayered_permutationNetwork _).mul
        (isLayered_parallel_blockDiagonal_one layer m)).mul ih
end IsLayered
end MiLAC.HybridCouplersPhaseShifters
