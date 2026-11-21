-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.IsLayered.series
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:42:29.239386+00:00
-- url     : https://prove2.me/submissions/03adc69e-5edf-446b-b9f4-c85bed4f6fc2

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_isLayered_permutationNetwork_mul
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
theorem _root_.solution {n : ℕ} {A B : Network n} (hA : IsLayered A) (hB : IsLayered B) :
    IsLayered (series A B) := by
  obtain ⟨σA, layersA, rfl⟩ := hA
  obtain ⟨σB, layersB, rfl⟩ := hB
  induction layersB with
  | nil => exact isLayered_permutationNetwork_mul σB σA layersA
  | cons layer rest ih =>
      obtain ⟨σ₀, layers, h⟩ := ih
      refine ⟨σ₀, layer :: layers, ?_⟩
      simp only [MiLAC.series, layered, Matrix.mul_assoc] at h ⊢
      rw [h]
end IsLayered
end MiLAC.HybridCouplersPhaseShifters
