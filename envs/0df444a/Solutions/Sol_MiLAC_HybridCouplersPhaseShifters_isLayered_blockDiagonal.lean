-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.isLayered_blockDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:32.493196+00:00
-- url     : https://prove2.me/submissions/79c99d60-4b41-490f-b33b-844a25dc2e5d

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
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
theorem _root_.solution {C S : ℕ} (θ₁₁ θ₁₂ θ₂₁ : Fin C → ℝ) (φ : Fin S → ℝ) :
    IsLayered (blockDiagonal θ₁₁ θ₁₂ θ₂₁ φ) := by
  refine ⟨1, [⟨C, S, θ₁₁, θ₁₂, θ₂₁, φ, rfl, 1⟩], ?_⟩
  simp [layered, permutationNetwork, Equiv.Perm.one_def]
end MiLAC.HybridCouplersPhaseShifters
