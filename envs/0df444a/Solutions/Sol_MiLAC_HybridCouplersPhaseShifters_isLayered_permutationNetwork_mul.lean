-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.isLayered_permutationNetwork_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:41:43.60611+00:00
-- url     : https://prove2.me/submissions/fe75f3b9-9f3f-4d04-8f43-14d8b2bbda88

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_permutationNetwork_mul
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
theorem _root_.solution {n : ℕ} (τ σ₀ : Equiv.Perm (Fin n))
    (layers : List (Layer n)) : IsLayered (permutationNetwork τ * layered σ₀ layers) := by
  cases layers with
  | nil => exact ⟨σ₀ * τ, [], permutationNetwork_mul σ₀ τ⟩
  | cons layer rest =>
      refine ⟨σ₀, { layer with σ := layer.σ * τ } :: rest, ?_⟩
      simp only [layered, ← permutationNetwork_mul layer.σ τ, Matrix.mul_assoc]
end MiLAC.HybridCouplersPhaseShifters
