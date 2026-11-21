-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.isLayered_parallel_blockDiagonal_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:44:32.789841+00:00
-- url     : https://prove2.me/submissions/ad15e2e6-df10-4f8e-a1ff-ca8833e8ee20

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_parallel_assoc
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_NetEquiv_parallel_left
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_IsLayered_of_netEquiv
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_isLayered_blockDiagonal
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_phaseDiagonal_parallel_one

set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters
namespace MiLAC.HybridCouplersPhaseShifters
theorem _root_.solution {n : ℕ} (layer : Layer n) (m : ℕ) :
    IsLayered (parallel (Matrix.reindex (finCongr layer.size) (finCongr layer.size)
      (blockDiagonal layer.θ₁₁ layer.θ₁₂ layer.θ₂₁ layer.φ)) (1 : Network m)) := by
  have h : NetEquiv
      ⟨n + m, parallel (Matrix.reindex (finCongr layer.size) (finCongr layer.size)
        (blockDiagonal layer.θ₁₁ layer.θ₁₂ layer.θ₂₁ layer.φ)) (1 : Network m)⟩
      ⟨2 * layer.C + (layer.S + m),
        blockDiagonal layer.θ₁₁ layer.θ₁₂ layer.θ₂₁ (Fin.append layer.φ 0)⟩ := by
    refine ((NetEquiv.reindex _ _).parallel_left _).trans ?_
    refine (parallel_assoc _ _ _).trans ?_
    rw [phaseDiagonal_parallel_one]
    exact ⟨Equiv.refl _, rfl⟩
  exact IsLayered.of_netEquiv h (isLayered_blockDiagonal _ _ _ _)
end MiLAC.HybridCouplersPhaseShifters
