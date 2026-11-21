-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.implementable_if_layered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:44:49.287802+00:00
-- url     : https://prove2.me/submissions/4afdf466-724a-4c69-905a-0b637c18f70d

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_implementable_mul
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_ImplementableOn_to_equiv
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_implementableOn_iff
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_implementable_if_blockDiagonal

set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters
namespace MiLAC.HybridCouplersPhaseShifters
theorem _root_.solution {n : ℕ} (σ₀ : Equiv.Perm (Fin n)) (layers : List (Layer n)) :
    Implementable (layered σ₀ layers) := by
  induction layers with
  | nil => exact Implementable.pn σ₀
  | cons layer layers ih =>
      have hD := ((implementableOn_iff _).2
        (implementable_if_blockDiagonal layer.θ₁₁ layer.θ₁₂ layer.θ₂₁ layer.φ)).to_equiv n
          (finCongr layer.size)
      exact implementable_mul (implementable_mul (Implementable.pn _) hD) ih
end MiLAC.HybridCouplersPhaseShifters
