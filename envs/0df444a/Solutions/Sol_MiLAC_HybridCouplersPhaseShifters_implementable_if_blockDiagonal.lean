-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.implementable_if_blockDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:43:53.703719+00:00
-- url     : https://prove2.me/submissions/51fc0597-82f2-4c87-a283-bd2ded84009e

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_ImplementableOn_to_equiv
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_implementableOn_iff
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_implementable_if_phaseDiagonal
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_implementable_if_block
public import Theorems.Thm_MiLAC_PhaseShifters_implementable_if_phaseDiagonal


set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters
namespace MiLAC.HybridCouplersPhaseShifters
theorem _root_.solution {C S : ℕ} (θ₁₁ θ₁₂ θ₂₁ : Fin C → ℝ) (φ : Fin S → ℝ) :
    Implementable (blockDiagonal θ₁₁ θ₁₂ θ₂₁ φ) :=
  Implementable.parallel
    ((ImplementableOn.blockDiagonal C _ fun _ =>
      (implementableOn_iff _).2 (implementable_if_block _ _ _)).to_equiv _ finProdFinEquiv)
    (implementable_if_phaseDiagonal φ)
end MiLAC.HybridCouplersPhaseShifters
