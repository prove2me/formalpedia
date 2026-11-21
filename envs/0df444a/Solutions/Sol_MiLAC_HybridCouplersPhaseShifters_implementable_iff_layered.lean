-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.implementable_iff_layered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:49:08.073815+00:00
-- url     : https://prove2.me/submissions/fe1693e5-e2e3-4af2-b8fe-ba9b2369a832

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_implementable_if_layered
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_implementable_only_if_layered

set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters
namespace MiLAC.HybridCouplersPhaseShifters
theorem _root_.solution {n : ℕ} {S : Network n} :
    Implementable S ↔
      ∃ σ₀ : Equiv.Perm (Fin n), ∃ layers : List (Layer n), S = layered σ₀ layers := by
  constructor
  · exact implementable_only_if_layered
  · rintro ⟨σ₀, layers, rfl⟩
    exact implementable_if_layered σ₀ layers
end MiLAC.HybridCouplersPhaseShifters
