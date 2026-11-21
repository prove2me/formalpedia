-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.implementable_if_phaseDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:41:42.901758+00:00
-- url     : https://prove2.me/submissions/1fc84ccc-1d2f-425c-9446-2ff73c94ee33

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_implementable_of_phaseShifters
public import Theorems.Thm_MiLAC_PhaseShifters_implementable_if_phaseDiagonal


set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters
namespace MiLAC.HybridCouplersPhaseShifters
theorem _root_.solution {n : ℕ} (φ : Fin n → ℝ) :
    Implementable (phaseDiagonal φ) :=
  implementable_of_phaseShifters (MiLAC.PhaseShifters.implementable_if_phaseDiagonal φ)
end MiLAC.HybridCouplersPhaseShifters
