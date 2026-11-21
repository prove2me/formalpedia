-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.implementable_only_if_layered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:48:24.524307+00:00
-- url     : https://prove2.me/submissions/42dc566d-b1ba-4c5a-a48f-49c0aae49bf0

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_isLayered_permutationNetwork
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_IsLayered_series
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_IsLayered_parallel
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_isLayered_phaseShifter
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_isLayered_hybridCoupler
public import Theorems.Thm_MiLAC_interconnection_eq_phaseShifter_zero


set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters
namespace MiLAC.HybridCouplersPhaseShifters
theorem _root_.solution {n : ℕ}
    {S : Network n} (hS : Implementable S) :
    ∃ σ₀ : Equiv.Perm (Fin n), ∃ layers : List (Layer n), S = layered σ₀ layers := by
  induction hS with
  | ic =>
      rw [interconnection_eq_phaseShifter_zero]
      exact isLayered_phaseShifter 0
  | ps φ => exact isLayered_phaseShifter φ
  | pn σ => exact isLayered_permutationNetwork σ
  | hc => exact isLayered_hybridCoupler
  | series _ _ hA hB => exact IsLayered.series hA hB
  | parallel _ _ hA hB => exact IsLayered.parallel hA hB
end MiLAC.HybridCouplersPhaseShifters
