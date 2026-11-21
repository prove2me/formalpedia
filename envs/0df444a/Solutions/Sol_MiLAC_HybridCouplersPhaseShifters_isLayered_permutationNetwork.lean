-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.isLayered_permutationNetwork
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:39.171854+00:00
-- url     : https://prove2.me/submissions/532aa5c0-edc4-4cda-b322-ab0db8a0b052

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters

set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters
namespace MiLAC.HybridCouplersPhaseShifters
theorem _root_.solution {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    IsLayered (permutationNetwork σ) :=
  ⟨σ, [], rfl⟩
end MiLAC.HybridCouplersPhaseShifters
