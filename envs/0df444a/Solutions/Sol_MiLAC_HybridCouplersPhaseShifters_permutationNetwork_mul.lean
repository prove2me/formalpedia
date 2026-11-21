-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.permutationNetwork_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:56.868723+00:00
-- url     : https://prove2.me/submissions/1db92c0a-6e3d-46db-950b-03555aa04068

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
theorem _root_.solution {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    permutationNetwork τ * permutationNetwork σ = permutationNetwork (σ * τ) := by
  unfold permutationNetwork
  rw [Equiv.Perm.mul_def, Equiv.toPEquiv_trans, PEquiv.toMatrix_trans]
end MiLAC.HybridCouplersPhaseShifters
