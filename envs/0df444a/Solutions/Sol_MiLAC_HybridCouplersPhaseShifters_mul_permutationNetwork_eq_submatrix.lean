-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.mul_permutationNetwork_eq_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:28.541952+00:00
-- url     : https://prove2.me/submissions/4ea358e0-b2b8-4c9f-a85e-a2b461c24720

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
theorem _root_.solution {n : ℕ} (M : Network n) (σ : Equiv.Perm (Fin n)) :
    M * permutationNetwork σ = M.submatrix id σ.symm :=
  PEquiv.mul_toMatrix_toPEquiv M σ
end MiLAC.HybridCouplersPhaseShifters
