-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.permutationNetwork_mul_eq_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:49.52995+00:00
-- url     : https://prove2.me/submissions/674ee98c-0076-45ff-adf3-df50d95c6e80

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
theorem _root_.solution {n : ℕ} (σ : Equiv.Perm (Fin n)) (M : Network n) :
    permutationNetwork σ * M = M.submatrix σ id :=
  PEquiv.toMatrix_toPEquiv_mul σ M
end MiLAC.HybridCouplersPhaseShifters
