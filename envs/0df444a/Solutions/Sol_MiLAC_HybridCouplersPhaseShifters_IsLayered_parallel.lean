-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.IsLayered.parallel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:46:46.321507+00:00
-- url     : https://prove2.me/submissions/486a8157-2c0d-4262-ab55-1f7515d0152f

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_parallel_mul
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_ImplementableOn_mul
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_IsLayered_mul
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_IsLayered_parallel_one
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_IsLayered_one_parallel

set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters
namespace MiLAC.HybridCouplersPhaseShifters
namespace IsLayered
theorem _root_.solution {n m : ℕ} {A : Network n} {B : Network m}
    (hA : IsLayered A) (hB : IsLayered B) : IsLayered (parallel A B) := by
  have hsplit : MiLAC.parallel A B =
      MiLAC.parallel A 1 *
        MiLAC.parallel 1 B := by
    rw [parallel_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hsplit]
  exact (hA.parallel_one m).mul (hB.one_parallel n)
end IsLayered
end MiLAC.HybridCouplersPhaseShifters
