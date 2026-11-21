-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.IsLayered.one_parallel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:46:02.256189+00:00
-- url     : https://prove2.me/submissions/1dd976ce-f47c-4ea9-a802-69ce5e05e098

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_parallel_swap
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_IsLayered_of_netEquiv
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_IsLayered_parallel_one

set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters
namespace MiLAC.HybridCouplersPhaseShifters
namespace IsLayered
theorem _root_.solution {n : ℕ} {S : Network n}
    (hS : IsLayered S) (m : ℕ) : IsLayered (parallel (1 : Network m) S) :=
  IsLayered.of_netEquiv (X := ⟨m + n, parallel (1 : Network m) S⟩)
    (parallel_swap _ _) (hS.parallel_one m)
end IsLayered
end MiLAC.HybridCouplersPhaseShifters
