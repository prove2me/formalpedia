-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.IsLayered.mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:43:03.393954+00:00
-- url     : https://prove2.me/submissions/11785633-e01d-449a-8e46-d3fd0077f441

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_IsLayered_series

set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters
namespace MiLAC.HybridCouplersPhaseShifters
namespace IsLayered
theorem _root_.solution {n : ℕ} {A B : Network n} (hA : IsLayered A) (hB : IsLayered B) :
    IsLayered (A * B) :=
  hB.series hA
end IsLayered
end MiLAC.HybridCouplersPhaseShifters
