-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.implementable_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:27.618911+00:00
-- url     : https://prove2.me/submissions/c271fa21-b1ce-4af9-be4f-0a03afed9d38

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
theorem _root_.solution {n : ℕ} {A B : Network n}
    (hA : Implementable A) (hB : Implementable B) : Implementable (A * B) :=
  Implementable.series hB hA
end MiLAC.HybridCouplersPhaseShifters
