-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.not_implementableOn_of_infinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:41:32.230781+00:00
-- url     : https://prove2.me/submissions/c5d12da6-d373-4ba3-87c7-f47edf781530

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
theorem _root_.solution {ι : Type*} [Infinite ι] (M : Matrix ι ι ℂ) :
    ¬ImplementableOn M := by
  rintro ⟨n, e, _⟩
  exact (Finite.of_injective e e.injective).false
end MiLAC.HybridCouplersPhaseShifters
