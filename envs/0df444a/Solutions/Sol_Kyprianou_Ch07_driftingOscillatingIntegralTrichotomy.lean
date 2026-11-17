-- Prove2me | solution 1 for Kyprianou.Ch07.driftingOscillatingIntegralTrichotomy
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:19:43.755824+00:00
-- url     : https://prove2.me/submissions/47444303-5e73-472a-976e-2a9374189230
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch07_signIntegralNegativeDrift
import Theorems.Thm_Kyprianou_Ch07_signIntegralPositiveDrift
import Theorems.Thm_Kyprianou_Ch07_doubleDivergentSignIntegralOscillation
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch07_DriftOscillationObservables
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch07

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X) :
    ((nonnegativeSignIntegral P X < ⊤ →
      DriftsToNegInfinity P X) ∧
     (nonpositiveSignIntegral P X < ⊤ →
      DriftsToPosInfinity P X) ∧
     (nonnegativeSignIntegral P X = ⊤ →
      nonpositiveSignIntegral P X = ⊤ →
      IsNontrivialLevyProcess P X →
      OscillatesAtInfinity P X)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hFinite
    exact Kyprianou.Ch07.signIntegralNegativeDrift P X hX hFinite
  · intro hFinite
    exact Kyprianou.Ch07.signIntegralPositiveDrift P X hX hFinite
  · intro hPos hNeg hNontrivial
    exact Kyprianou.Ch07.doubleDivergentSignIntegralOscillation
      P X hX hPos hNeg hNontrivial
