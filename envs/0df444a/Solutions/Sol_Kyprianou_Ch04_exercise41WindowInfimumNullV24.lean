-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41WindowInfimumNullV24
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:44:02.274928+00:00
-- url     : https://prove2.me/submissions/2b2c48ed-7cec-4016-90dc-fa734cda3362

import Theorems.Thm_Kyprianou_Ch04_exercise41FutureFunctionalOccupationV26
import Theorems.Thm_Kyprianou_Ch04_exercise41MeasurableGridInfimumV26
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

open Kyprianou.Ch04
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal inferInstance) (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) (q : ℕ → NNReal) (h : NNReal) :
    ∀ᵐ w ∂P, volume {s : ℝ | 0 ≤ s ∧ L.X s.toNNReal w +
      (⨅ k : ℕ, (L.X (s.toNNReal + min (q k) h) w - L.X s.toNNReal w)) = 0} = 0 := by
  exact exercise41FutureFunctionalOccupationV26 P F L hBV hd
    (fun f => ⨅ k : ℕ, f (min (q k) h)) (exercise41MeasurableGridInfimumV26 q h)