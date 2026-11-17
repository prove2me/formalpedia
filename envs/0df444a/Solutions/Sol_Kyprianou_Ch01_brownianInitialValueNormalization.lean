-- Prove2me | solution 1 for Kyprianou.Ch01.brownianInitialValueNormalization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:17:08.883064+00:00
-- url     : https://prove2.me/submissions/232e67a9-44d5-4d09-8ae5-e32342a4e7ce

import Mathlib.Probability.BrownianMotion.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal X P)
    (hzero : ∀ᵐ ω ∂P, X 0 ω = 0) :
    IsPreBrownianReal (fun t ω => X t ω - X 0 ω) P := by
  refine hB.congr ?_
  intro t
  filter_upwards [hzero] with ω hz
  simp [hz]
