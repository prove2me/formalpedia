-- Prove2me | solution 1 for Kyprianou.Ch02.finitePoissonTimeMarkCellIntensity
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:29:48.768372+00:00
-- url     : https://prove2.me/submissions/c0b5365b-0dd2-450f-ac2d-98e626792d82

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory LevyStochCalc.Poisson
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem finitePoissonTimeMarkCellIntensity
    {E : Type} [MeasurableSpace E]
    (ν : Measure E) (s : ℕ → Set E)
    (hs_meas : ∀ m, MeasurableSet (s m))
    (hs_fin : ∀ m, ν (s m) < ⊤) :
    ∀ q : ℕ × ℕ,
      LevyStochCalc.Poisson.referenceIntensity ν
        (Set.Ico (q.1 : ℝ) (q.1 + 1) ×ˢ s q.2) ≠ ⊤ := by
  intro q
  refine ne_top_of_le_ne_top ?_ (Measure.prod_prod_le _ _)
  refine ENNReal.mul_ne_top ?_ (hs_fin q.2).ne
  refine ne_top_of_le_ne_top ?_ (Measure.restrict_apply_le _ _)
  simp

end Kyprianou.Ch02

theorem solution
    {E : Type} [MeasurableSpace E]
    (ν : Measure E) (s : ℕ → Set E)
    (hs_meas : ∀ m, MeasurableSet (s m))
    (hs_fin : ∀ m, ν (s m) < ⊤) :
    ∀ q : ℕ × ℕ,
      LevyStochCalc.Poisson.referenceIntensity ν
        (Set.Ico (q.1 : ℝ) (q.1 + 1) ×ˢ s q.2) ≠ ⊤ :=
  Kyprianou.Ch02.finitePoissonTimeMarkCellIntensity ν s hs_meas hs_fin
