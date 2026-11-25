-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_ae_abs_tail_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:27:13.662793+00:00
-- url     : https://prove2.me/submissions/0e689c16-fca7-43f7-865a-6e5019744279

import Mathlib
open MeasureTheory Filter Topology
set_option autoImplicit false

/-- Almost-sure convergence of measurable real variables implies
the real-valued probability tail condition in the chapter definition. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (Q : Nat → Ω → Real) (I : Ω → Real)
    (hQ : ∀ n, AEStronglyMeasurable (Q n) P)
    (hLim : ∀ᵐ w ∂P,
      Tendsto (fun n => Q n w) atTop (nhds (I w)))
    (epsilon : Real) (heps : 0 < epsilon) :
    Tendsto (fun n => (P {w : Ω | epsilon ≤ |Q n w - I w|}).toReal)
      atTop (nhds 0) := by
  have h := tendstoInMeasure_of_tendsto_ae hQ hLim
  simpa only [Real.norm_eq_abs, measureReal_def] using
    (tendstoInMeasure_iff_measureReal_norm.mp h epsilon heps)
