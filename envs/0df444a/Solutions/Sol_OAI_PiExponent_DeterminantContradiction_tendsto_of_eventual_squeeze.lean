-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.tendsto_of_eventual_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:34:14.767118+00:00
-- url     : https://prove2.me/submissions/b750fe5b-7146-454e-80bc-5883daf31f85

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open Filter Topology

theorem solution {f lower upper : Real → Real} {L : Real}
    (hbound : ∀ᶠ x : Real in atTop, lower x ≤ f x ∧ f x ≤ upper x)
    (hlower : Tendsto lower atTop (nhds L)) (hupper : Tendsto upper atTop (nhds L)) :
    Tendsto f atTop (nhds L) := by
  apply Filter.Tendsto.squeeze' hlower hupper
  · exact hbound.mono fun x hx => hx.1
  · exact hbound.mono fun x hx => hx.2