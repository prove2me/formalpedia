-- Prove2me | solution 1 for GlobalTheory.LocRep.rep_add
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T04:15:12.045972+00:00
-- url     : https://prove2.me/submissions/1b7ed2e3-15bb-4d8c-a96f-c2ab6a46ad39

import Mathlib
open MeasureTheory
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ}


theorem solution (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) (v w : K) :
    ι (v + w) =ᵐ[μ] fun x => ι v x + ι w x := by
  simpa using hlin 1 v w
