-- Prove2me | solution 1 for GlobalTheory.LocRep.locallyIntegrable_rep
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T04:15:01.230832+00:00
-- url     : https://prove2.me/submissions/5d0b1218-50ac-4eda-927d-58f6f11f2b19

import Mathlib
open MeasureTheory
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ}


theorem solution [LocallyCompactSpace G]
    (hloc : ∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖) (v : K) :
    LocallyIntegrable (ι v) μ := by
  apply locallyIntegrable_iff.mpr; intro C hC; obtain ⟨M,hM⟩ := hloc C hC; exact (hM v).1
