-- Prove2me | solution 1 for Kyprianou.Ch04.physicalMarkIndicatorWindowIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:29:47.932435+00:00
-- url     : https://prove2.me/submissions/803e905f-aadd-4fe5-be42-d09bd9a35e41

import Mathlib
open MeasureTheory Set
set_option autoImplicit false

/-- A marked indicator on the full time window is exactly the band set integral. -/
theorem solution (R : Measure (ℝ × ℝ)) (T : ℝ) (B : Set ℝ)
    (hB : MeasurableSet B) (k : ℝ × ℝ → ℝ) :
    (∫ z in Icc 0 T ×ˢ (univ : Set ℝ),
      B.indicator (fun x => k (z.1,x)) z.2 ∂ R) =
    ∫ z in Icc 0 T ×ˢ B, k z ∂ R := by
  have he : (fun z : ℝ × ℝ => B.indicator (fun x => k (z.1,x)) z.2) =
      (univ ×ˢ B).indicator k := by
    funext z
    by_cases hz : z.2 ∈ B
    · rw [indicator_of_mem hz,indicator_of_mem (show z ∈ univ ×ˢ B from ⟨mem_univ _,hz⟩)]
    · rw [indicator_of_notMem hz,indicator_of_notMem (show z ∉ univ ×ˢ B from fun h => hz h.2)]
  rw [he,integral_indicator (MeasurableSet.univ.prod hB),
    Measure.restrict_restrict (MeasurableSet.univ.prod hB)]
  simp [prod_inter_prod,inter_comm]
