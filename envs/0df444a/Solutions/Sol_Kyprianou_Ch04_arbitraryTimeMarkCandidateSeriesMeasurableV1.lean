-- Prove2me | solution 1 for Kyprianou.Ch04.arbitraryTimeMarkCandidateSeriesMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:32:43.767784+00:00
-- url     : https://prove2.me/submissions/671e8c8b-2180-46ee-8962-2e8dfbb607b6

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

namespace Kyprianou.Ch04
theorem _root_.solution (time : ℕ → (NNReal → ℝ) → NNReal)
    (mark : ℕ → (NNReal → ℝ) → ℝ)
    (ht : ∀ k, Measurable (time k)) (hm : ∀ k, Measurable (mark k))
    (D : Set (ℝ × ℝ)) (hD : MeasurableSet D) :
    Measurable (fun Y : NNReal → ℝ => ∑' k : ℕ,
      if 0 < time k Y ∧ mark k Y ≠ 0 ∧
        ((time k Y : ℝ), mark k Y) ∈ D ∧
        (∀ j : ℕ, j < k → time j Y ≠ time k Y)
      then (1 : ENNReal) else 0) := by
  refine Measurable.ennreal_tsum fun k => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  have hk := ht k
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_))
  · first
      | exact measurableSet_lt measurable_const (measurable_coe_nnreal_real.comp hk)
      | exact measurableSet_lt measurable_const hk
  · exact (measurableSet_eq_fun (hm k) measurable_const).compl
  · exact ((measurable_coe_nnreal_real.comp hk).prodMk (hm k)) hD
  · show MeasurableSet {a : NNReal → ℝ | ∀ j < k, time j a ≠ time k a}
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (measurableSet_eq_fun (ht j) hk).compl

end Kyprianou.Ch04

