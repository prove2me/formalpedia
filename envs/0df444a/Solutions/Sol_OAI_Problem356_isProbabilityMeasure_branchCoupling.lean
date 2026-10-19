-- Prove2me | solution 1 for OAI.Problem356.isProbabilityMeasure_branchCoupling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:14:01.950989+00:00
-- url     : https://prove2.me/submissions/6d0ee049-45d8-4690-a45d-a560794c44e6

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling

open OAI OAI.Problem356
open MeasureTheory
open scoped ENNReal


theorem solution (nu : Measure E3) [IsProbabilityMeasure nu]
    {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) : IsProbabilityMeasure (branchCoupling nu H1 H2 H3 H4) := by
  have hg : ∀ f g h : E3 → E3, Measurable f → Measurable g → Measurable h →
      Measurable (branchGraph f g h) := fun f g h hf hg hh => hf.prodMk (hg.prodMk hh)
  constructor
  simp only [branchCoupling, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
  rw [Measure.map_apply (hg _ _ _ measurable_id h1 h2) MeasurableSet.univ,
    Measure.map_apply (hg _ _ _ h1 h2 measurable_id) MeasurableSet.univ,
    Measure.map_apply (hg _ _ _ h2 measurable_id h1) MeasurableSet.univ,
    Measure.map_apply (hg _ _ _ measurable_id h3 h4) MeasurableSet.univ,
    Measure.map_apply (hg _ _ _ h3 h4 measurable_id) MeasurableSet.univ,
    Measure.map_apply (hg _ _ _ h4 measurable_id h3) MeasurableSet.univ]
  simp only [Set.preimage_univ, measure_univ]
  have : (1 : ℝ≥0∞) + 1 + 1 + 1 + 1 + 1 = 6 := by norm_num
  rw [this]
  exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)

