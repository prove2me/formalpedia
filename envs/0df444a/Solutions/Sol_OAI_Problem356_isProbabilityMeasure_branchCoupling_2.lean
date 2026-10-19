-- Prove2me | solution 2 for OAI.Problem356.isProbabilityMeasure_branchCoupling
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:00:42.303251+00:00
-- url     : https://prove2.me/submissions/ed2b7a53-d845-4bf9-a79c-5acb5861f243

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/BranchCoupling.lean:L119-L133
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.isProbabilityMeasure_branchCoupling. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling

-- ---- from OAI.Analysis.CoulombTransport.BranchCoupling ----
namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356

lemma measurable_branchGraph {f g h : E3 → E3}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measurable (branchGraph f g h) := hf.prodMk (hg.prodMk hh)

lemma isProbabilityMeasure_branchCoupling (nu : Measure E3) [IsProbabilityMeasure nu]
    {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) : IsProbabilityMeasure (branchCoupling nu H1 H2 H3 H4) := by
  constructor
  simp only [branchCoupling, Measure.smul_apply, Measure.add_apply,
    Measure.map_apply (measurable_branchGraph measurable_id h1 h2) MeasurableSet.univ,
    Measure.map_apply (measurable_branchGraph h1 h2 measurable_id) MeasurableSet.univ,
    Measure.map_apply (measurable_branchGraph h2 measurable_id h1) MeasurableSet.univ,
    Measure.map_apply (measurable_branchGraph measurable_id h3 h4) MeasurableSet.univ,
    Measure.map_apply (measurable_branchGraph h3 h4 measurable_id) MeasurableSet.univ,
    Measure.map_apply (measurable_branchGraph h4 measurable_id h3) MeasurableSet.univ,
    Set.preimage_univ, measure_univ, smul_eq_mul]
  norm_num only [one_div, show (1 + 1 + 1 + 1 + 1 + 1 : ℝ≥0∞) = 6 by norm_num]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open MeasureTheory
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.Problem356.isProbabilityMeasure_branchCoupling := @_root_.OAI.Problem356.isProbabilityMeasure_branchCoupling
