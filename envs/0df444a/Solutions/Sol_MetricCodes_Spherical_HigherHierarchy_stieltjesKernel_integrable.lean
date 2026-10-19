-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.stieltjesKernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/5fb4ab9e-f38f-466e-b1eb-f1e0626f31cf

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory
open scoped BigOperators Interval
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {x : ℝ} (hx : 0 ≤ x)
    (hpositive : ∀ᵐ t ∂μ, 0 < t) :
    Integrable (fun t : ℝ => t / (t + x)) μ := by
  apply (integrable_const (α := ℝ) (μ := μ) (c := (1 : ℝ))).mono'
    (measurable_id.div (measurable_id.add measurable_const)).aestronglyMeasurable
  filter_upwards [hpositive] with t ht
  have hden : 0 < t + x := by linarith
  have hnonneg : 0 ≤ t / (t + x) := div_nonneg ht.le hden.le
  simp only [Pi.div_apply, Pi.add_apply, id_eq]
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  simpa using (div_le_one hden).mpr (by linarith)
end MetricCodes.Spherical.HigherHierarchy
