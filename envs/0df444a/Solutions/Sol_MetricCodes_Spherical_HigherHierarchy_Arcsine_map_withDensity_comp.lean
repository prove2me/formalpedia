-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Arcsine.map_withDensity_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/8bd40e94-1176-4b2a-9648-639718f9e95a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal Interval
open MetricCodes.Spherical.HigherHierarchy.Arcsine
namespace MetricCodes.Spherical.HigherHierarchy.Arcsine
theorem _root_.solution {μ : Measure ℝ} {f : ℝ → ℝ}
    {w : ℝ → ℝ≥0∞} (hf : Measurable f) (hw : Measurable w) :
    (μ.withDensity (w ∘ f)).map f = (μ.map f).withDensity w := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs),
    withDensity_apply _ hs, ← lintegral_indicator hs,
    lintegral_map (hw.indicator hs) hf]
  rw [← lintegral_indicator (hf hs)]
  apply lintegral_congr
  intro t
  by_cases ht : f t ∈ s <;> simp [Function.comp_apply, ht]
end MetricCodes.Spherical.HigherHierarchy.Arcsine
