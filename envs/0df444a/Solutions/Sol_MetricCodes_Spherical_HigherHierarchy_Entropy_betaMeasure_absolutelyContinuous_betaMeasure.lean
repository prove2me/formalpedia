-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Entropy.betaMeasure_absolutelyContinuous_betaMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/008969a0-8c2e-4093-9bff-20d34ed0e779

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.Entropy
namespace MetricCodes.Spherical.HigherHierarchy.Entropy
theorem _root_.solution
    {α β γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) :
    betaMeasure α β ≪ betaMeasure γ δ := by
  intro s hs
  change (volume.withDensity (betaPDF γ δ)) s = 0 at hs
  change (volume.withDensity (betaPDF α β)) s = 0
  have hmeas₁ : Measurable (betaPDF α β) :=
    (measurable_betaPDFReal α β).ennreal_ofReal
  have hmeas₂ : Measurable (betaPDF γ δ) :=
    (measurable_betaPDFReal γ δ).ennreal_ofReal
  rw [withDensity_apply_eq_zero hmeas₂] at hs
  rw [withDensity_apply_eq_zero hmeas₁]
  apply measure_mono_null _ hs
  rintro x ⟨hx, hxs⟩
  refine ⟨?_, hxs⟩
  have hsupport : 0 < x ∧ x < 1 := by
    by_contra h
    exact hx (by simp [betaPDF, betaPDFReal, h])
  have hpos := betaPDFReal_pos hsupport.1 hsupport.2 hγ hδ
  intro hzero
  have hnonpos := ENNReal.ofReal_eq_zero.mp hzero
  exact (not_le_of_gt hpos) hnonpos
end MetricCodes.Spherical.HigherHierarchy.Entropy
