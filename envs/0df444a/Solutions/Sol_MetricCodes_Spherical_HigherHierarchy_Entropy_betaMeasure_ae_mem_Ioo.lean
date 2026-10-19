-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Entropy.betaMeasure_ae_mem_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/6f31f00c-6aa4-461d-aa37-846151a02c65

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
theorem _root_.solution {α β : ℝ} :
    ∀ᵐ x ∂(betaMeasure α β), x ∈ Set.Ioo (0 : ℝ) 1 := by
  change ∀ᵐ x ∂(volume.withDensity (betaPDF α β)), x ∈ Set.Ioo (0 : ℝ) 1
  have hmeas : Measurable (betaPDF α β) :=
    (measurable_betaPDFReal α β).ennreal_ofReal
  rw [ae_withDensity_iff hmeas]
  filter_upwards [] with x hx
  by_contra h
  have h' : ¬ (0 < x ∧ x < 1) := by simpa using h
  exact hx (by simp [betaPDF, betaPDFReal, h'])
end MetricCodes.Spherical.HigherHierarchy.Entropy
