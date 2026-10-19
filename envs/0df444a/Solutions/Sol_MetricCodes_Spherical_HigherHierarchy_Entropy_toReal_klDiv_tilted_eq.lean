-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Entropy.toReal_klDiv_tilted_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/468f360b-6d07-4e4a-a27e-b4ef0508ea34

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
theorem _root_.solution {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α → ℝ} (hμν : μ ≪ ν)
    (hfμ : Integrable f μ)
    (hfν : Integrable (fun x => Real.exp (f x)) ν)
    (hllr : Integrable (llr μ ν) μ) :
    (InformationTheory.klDiv μ (ν.tilted f)).toReal =
      (InformationTheory.klDiv μ ν).toReal - ∫ x, f x ∂μ +
        Real.log (∫ x, Real.exp (f x) ∂ν) := by
  letI : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted hfν
  have hac : μ ≪ ν.tilted f :=
    hμν.trans (absolutelyContinuous_tilted hfν)
  rw [InformationTheory.toReal_klDiv_of_measure_eq hac (by simp),
    InformationTheory.toReal_klDiv_of_measure_eq hμν (by simp)]
  exact integral_llr_tilted_right hμν hfμ hfν hllr
end MetricCodes.Spherical.HigherHierarchy.Entropy
