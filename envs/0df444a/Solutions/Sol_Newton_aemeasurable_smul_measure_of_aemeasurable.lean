-- Prove2me | solution 1 for Newton.aemeasurable_smul_measure_of_aemeasurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:35:45.592808+00:00
-- url     : https://prove2.me/submissions/d5a2a066-0c65-4935-a3ef-72fef9d19614

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Definitions.Def_Newton_Analysis_Convolution_Basic
import Definitions.Def_Newton_Analysis_Convolution_Minkowski
import Definitions.Def_Newton_Analysis_Convolution_Bounds

set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal ContDiff Pointwise
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    {α : Type*} [MeasurableSpace α]
    (f : α → ℝ≥0∞) (μ : Measure α) (c : ℝ≥0∞)
    (hf : AEMeasurable f μ) : AEMeasurable f (c • μ) := by
  rcases hf with ⟨g, hg_meas, hfg⟩
  refine ⟨g, hg_meas, ?_⟩
  have h_zero : μ {x | f x ≠ g x} = 0 := (ae_iff).1 hfg
  -- Scale the measure: null sets remain null for `c • μ`
  have h_zero' : (c • μ) {x | f x ≠ g x} = 0 := by
    -- Avoid `simp` turning equality into a disjunction via `mul_eq_zero`.
    -- Directly rewrite using `Measure.smul_apply` and `h_zero`.
    simp [Measure.smul_apply, h_zero]
  -- Turn the null-set statement back into an a.e. equality for `c • μ`.
  exact (ae_iff).2 h_zero'
end Newton
