-- Prove2me | solution 1 for Newton.core_indicator_eLpNorm_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:28:23.814235+00:00
-- url     : https://prove2.me/submissions/79a08504-fbe0-4c0f-8266-a42ecb32349c

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_Analysis_Convolution_Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_ContinuousDense
import Definitions.Def_Newton_Analysis_Convolution_ApproximateIdentity

set_option autoImplicit false
open MeasureTheory Complex NNReal SchwartzMap
open scoped ENNReal ContDiff Topology Pointwise
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    {p : ℝ≥0∞} {coreSet : Set (Fin n → ℝ)}
    (h_core_meas : MeasurableSet coreSet)
    {g : (Fin n → ℝ) → ℂ} {δ : ℝ}
    (h_bound :
      ∀ᵐ x ∂volume.restrict coreSet, ‖g x‖ ≤ δ) :
  eLpNorm (fun x => Set.indicator coreSet g x) p volume
    ≤ (volume coreSet) ^ (1 / p.toReal) * ENNReal.ofReal δ := by
  -- Move to the restricted measure on `coreSet` via the indicator equivalence.
  have h_indicator_eq :
      eLpNorm (fun x => Set.indicator coreSet g x) p volume
        = eLpNorm g p (volume.restrict coreSet) := by
    simpa using
      (eLpNorm_indicator_eq_eLpNorm_restrict
        (μ := volume) (p := p) (s := coreSet) (f := g) h_core_meas)
  -- Apply the general bound under an a.e. pointwise bound on the restricted measure.
  have h_le_restrict :
      eLpNorm g p (volume.restrict coreSet)
        ≤ (volume.restrict coreSet Set.univ) ^ (1 / p.toReal) * ENNReal.ofReal δ := by
    simpa using
      (eLpNorm_le_of_ae_bound (μ := volume.restrict coreSet) (p := p) (f := g) h_bound)
  -- Evaluate the total mass of the restricted measure on `univ`.
  have h_measure_univ : (volume.restrict coreSet) Set.univ = volume coreSet := by
    simp [Measure.restrict_apply]
  simpa [h_indicator_eq, h_measure_univ] using h_le_restrict
end Newton
