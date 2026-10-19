-- Prove2me | solution 1 for OAI.Problem356.densityMeasure_sum_weighted_squares
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:23:03.693285+00:00
-- url     : https://prove2.me/submissions/200756ac-ad53-4b48-9cd9-954063bb5220

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling

open OAI OAI.Problem356
universe uIndex uX
open MeasureTheory
open scoped BigOperators


theorem solution {ι : Type uIndex}
    (s : Finset ι) (a : ι → ℝ) (g : ι → E3 → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hgm : ∀ i ∈ s, Measurable (g i)) :
    densityMeasure (fun x => ∑ i ∈ s, a i * (g i x) ^ 2) =
      ∑ i ∈ s, ENNReal.ofReal (a i) • densityMeasure (fun x => (g i x) ^ 2) := by
  ext A hA
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, densityMeasure, withDensity_apply _ hA, smul_eq_mul]
  have hpt : ∀ x, ENNReal.ofReal (∑ i ∈ s, a i * (g i x) ^ 2) =
      ∑ i ∈ s, ENNReal.ofReal (a i) * ENNReal.ofReal ((g i x) ^ 2) := by
    intro x
    rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => mul_nonneg (ha i hi) (sq_nonneg _))]
    exact Finset.sum_congr rfl (fun i hi => ENNReal.ofReal_mul (ha i hi))
  simp_rw [hpt]
  rw [lintegral_finsetSum s (fun i hi => (((hgm i hi).pow_const 2).ennreal_ofReal).const_mul _)]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  exact lintegral_const_mul _ ((hgm i hi).pow_const 2).ennreal_ofReal

