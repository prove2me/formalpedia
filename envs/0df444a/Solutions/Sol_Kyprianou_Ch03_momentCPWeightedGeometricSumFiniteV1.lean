-- Prove2me | solution 1 for Kyprianou.Ch03.momentCPWeightedGeometricSumFiniteV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T13:07:16.381033+00:00
-- url     : https://prove2.me/submissions/91c7b8c0-9271-46e2-a7ba-500bb48eb14a

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
set_option autoImplicit false
theorem solution
    (a M : Real) (ha : 0 ≤ a) (r : ENNReal) (hr : r ≠ ⊤) :
    (∑' n : ℕ, ENNReal.ofReal (Real.exp (-M) / (n.factorial : ℝ)) *
      (ENNReal.ofReal a * r ^ n)) < ⊤ := by
  have hsum : HasSum (fun n : ℕ => Real.exp (-M) * a * (r.toReal ^ n / (n.factorial : ℝ)))
      (Real.exp (-M) * a * Real.exp r.toReal) := by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp r.toReal).mul_left (Real.exp (-M) * a)
  have he (n : ℕ) : ENNReal.ofReal (Real.exp (-M) / (n.factorial : ℝ)) *
      (ENNReal.ofReal a * r ^ n) =
        ENNReal.ofReal (Real.exp (-M) * a * (r.toReal ^ n / (n.factorial : ℝ))) := by
    have hp : r ^ n = ENNReal.ofReal (r.toReal ^ n) := by
      rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hr]
    rw [hp]
    rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  simp_rw [he]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum.summable, hsum.tsum_eq]
  exact ENNReal.ofReal_lt_top
