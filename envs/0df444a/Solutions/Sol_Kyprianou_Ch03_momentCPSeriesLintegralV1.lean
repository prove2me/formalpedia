-- Prove2me | solution 1 for Kyprianou.Ch03.momentCPSeriesLintegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:53:54.089641+00:00
-- url     : https://prove2.me/submissions/7ea4b6d3-c096-478f-bbb2-2df88b645159

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
set_option autoImplicit false
theorem solution
    (mu : Measure Real) [IsFiniteMeasure mu]
    (f : Real → ENNReal) :
    (∫⁻ x, f x ∂(KSATSingleFlip.Connect.compoundPoisson mu)) =
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(mu Set.univ).toReal) /
        (n.factorial : ℝ)) * (∫⁻ x, f x ∂(KSATSingleFlip.Connect.convPow mu n)) := by
  unfold KSATSingleFlip.Connect.compoundPoisson
  rw [if_neg (measure_ne_top mu Set.univ), lintegral_sum_measure]
  simp_rw [lintegral_smul_measure, smul_eq_mul]
