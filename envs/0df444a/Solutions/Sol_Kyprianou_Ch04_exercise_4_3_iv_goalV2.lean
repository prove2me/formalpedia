-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_3_iv_goalV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T07:48:43.838813+00:00
-- url     : https://prove2.me/submissions/515a7501-0235-4a73-930a-bf41008299a2

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_3Certification
import Theorems.Thm_Kyprianou_Ch04_bvUnitMarginalRealExponentialMoment
import Theorems.Thm_Kyprianou_Ch04_discountedExponentialUnitMoment
open MeasureTheory ProbabilityTheory Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The unit exponential moment uniquely determines the discount rate. -/
theorem solution : certificate_ex4_3_iv := by
  unfold certificate_ex4_3_iv
  intro Omega m P pProb F X hLevy hAdapted T hTriplet hBV hNonLattice
  intro f hf lam hlam hEigen hIntegrable beta hEq hTail
  simp_rw [hEq] at hEigen hIntegrable
  obtain ⟨hi, hm⟩ := discountedExponentialUnitMoment P F X
    (fun w => by simp [hLevy.start_zero]) beta lam hEigen
  apply Real.exp_injective
  rw [← hm]
  exact bvUnitMarginalRealExponentialMoment P (X 1)
    ((hAdapted 1).mono (F.le 1) le_rfl) T
    (fun theta => by simpa using hTriplet 1 theta) hBV beta hi
    (by simpa using hIntegrable 0)
