-- Prove2me | solution 1 for Kyprianou.Ch03.stableFracMomentPositivePowerTailV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T16:04:03.44784+00:00
-- url     : https://prove2.me/submissions/802d078a-2a72-43cf-ba88-fa2b389734ae

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (c alpha eta : Real) :
    IntegrableOn (fun x : Real => c * x ^ (eta - 1 - alpha))
      (Set.Ici (1 : Real)) volume ↔ c = 0 ∨ eta < alpha := by
  by_cases hc : c = 0
  · simp [hc]
  · unfold IntegrableOn
    rw [integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc)]
    change IntegrableOn (fun x : ℝ => x^(eta-1-alpha)) (Ici (1 : ℝ)) volume ↔ _
    rw [integrableOn_Ici_iff_integrableOn_Ioi, integrableOn_Ioi_rpow_iff (by norm_num : (0:ℝ)<1)]
    simp only [hc, false_or]
    constructor <;> intro h <;> linarith
