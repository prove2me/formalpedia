-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_expNeg_setLintegral
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T09:28:51.36433+00:00
-- url     : https://prove2.me/submissions/6d1da7d9-844f-4ceb-a03d-4366653a9005

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution (a : Real) (ha : 0 ≤ a) :
    (∫⁻ t in Set.Ici (0 : Real), ENNReal.ofReal (Real.exp (-a * t)) ∂volume) =
      (ENNReal.ofReal a)⁻¹ := by
  by_cases ha0 : a = 0
  · subst ha0
    simp [Real.volume_Ici]
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hInt : IntegrableOn (fun t : Real => Real.exp (-a * t)) (Set.Ici (0 : Real)) volume := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact integrableOn_exp_mul_Ioi (show (-a) < 0 by linarith) 0
    have h1 : ∫ x in Set.Ioi (0 : Real), Real.exp (-a * x) = a⁻¹ := by
      have h := integral_exp_mul_Ioi (show (-a) < 0 by linarith) (0 : Real)
      simpa [neg_div_neg_eq, one_div] using h
    rw [← ofReal_integral_eq_lintegral_ofReal hInt (by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      exact Real.exp_nonneg _)]
    rw [integral_Ici_eq_integral_Ioi, h1]
    simp [ENNReal.ofReal_inv_of_pos ha']
