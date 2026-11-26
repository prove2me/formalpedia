-- Prove2me | solution 1 for Kyprianou.Ch05.positiveLevyDeficitIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:00:53.74904+00:00
-- url     : https://prove2.me/submissions/b6c70785-036c-4e37-b4a1-b6eb763a24d7

import Mathlib.MeasureTheory.Integral.IntegrableOn
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (mu : Measure Real)
    (hm : (∫⁻ x in Set.Ioi (0 : Real),
      ENNReal.ofReal (min (1 : Real) x) ∂mu) < ⊤)
    (t : Real) (ht : 0 < t) :
    IntegrableOn (fun x : Real => 1 - Real.exp (-t*x)) (Set.Ioi 0) mu := by
  refine ⟨(by fun_prop), ?_⟩
  have hnn : 0 ≤ᵐ[mu.restrict (Set.Ioi (0 : Real))]
      (fun x => 1 - Real.exp (-t*x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith [mul_pos ht hx]))
  rw [hasFiniteIntegral_iff_ofReal hnn]
  calc
    _ ≤ ∫⁻ x in Set.Ioi (0 : Real),
        ENNReal.ofReal (max 1 t) * ENNReal.ofReal (min 1 x) ∂mu := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [← ENNReal.ofReal_mul (le_trans zero_le_one (le_max_left 1 t))]
      apply ENNReal.ofReal_le_ofReal
      by_cases h : x ≤ 1
      · rw [min_eq_right h]
        have he := Real.add_one_le_exp (-t*x)
        have hm' := mul_le_mul_of_nonneg_right (le_max_right 1 t) hx.le
        linarith
      · rw [min_eq_left (le_of_not_ge h), mul_one]
        have he := Real.exp_pos (-t*x)
        linarith [le_max_left (1 : Real) t]
    _ = ENNReal.ofReal (max 1 t) *
        (∫⁻ x in Set.Ioi (0 : Real), ENNReal.ofReal (min 1 x) ∂mu) := by
      rw [lintegral_const_mul _ (by fun_prop)]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hm
