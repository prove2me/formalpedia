-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46MM1TrafficIntegratedTailV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:00:16.913571+00:00
-- url     : https://prove2.me/submissions/28df7936-11c5-4b2f-9c15-e2dc70f64c62

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46NegativeExponentialTailV1
import Theorems.Thm_AvramDividend_Classical_original_negative_tail_unweighted_layercake
import Theorems.Thm_AvramDividend_Classical_positiveLIntegral_exp_neg_mul_Ioi
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (lambda mu : Real) (hlambda : 0 < lambda) (hmu : lambda < mu)
    (nu : Measure Real)
    (hnu : nu = ((volume : Measure Real).restrict (Iio 0)).withDensity
      (fun y => ENNReal.ofReal (lambda*mu*Real.exp (mu*y)))) :
    let rho := ∫⁻ y : Real, ENNReal.ofReal (-y) ∂nu
    rho = ENNReal.ofReal (lambda/mu) ∧
      ((volume : Measure Real).restrict (Ioi 0)).withDensity
        (fun x => nu (Iio (-x)) / rho) =
      ((volume : Measure Real).restrict (Ioi 0)).withDensity
        (fun x => ENNReal.ofReal (mu*Real.exp (-mu*x))) := by
  dsimp only
  have hm : 0 < mu := hlambda.trans hmu
  have ht (x : Real) (hx : 0 ≤ x) :
      nu (Iio (-x)) = ENNReal.ofReal (lambda * Real.exp (-mu*x)) := by
    rw [hnu]
    exact Kyprianou.Ch04.exercise46NegativeExponentialTailV1 lambda mu hlambda hm x hx
  have hs : nu (Ici (0 : Real)) = 0 := by
    rw [hnu, withDensity_apply _ measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
    have he : Ici (0 : Real) ∩ Iio 0 = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_Ici, mem_Iio, mem_empty_iff_false, iff_false]
      exact fun h => (not_lt_of_ge h.1) h.2
    simp [he]
  have hr : (∫⁻ y : Real, ENNReal.ofReal (-y) ∂nu) = ENNReal.ofReal (lambda/mu) := by
    rw [AvramDividend.Classical.original_negative_tail_unweighted_layercake nu hs]
    calc
      _ = ∫⁻ t in Ioi (0 : Real), ENNReal.ofReal lambda *
          ENNReal.ofReal (Real.exp (-mu*t)) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        rw [ht x hx.le, ENNReal.ofReal_mul hlambda.le]
      _ = _ := by
        rw [lintegral_const_mul _ (by fun_prop),
          AvramDividend.Classical.positiveLIntegral_exp_neg_mul_Ioi mu 0 hm,
          ← ENNReal.ofReal_mul hlambda.le]
        simp [div_eq_mul_inv]
  refine ⟨hr, ?_⟩
  rw [hr]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [ht x hx.le, ← ENNReal.ofReal_div_of_pos (div_pos hlambda hm)]
  congr 1
  field_simp [hlambda.ne', hm.ne']
  <;> ring
