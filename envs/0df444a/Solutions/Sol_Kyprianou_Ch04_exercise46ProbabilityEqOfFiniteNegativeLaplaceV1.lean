-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46ProbabilityEqOfFiniteNegativeLaplaceV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:58:27.173793+00:00
-- url     : https://prove2.me/submissions/ea40af9a-c14f-437f-99bd-4e0a309e8762

import Mathlib
import Theorems.Thm_AvramDividend_Classical_measure_eq_of_pos_mgf_on_ray
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (nu eta : Measure Real) [IsProbabilityMeasure nu] [IsProbabilityMeasure eta]
    (hfin : ∀ s : Real, 0 < s →
      (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-s*x)) ∂nu) < ⊤)
    (heq : ∀ s : Real, 0 < s →
      (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-s*x)) ∂nu) =
      (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-s*x)) ∂eta)) :
    nu = eta := by
  let R : Real → Real := fun x => -x
  have hR : Measurable R := measurable_neg
  letI : IsProbabilityMeasure (nu.map R) := Measure.isProbabilityMeasure_map hR.aemeasurable
  letI : IsProbabilityMeasure (eta.map R) := Measure.isProbabilityMeasure_map hR.aemeasurable
  have hL (m : Measure Real) (s : Real) :
      (∫⁻ x, ENNReal.ofReal (Real.exp (s*x)) ∂m.map R) =
        ∫⁻ x, ENNReal.ofReal (Real.exp (-s*x)) ∂m := by
    rw [lintegral_map (by fun_prop) hR]
    congr 1
    funext x
    congr 2
    simp [R, mul_neg, neg_mul]
  have hI (m : Measure Real) (s : Real)
      (h : (∫⁻ x, ENNReal.ofReal (Real.exp (-s*x)) ∂m) < ⊤) :
      Integrable (fun x : Real => Real.exp (s*x)) (m.map R) :=
    (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
      (Eventually.of_forall fun x => (Real.exp_pos _).le)).mp
      (by rw [hL]; exact h.ne)
  have hM := AvramDividend.Classical.measure_eq_of_pos_mgf_on_ray
    (μ := nu.map R) (ν := eta.map R)
    (fun s hs => hI nu s (hfin s hs))
    (fun s hs => hI eta s (by rw [← heq s hs]; exact hfin s hs))
    (fun s hs => by
      rw [integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall fun x => (Real.exp_pos _).le) (by fun_prop),
        integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall fun x => (Real.exp_pos _).le) (by fun_prop),
        hL, hL, heq s hs])
  have h := congrArg (Measure.map R) hM
  simpa [Measure.map_map hR hR, R, Function.comp_def] using h
