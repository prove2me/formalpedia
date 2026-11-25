-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46QueueLaplaceExponentV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T20:42:38.654678+00:00
-- url     : https://prove2.me/submissions/a9684270-d65a-4c0f-83b3-8b9c72d8759d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_laplace_exponent_rearrangement_of_integrable
import Theorems.Thm_AvramDividend_Classical_bv_exponential_jump_integrable_nonneg
import Theorems.Thm_AvramDividend_Classical_bv_compensation_integrable
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P G)
    (hBV : L.BoundedVariation) (hDrift : L.drift = 1)
    (lambda : Real) (hlambda : 0 < lambda)
    (service : Measure Real) [IsProbabilityMeasure service]
    (hInputLaw : L.ν = ENNReal.ofReal lambda • service.map (fun x : Real => -x))
    (theta : Real) (htheta : 0 ≤ theta) :
    L.ψ theta = theta - lambda *
      (∫ y : Real, (1 - Real.exp (-theta * y)) ∂service) := by
  have hneg : ∀ᵐ y ∂L.ν, y ∈ Iio (0 : Real) := by
    rw [ae_iff]
    change L.ν {y | ¬ y < 0} = 0
    have hs : {y : Real | ¬ y < 0} = Ici 0 := by
      ext y
      exact not_lt
    rw [hs]
    exact L.ν_Ici
  rw [bv_laplace_exponent_rearrangement_of_integrable L hBV theta
    (bv_exponential_jump_integrable_nonneg L hBV theta htheta)
    (bv_compensation_integrable L hBV theta), hDrift, one_mul,
    Measure.restrict_eq_self_of_ae_mem hneg, hInputLaw, integral_smul_measure,
    ENNReal.toReal_ofReal hlambda.le, smul_eq_mul]
  rw [integral_map (φ := fun x : Real => -x) (measurable_id.neg.aemeasurable)
    (by fun_prop : AEStronglyMeasurable (fun y : Real => Real.exp (theta * y) - 1)
      (service.map (fun x : Real => -x)))]
  have he : (fun y : Real => Real.exp (theta * -y) - 1) =
      fun y => -(1 - Real.exp (-theta * y)) := by
    funext y
    rw [mul_neg, neg_mul]
    ring
  rw [he, integral_neg]
  ring
