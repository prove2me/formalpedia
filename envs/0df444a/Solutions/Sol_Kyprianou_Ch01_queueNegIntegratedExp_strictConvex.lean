-- Prove2me | solution 1 for Kyprianou.Ch01.queueNegIntegratedExp_strictConvex
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T11:29:45.655984+00:00
-- url     : https://prove2.me/submissions/a8df7478-1588-4baa-b6b1-8384d4960530

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_positiveIntegral_of_ae_pos
import Theorems.Thm_Kyprianou_Ch01_queueExpDeficit_integrable
import Theorems.Thm_Kyprianou_Ch01_queueExpJensenGap_ae_pos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
set_option autoImplicit false

/-- Strict convexity of an integrated positive-support exponential deficit. -/
theorem solution
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0) :
    StrictConvexOn ℝ (Set.Ici (0 : ℝ))
      (fun theta : ℝ => -(∫ x : ℝ, (1 - Real.exp (-theta * x)) ∂F)) := by
  refine ⟨convex_Ici (0 : ℝ), ?_⟩
  intro u hu v hv huv a b ha hb hab
  have hm : 0 ≤ a * u + b * v := by
    have hpa : 0 ≤ a := le_of_lt ha
    have hpb : 0 ≤ b := le_of_lt hb
    nlinarith [mul_nonneg hpa hu, mul_nonneg hpb hv]
  have hiu := Kyprianou.Ch01.queueExpDeficit_integrable F hpositive u hu
  have hiv := Kyprianou.Ch01.queueExpDeficit_integrable F hpositive v hv
  have him := Kyprianou.Ch01.queueExpDeficit_integrable F hpositive (a * u + b * v) hm
  let D : ℝ → ℝ := fun z =>
    (1 - Real.exp (-(a * u + b * v) * z)) -
      (a * (1 - Real.exp (-u * z)) + b * (1 - Real.exp (-v * z)))
  have hdi : Integrable D F := by
    exact him.sub ((hiu.const_mul a).add (hiv.const_mul b))
  have hdp : ∀ᵐ z ∂F, 0 < D z := by
    simpa only [D] using
      (Kyprianou.Ch01.queueExpJensenGap_ae_pos
        F hpositive u v huv a b ha hb hab)
  have hDpos : 0 < ∫ z, D z ∂F :=
    Kyprianou.Ch01.positiveIntegral_of_ae_pos F D hdi hdp
  simp only [smul_eq_mul]
  have hDvalue :
      (∫ z, D z ∂F) =
        (∫ z : ℝ, (1 - Real.exp (-(a * u + b * v) * z)) ∂F) -
        (a * ∫ z : ℝ, (1 - Real.exp (-u * z)) ∂F) -
        (b * ∫ z : ℝ, (1 - Real.exp (-v * z)) ∂F) := by
    dsimp [D]
    have hsub := integral_sub him ((hiu.const_mul a).add (hiv.const_mul b))
    have hadd := integral_add (hiu.const_mul a) (hiv.const_mul b)
    simp only [Pi.sub_apply, Pi.add_apply, integral_const_mul] at hsub hadd
    rw [hsub, hadd]
    ring
  rw [hDvalue] at hDpos
  linarith
