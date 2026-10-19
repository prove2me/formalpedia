-- Prove2me | solution 1 for OAI.RadialTransition.gibbs_bogoliubov
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:06:09.020985+00:00
-- url     : https://prove2.me/submissions/4c57dc7e-06a2-4ec6-a733-472de76a2ffd

import Mathlib
import Definitions.Def_OAIQWRTD000

section
-- module Solutions.OAIQW_RadialTransition.BoltzmannMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem boltzmannMeasure_probability {X : Type uX} [MeasurableSpace X] {μ : Measure X}
    {E : X → ℝ} (hi : Integrable (fun x => Real.exp (-E x)) μ)
    (hp : 0 < boltzmannPartition μ E) : IsProbabilityMeasure (boltzmannMeasure μ E) := by
  constructor
  rw [boltzmannMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall (fun x => (Real.exp_pos _).le))]
  change (ENNReal.ofReal (boltzmannPartition μ E))⁻¹ * ENNReal.ofReal (boltzmannPartition μ E) = 1
  rw [ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top]

theorem integral_boltzmann {X : Type uX} [MeasurableSpace X] {μ : Measure X}
    {E : X → ℝ} (hE : Measurable E) (f : X → ℝ) :
    (∫ x, f x ∂boltzmannMeasure μ E) =
      (boltzmannPartition μ E)⁻¹ * ∫ x, Real.exp (-E x) * f x ∂μ := by
  have hw : Measurable (fun x => ENNReal.ofReal (Real.exp (-E x))) :=
    (Real.measurable_exp.comp hE.neg).ennreal_ofReal
  rw [boltzmannMeasure, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul
      hw (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have hZ : 0 ≤ boltzmannPartition μ E := integral_nonneg (fun _ => (Real.exp_pos _).le)
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]

theorem integrable_boltzmann {X : Type uX} [MeasurableSpace X] {μ : Measure X}
    {E f : X → ℝ} (hE : Measurable E)
    (hi : Integrable (fun x => Real.exp (-E x) * f x) μ)
    (hp : 0 < boltzmannPartition μ E) : Integrable f (boltzmannMeasure μ E) := by
  have hw : Measurable (fun x => ENNReal.ofReal (Real.exp (-E x))) :=
    (Real.measurable_exp.comp hE.neg).ennreal_ofReal
  apply Integrable.smul_measure
  · apply (integrable_withDensity_iff_integrable_smul'
      hw
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
    simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul] using hi
  · exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hp)

theorem gibbs_bogoliubov_oai {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {E F : X → ℝ} (hE : Measurable E)
    (hiE : Integrable (fun x => Real.exp (-E x)) μ)
    (hiF : Integrable (fun x => Real.exp (-F x)) μ)
    (hpE : 0 < ∫ x, Real.exp (-E x) ∂μ) (hpF : 0 < ∫ x, Real.exp (-F x) ∂μ)
    (hi : Integrable (fun x => F x - E x)
      ((ENNReal.ofReal (∫ x, Real.exp (-E x) ∂μ))⁻¹ •
        μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-E x))))) :
    Real.log (∫ x, Real.exp (-E x) ∂μ) - Real.log (∫ x, Real.exp (-F x) ∂μ) ≤
      ∫ x, F x - E x ∂((ENNReal.ofReal (∫ x, Real.exp (-E x) ∂μ))⁻¹ •
        μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-E x)))) := by
  change 0 < boltzmannPartition μ E at hpE
  change 0 < boltzmannPartition μ F at hpF
  change Integrable (fun x => F x - E x) (boltzmannMeasure μ E) at hi
  show Real.log (boltzmannPartition μ E) - Real.log (boltzmannPartition μ F) ≤
      ∫ x, F x - E x ∂boltzmannMeasure μ E
  let := boltzmannMeasure_probability hiE hpE
  have hexp : Integrable (fun x => Real.exp (-(F x - E x))) (boltzmannMeasure μ E) := by
    apply integrable_boltzmann hE _ hpE
    convert hiF using 1
    ext x
    rw [← Real.exp_add]
    congr 1
    ring
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall (fun x => mem_univ (-(F x - E x)))) hi.neg hexp
  rw [integral_neg, integral_boltzmann hE (fun x => Real.exp (-(F x - E x)))] at hj
  have he (x : X) : Real.exp (-E x) * Real.exp (-(F x - E x)) = Real.exp (-F x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he] at hj
  have hl := Real.log_le_log (Real.exp_pos _) hj
  change Real.log (Real.exp (-∫ x, F x - E x ∂boltzmannMeasure μ E)) ≤
    Real.log ((boltzmannPartition μ E)⁻¹ * boltzmannPartition μ F) at hl
  rw [Real.log_exp, Real.log_mul (inv_ne_zero hpE.ne') hpF.ne', Real.log_inv] at hl
  linarith

end RadialTransition

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.RadialTransition.gibbs_bogoliubov_oai.{u_1} := @OAI.RadialTransition.gibbs_bogoliubov_oai.{u_1}
