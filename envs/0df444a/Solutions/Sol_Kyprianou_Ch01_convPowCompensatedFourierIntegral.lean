-- Prove2me | solution 1 for Kyprianou.Ch01.convPowCompensatedFourierIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:15:31.956342+00:00
-- url     : https://prove2.me/submissions/a4fbb06c-d577-4b2c-82dd-6b0c860053c7

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_transforms
import Theorems.Thm_Kyprianou_Ch01_convPowCharFun
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex QueueingFundamentals.MG1
set_option autoImplicit false
/-! Fourier integral for arbitrary convolution powers; all powers remain probability laws. -/
theorem solution
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (n : ℕ) (xi : ℝ) :
    (∫ x : ℝ,
      (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1)
        ∂(QueueingFundamentals.MG1.convPow jumpLaw n)) =
      (charFun jumpLaw xi) ^ n - 1 := by
  have hprob : ∀ n : ℕ,
      IsProbabilityMeasure (QueueingFundamentals.MG1.convPow jumpLaw n) := by
    intro k
    induction k with
    | zero =>
        dsimp [QueueingFundamentals.MG1.convPow]
        exact Measure.dirac.isProbabilityMeasure
    | succ k hk =>
        letI := hk
        dsimp [QueueingFundamentals.MG1.convPow]
        exact Measure.probabilitymeasure_of_probabilitymeasures_conv _ _
  letI : IsProbabilityMeasure (QueueingFundamentals.MG1.convPow jumpLaw n) := hprob n
  have hmeas : Measurable (fun x : ℝ =>
      Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I)) := by
    fun_prop
  have hint : Integrable (fun x : ℝ =>
      Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I))
      (QueueingFundamentals.MG1.convPow jumpLaw n) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable 1
    filter_upwards [] with x
    simp [Complex.norm_exp, Complex.mul_re]
  rw [integral_sub hint (integrable_const 1)]
  rw [← charFun_apply_real]
  rw [Kyprianou.Ch01.convPowCharFun]
  simp
