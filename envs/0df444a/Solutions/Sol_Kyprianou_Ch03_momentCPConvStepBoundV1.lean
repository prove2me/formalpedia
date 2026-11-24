-- Prove2me | solution 1 for Kyprianou.Ch03.momentCPConvStepBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:53:58.689859+00:00
-- url     : https://prove2.me/submissions/43c87208-514e-4c02-bb3b-7e91a790f4c5

import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
set_option autoImplicit false
theorem solution
    (mu : Measure Real) [IsFiniteMeasure mu]
    (g : Real → Real) (hg : Kyprianou.Ch03.IsSubmultiplicative g)
    (hg_meas : Measurable g)
    (nu : Measure Real) [IsFiniteMeasure nu]
    (c : Real) (hc : 0 < c)
    (hsub : ∀ x y : Real, g (x + y) ≤ c * g x * g y) :
    (∫⁻ x, (fun x : ℝ => ENNReal.ofReal (g x)) x ∂(mu ∗ nu)) ≤
      ENNReal.ofReal c * (∫⁻ x, (fun x : ℝ => ENNReal.ofReal (g x)) x ∂mu) * (∫⁻ x, (fun x : ℝ => ENNReal.ofReal (g x)) x ∂nu) := by
  let f (x : ℝ) := ENNReal.ofReal (g x)
  have hf : Measurable f := ENNReal.measurable_ofReal.comp hg_meas
  change (∫⁻ x, f x ∂(mu ∗ nu)) ≤ _
  rw [Measure.conv, lintegral_map hf (by fun_prop)]
  calc
    _ ≤ ∫⁻ z : ℝ × ℝ, ENNReal.ofReal c * f z.1 * f z.2 ∂(mu.prod nu) := by
      apply lintegral_mono
      intro z
      have hh := ENNReal.ofReal_le_ofReal (hsub z.1 z.2)
      rw [ENNReal.ofReal_mul (mul_nonneg hc.le (hg.1 _)), ENNReal.ofReal_mul hc.le] at hh
      exact hh
    _ = _ := by
      rw [lintegral_prod _ (by fun_prop)]
      simp_rw [lintegral_const_mul _ hf]
      rw [lintegral_mul_const _ (hf.const_mul _), lintegral_const_mul _ hf]
