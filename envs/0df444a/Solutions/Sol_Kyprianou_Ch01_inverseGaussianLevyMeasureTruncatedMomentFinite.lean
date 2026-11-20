-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianLevyMeasureTruncatedMomentFinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:05:49.33793+00:00
-- url     : https://prove2.me/submissions/39c1db50-4068-4078-a758-b5512c4ada3b

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianTruncatedMomentRealIntegrable
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (b : ℝ) (hb : 0 < b) :
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-(b ^ 2 * x / 2))))
    (∫⁻ x : ℝ, ENNReal.ofReal (min 1 (x ^ 2)) ∂Pi) < ⊤ := by
  have hreal := Kyprianou.Ch01.inverseGaussianTruncatedMomentRealIntegrable b hb
  have hden : Measurable (fun x : ℝ =>
      ENNReal.ofReal ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
        Real.exp (-(b ^ 2 * x / 2)))) := by fun_prop
  change (∫⁻ x : ℝ, ENNReal.ofReal (min 1 (x ^ 2)) ∂
      ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
            Real.exp (-(b ^ 2 * x / 2)))))) < ⊤
  rw [lintegral_withDensity_eq_lintegral_mul _ hden
    (by fun_prop : Measurable (fun x : ℝ =>
      ENNReal.ofReal (min 1 (x ^ 2))))]
  have hpoint (x : ℝ) :
      ENNReal.ofReal
        ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
          Real.exp (-(b ^ 2 * x / 2))) *
          ENNReal.ofReal (min 1 (x ^ 2)) =
        ENNReal.ofReal
          ((min 1 (x ^ 2)) *
            ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-(b ^ 2 * x / 2)))) := by
    have hxden : 0 ≤ (1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
        Real.exp (-(b ^ 2 * x / 2)) :=
      mul_nonneg (div_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (Real.exp_pos _).le
    rw [← ENNReal.ofReal_mul hxden]
    congr 1
    ring
  change (∫⁻ x : ℝ,
    ENNReal.ofReal
      ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
        Real.exp (-(b ^ 2 * x / 2))) *
      ENNReal.ofReal (min 1 (x ^ 2))
        ∂(volume.restrict (Set.Ioi (0 : ℝ)))) < ⊤
  simp_rw [hpoint]
  have hm : AEStronglyMeasurable
      (fun x : ℝ =>
        (min 1 (x ^ 2)) *
          ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
            Real.exp (-(b ^ 2 * x / 2))))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by fun_prop
  have hn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun x : ℝ =>
        (min 1 (x ^ 2)) *
          ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
            Real.exp (-(b ^ 2 * x / 2)))) := by
    filter_upwards [] with x
    positivity
  exact (lintegral_ofReal_ne_top_iff_integrable hm hn).2 hreal |>.lt_top
