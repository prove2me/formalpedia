-- Prove2me | solution 1 for Kyprianou.Ch01.expAscendingRenewalPositiveSeries
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T08:35:52.584838+00:00
-- url     : https://prove2.me/submissions/00048c80-242a-43e6-98c3-99d04eaf39c0

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_QueueingFundamentals_MG1_transforms
import Definitions.Def_levy_foundations_arrivalGammaDensity
import Theorems.Thm_Kyprianou_Ch01_gammaArrivalConvolutionPowerViaKernel
import Theorems.Thm_Kyprianou_Ch01_gammaArrivalDensityRenewalMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    (beta : ℝ) (hbeta : 0 < beta) :
    let mu : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun y : ℝ => ENNReal.ofReal (beta * Real.exp (-beta * y)))
    ∀ x : ℝ, 0 ≤ x →
      Summable (fun n : ℕ => ((QueueingFundamentals.MG1.convPow mu (n + 1))
        (Set.Icc (0 : ℝ) x)).toReal) ∧
      (∑' n : ℕ, ((QueueingFundamentals.MG1.convPow mu (n + 1))
        (Set.Icc (0 : ℝ) x)).toReal) = beta * x := by
  intro mu x hx
  have hd (n : ℕ) :
      ((QueueingFundamentals.MG1.convPow mu (n + 1))
        (Set.Icc (0 : ℝ) x)).toReal =
      ((volume.withDensity (LevyFoundations.arrivalGammaDensity beta n))
        (Set.Icc (0 : ℝ) x)).toReal := by
    rw [Kyprianou.Ch01.gammaArrivalConvolutionPowerViaKernel beta hbeta n]
  have h := Kyprianou.Ch01.gammaArrivalDensityRenewalMass beta hbeta x hx
  simpa only [hd] using h
