-- Prove2me | solution 1 for Kyprianou.Ch01.gammaArrivalConvolutionPowerViaKernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T08:42:02.335332+00:00
-- url     : https://prove2.me/submissions/31139966-0c0c-4ff4-a7e3-89dbb1e20efa

import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.WithDensity
import Definitions.Def_QueueingFundamentals_MG1_transforms
import Definitions.Def_levy_foundations_arrivalGammaDensity
import Theorems.Thm_Kyprianou_Ch01_expSourceEqualsArrivalDensity
import Theorems.Thm_Kyprianou_Ch01_gammaArrivalConvolutionOneStep
import Theorems.Thm_Kyprianou_Ch01_gammaArrivalDensityMeasurablePublic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Each source exponential convolution power is the next Erlang law. -/
theorem solution (beta : ℝ) (hbeta : 0 < beta) :
    let mu : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (beta * Real.exp (-beta * x)))
    ∀ n : ℕ, QueueingFundamentals.MG1.convPow mu (n + 1) =
      volume.withDensity (LevyFoundations.arrivalGammaDensity beta n) := by
  intro mu n
  have hmu : mu =
      volume.withDensity (LevyFoundations.arrivalGammaDensity beta 0) := by
    exact Kyprianou.Ch01.expSourceEqualsArrivalDensity beta hbeta
  induction n with
  | zero =>
      simpa [QueueingFundamentals.MG1.convPow] using hmu
  | succ n ih =>
      change QueueingFundamentals.MG1.convPow mu ((n + 1) + 1) = _
      rw [QueueingFundamentals.MG1.convPow, ih, hmu]
      rw [MeasureTheory.conv_withDensity_eq_lconvolution
        (Kyprianou.Ch01.gammaArrivalDensityMeasurablePublic beta n)
        (Kyprianou.Ch01.gammaArrivalDensityMeasurablePublic beta 0)]
      congr 1
      funext z
      simpa only [MeasureTheory.lconvolution_def, neg_add_eq_sub] using
        (Kyprianou.Ch01.gammaArrivalConvolutionOneStep beta hbeta n z)
