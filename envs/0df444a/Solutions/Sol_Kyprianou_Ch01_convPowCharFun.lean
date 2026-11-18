-- Prove2me | solution 1 for Kyprianou.Ch01.convPowCharFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:51:48.871209+00:00
-- url     : https://prove2.me/submissions/5eb5b22f-cf1e-41fd-a442-62ccf9ab91cf

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_transforms
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex QueueingFundamentals.MG1
set_option autoImplicit false

/-! A convolution power has the corresponding power of its characteristic function. -/
theorem solution
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) (xi : ℝ) :
    charFun (QueueingFundamentals.MG1.convPow μ n) xi =
      (charFun μ xi) ^ n := by
  have hprob : ∀ m : ℕ,
      IsProbabilityMeasure (QueueingFundamentals.MG1.convPow μ m) := by
    intro m
    induction m with
    | zero =>
        dsimp [QueueingFundamentals.MG1.convPow]
        exact Measure.dirac.isProbabilityMeasure
    | succ m hm =>
        letI := hm
        dsimp [QueueingFundamentals.MG1.convPow]
        exact Measure.probabilitymeasure_of_probabilitymeasures_conv _ _
  induction n with
  | zero =>
      simp [QueueingFundamentals.MG1.convPow, charFun_dirac]
  | succ n hn =>
      letI := hprob n
      calc
        charFun (QueueingFundamentals.MG1.convPow μ (n + 1)) xi =
            charFun (QueueingFundamentals.MG1.convPow μ n) xi *
              charFun μ xi := by
            rw [QueueingFundamentals.MG1.convPow, charFun_conv xi]
        _ = (charFun μ xi) ^ (n + 1) := by
          rw [hn, pow_succ]
