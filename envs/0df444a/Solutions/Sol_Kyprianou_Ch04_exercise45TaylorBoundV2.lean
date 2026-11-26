-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45TaylorBoundV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:15:43.674827+00:00
-- url     : https://prove2.me/submissions/bc1d122a-e2f5-4c41-b86b-469b8fdb0a7c

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Theorems.Thm_Kyprianou_Ch04_spatialQuadraticJumpRemainderV1
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false
theorem solution
    (f g h : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hf : ContDiff ℝ 2 f)
    (hg : ∀ x, g x = deriv f x) (hh : ∀ x, h x = deriv g x)
    (hF : ∀ x, |f x| ≤ K) (hG : ∀ x, |g x| ≤ K) (hH : ∀ x, |h x| ≤ K)
    (x z : ℝ) :
    |f (x+z)-f x-z * g x| ≤ (2 * K+K * |z|) ∧
    |f (x+z)-f x-z * g x| ≤ K * z^2 := by
  constructor
  · calc
      |f (x+z)-f x-z * g x| ≤ |f (x+z)-f x| + |z * g x| := abs_sub _ _
      _ ≤ |f (x+z)| + |f x| + |z| * |g x| := by rw [abs_mul]; linarith [abs_sub (f (x+z)) (f x)]
      _ ≤ 2 * K + K * |z| := by nlinarith [hF (x+z),hF x,
        mul_le_mul_of_nonneg_left (hG x) (abs_nonneg z)]
  · have he : g = deriv f := funext hg
    rw [he]
    exact Kyprianou.Ch04.spatialQuadraticJumpRemainderV1 f K x z hf hK
      (fun u => by rw [← he,← hh]; exact hH u)
