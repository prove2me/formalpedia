-- Prove2me | solution 1 for Helfgott.moebius_reciprocal_sqrt_two_finite
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T05:53:12.914695+00:00
-- url     : https://prove2.me/submissions/18df9ea3-cd8c-4266-8afc-bf3ed92b94fb

import Theorems.Thm_Helfgott_mobiusTable1200001_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrt1200001_checked
import Theorems.Thm_Helfgott_moebius_reciprocal_square_of_finite_certificate
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Helfgott
open scoped BigOperators

theorem solution : ∀ x : ℝ, (1 : ℝ) ≤ x → x < (1200001 : ℝ) →
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ))^2*x ≤ 2 :=
  moebius_reciprocal_square_of_finite_certificate 1200001 1000000000000 16 16
    mobiusTable1200001 mobiusReciprocal1200001 (by decide) (by decide)
    (by decide) (by decide) mobiusTable1200001_checked (by decide +kernel)
    mobiusReciprocalSqrt1200001_checked
#print axioms solution
