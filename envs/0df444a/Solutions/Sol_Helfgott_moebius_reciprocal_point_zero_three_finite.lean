-- Prove2me | solution 1 for Helfgott.moebius_reciprocal_point_zero_three_finite
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:29:41.491644+00:00
-- url     : https://prove2.me/submissions/3c2e73c1-ecd6-4d5a-b4b3-8cd46d231eff

import Theorems.Thm_Helfgott_mobiusTable1200001_checked
import Theorems.Thm_Helfgott_mobiusReciprocal1200001_checked
import Theorems.Thm_Helfgott_moebius_reciprocal_decay_of_finite_certificate
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Helfgott
open scoped BigOperators

theorem solution : ∀ x : ℝ, (11815 : ℝ) ≤ x → x < (1200001 : ℝ) →
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ)| ≤
      (3 / 100 : ℝ) / Real.log x :=
  moebius_reciprocal_decay_of_finite_certificate 11815 1200001 1000000000000 16 16
    mobiusTable1200001 mobiusReciprocal1200001 (by decide) (by decide) (by decide)
    (by decide) (by decide) mobiusTable1200001_checked (by decide +kernel)
    mobiusReciprocal1200001_checked
#print axioms solution
