-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.binomial_truncated_log_coefficient_exp_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-08T06:29:03.458181+00:00
-- url     : https://prove2.me/submissions/d35e8ec0-b3ec-4ed7-8760-2f389cee22c0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_no_fixed_data
import Definitions.Def_OAI_PiExponent_AnalyticRemainder

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {nu : Real} (d : FixedData nu) (hnu : 0 <= nu)
    {H : Real} (hH : 0 < H) (j s h : Nat) (b a : Fin d.m → Nat)
    (hj : j < d.K)
    (hrow : (d.v0 : Real) * s +
      (∑ i, MatrixArithmetic.logWeights (finiteDenominators d) i * b i) /
        (d.base.theta : Real) < H)
    (hcol : (d.w0 : Real) * h +
      ∑ i, MatrixArithmetic.logWeights (finiteDenominators d) i * a i ≤ H) :
    ‖(∏ i, ((a i).choose (b i) : Complex)) *
      (((1 + Polynomial.X) ^ h * ∏ i,
        (Polynomial.C ((j : Complex) *
          MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i) +
          InterpolationMatrix.truncatedLog
            (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)) ^
              (a i - b i)).coeff s)‖ ≤
      Real.exp (H * (d.analyticError -
        nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H))) *
      Real.exp (Real.log 2 / 4 - Real.log (1 - Real.exp (-Real.log 2 / 2))) *
      translationEnvelope d.m d.v0 H := by
  exact False.elim ((OAI.PiExponent.DeterminantContradiction.no_fixed_data nu).false d)
