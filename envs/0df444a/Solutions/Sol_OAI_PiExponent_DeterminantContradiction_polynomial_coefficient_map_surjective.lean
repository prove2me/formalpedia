-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.polynomial_coefficient_map_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:26:39.034602+00:00
-- url     : https://prove2.me/submissions/d621d3a5-4187-4528-9ebe-d27a7949968d

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_interpolant_support
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_interpolant_coeff

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

noncomputable section

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real) :
    Function.Surjective
      (fun P : WeightedPolynomial d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d)) H =>
        fun c : Column d H =>
          P.val.coeff (InterpolationMatrix.exponentVector c.1)) := by
  classical
  intro f
  refine ⟨⟨∑ c : Column d H,
    MvPolynomial.C (f c) * MvPolynomial.monomial
      (InterpolationMatrix.exponentVector c.1) 1, ?_⟩, ?_⟩
  · exact OAI.PiExponent.DeterminantContradiction.weighted_interpolant_support
      nu d H f
  · funext c
    exact OAI.PiExponent.DeterminantContradiction.weighted_interpolant_coeff
      nu d H f c