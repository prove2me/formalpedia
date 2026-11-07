-- Prove2me | solution 1 for OAI.OscSpecial.quadratic_phase_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:27:30.79492+00:00
-- url     : https://prove2.me/submissions/8a1c4261-e60f-4ae2-bfff-10dd050ba0d7

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open OAI.OscSpecial
namespace OAI.OscSpecial
theorem _root_.solution (a b k l : ℝ) :
    |(a - b) * k ^ 2 + 2 * a * k * l + b * l ^ 2| ≤
      phaseBoundConstant a b * (k ^ 2 + k * l + l ^ 2) := by
  let Q : ℝ := k ^ 2 + k * l + l ^ 2
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    nlinarith [sq_nonneg (k + l), sq_nonneg k, sq_nonneg l]
  have hsum : k ^ 2 + l ^ 2 ≤ 2 * Q := by
    dsimp [Q]
    nlinarith [sq_nonneg (k + l)]
  have hcross : 2 * |k| * |l| ≤ k ^ 2 + l ^ 2 := by
    nlinarith [sq_nonneg (|k| - |l|), sq_abs k, sq_abs l]
  have hk : k ^ 2 ≤ 2 * Q := by nlinarith [hsum, sq_nonneg l]
  have hl : l ^ 2 ≤ 2 * Q := by nlinarith [hsum, sq_nonneg k]
  have hkl : 2 * |k| * |l| ≤ 2 * Q := hcross.trans hsum
  have h1 := mul_le_mul_of_nonneg_left hk (abs_nonneg (a - b))
  have h2 := mul_le_mul_of_nonneg_left hkl (abs_nonneg a)
  have h3 := mul_le_mul_of_nonneg_left hl (abs_nonneg b)
  have htri :
      |(a - b) * k ^ 2 + 2 * a * k * l + b * l ^ 2| ≤
        |a - b| * k ^ 2 + 2 * |a| * |k| * |l| + |b| * l ^ 2 := by
    calc
      |(a - b) * k ^ 2 + 2 * a * k * l + b * l ^ 2| ≤
          |(a - b) * k ^ 2| + |2 * a * k * l| + |b * l ^ 2| := by
        calc
          _ ≤ |(a - b) * k ^ 2 + 2 * a * k * l| + |b * l ^ 2| := abs_add_le _ _
          _ ≤ _ := by
            have hh := abs_add_le ((a - b) * k ^ 2) (2 * a * k * l)
            linarith
      _ = _ := by
        simp [abs_mul,  abs_of_nonneg (sq_nonneg k),
          abs_of_nonneg (sq_nonneg l)]
  unfold phaseBoundConstant
  nlinarith [htri, h1, h2, h3, hQ]
end OAI.OscSpecial
