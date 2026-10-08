-- Prove2me | solution 1 for HlawkaCodex84SOSPolynomial.polynomial_row0
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T07:43:47.55747+00:00
-- url     : https://prove2.me/submissions/9bb52e00-c357-4af7-9ac6-8d1e8544113f

import Definitions.Def_HlawkaCodex84_SOSPolynomialData
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
open scoped BigOperators
open HlawkaCodex84SOSPolynomialData

theorem solution (e : Fin 9 → ℝ) (j : Fin 3) :
    certificateMatrix e 0 j = comparisonMatrix e 0 j := by
  generalize h0 : e 0 = x0
  generalize h1 : e 1 = x1
  generalize h2 : e 2 = x2
  generalize h3 : e 3 = x3
  generalize h4 : e 4 = x4
  generalize h5 : e 5 = x5
  generalize h6 : e 6 = x6
  generalize h7 : e 7 = x7
  generalize h8 : e 8 = x8
  have he : e = ![x0,x1,x2,x3,x4,x5,x6,x7,x8] := by
    ext k
    fin_cases k <;> simp_all
  rw [he]
  fin_cases j <;>
    norm_num [certificateMatrix, comparisonMatrix, boxMatrix, tensorLift, blockWeights,
      realGram, realMultiplier, realGraph,
      HlawkaCodex84SOSCache.gram,
      HlawkaCodex84SOSCache.multiplier0, HlawkaCodex84SOSCache.multiplier1,
      HlawkaCodex84SOSCache.multiplier2, HlawkaCodex84SOSCache.multiplier3,
      HlawkaCodex84SOSCache.multiplier4, HlawkaCodex84SOSCache.multiplier5,
      HlawkaCodex84SOSCache.multiplier6, HlawkaCodex84SOSCache.multiplier7,
      HlawkaCodex84SOSCache.multiplier8,
      HlawkaCodex84SOSPolynomialData.graph, HlawkaCodex84SOSPolynomialData.pairVector,
      HlawkaCodex84SOSPolynomialData.pairLeft, HlawkaCodex84SOSPolynomialData.pairRight,
      HlawkaCodex84SOSPolynomialData.rho,
      Matrix.mul_apply, Matrix.transpose, Matrix.map, Matrix.vecMulVec,
      Matrix.vecHead, Matrix.vecTail, Fin.ofNat,
      Fin.succ, Fin.mk.injEq, Fin.sum_univ_succ] <;>
    simp <;> ring

