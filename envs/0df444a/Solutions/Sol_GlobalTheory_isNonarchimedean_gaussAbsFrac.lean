-- Prove2me | solution 1 for GlobalTheory.isNonarchimedean_gaussAbsFrac
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T12:42:49.957817+00:00
-- url     : https://prove2.me/submissions/c8c6b482-6ffe-42d4-895d-f51f3a5b1c71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
open MvPolynomial
variable {R σ τ : Type*} [CommRing R]
variable [Nontrivial R] (a : AbsoluteValue R ℝ) (ha : IsNonarchimedean a)
variable {K : Type*} [Field K] (a : AbsoluteValue K ℝ) (ha : IsNonarchimedean a)
variable {F : Type*} [Field F] [Algebra (MvPolynomial σ K) F]
  [IsFractionRing (MvPolynomial σ K) F]

theorem solution : IsNonarchimedean (gaussAbsFrac a ha σ F) :=
  isNonarchimedean_valuationAbs _ _
