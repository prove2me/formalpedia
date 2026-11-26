-- Prove2me | solution 1 for GlobalTheory.gaussAbs_rename
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T12:48:39.6288+00:00
-- url     : https://prove2.me/submissions/7466f5fd-d629-45c2-9579-646768321c6f

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

theorem solution {e : σ → τ} (he : Function.Injective e) (f : MvPolynomial σ R) :
    gaussAbs a ha (rename e f) = gaussAbs a ha f := by
  simp [gaussAbs_apply, gaussVal_rename _ he]
