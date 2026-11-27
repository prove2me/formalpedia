-- Prove2me | solution 2 for GlobalTheory.gaussAbs_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:39:53.863791+00:00
-- url     : https://prove2.me/submissions/a0557f63-ce9f-40a0-a000-6cfd193c5dc6

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
namespace GlobalTheory
theorem _root_.solution {e : σ → τ} (he : Function.Injective e) (f : MvPolynomial σ R) :
    gaussAbs a ha (rename e f) = gaussAbs a ha f := by
  rw [gaussAbs_apply, gaussVal_rename _ he, gaussAbs_apply]
end GlobalTheory
