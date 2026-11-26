-- Prove2me | solution 1 for GlobalTheory.gaussAddVal_rename
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T12:50:15.101724+00:00
-- url     : https://prove2.me/submissions/f23128a6-bd22-43d5-a938-987fa5089deb

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
variable {R Γ σ τ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
  (v : AddValuation R Γ)

theorem solution {e : σ → τ} (he : Function.Injective e) (f : MvPolynomial σ R) :
    gaussAddVal v (rename e f) = gaussAddVal v f := by
  rw [gaussAddVal, gaussAddVal, AddValuation.ofValuation_apply, AddValuation.ofValuation_apply,
    gaussVal_rename (AddValuation.toValuation v) he]
